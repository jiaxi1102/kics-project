from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
import time
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd
import scipy
from scipy import sparse
from scipy.io import mmread
from scipy.optimize import minimize
from scipy.special import digamma, gammaln
from scipy.stats import beta
import sklearn
from sklearn.linear_model import LogisticRegression

DATA_FILES = {
    "metadata": {
        "name": "stateFate_inVitro_metadata.txt.gz",
        "url": "https://kleintools.hms.harvard.edu/paper_websites/state_fate2020/stateFate_inVitro_metadata.txt.gz",
        "sha256": "c88e02cc512205e7033e28bf512f5d0dd43b98ba547fdd4a196b4bd9b62d7c07",
    },
    "clone_matrix": {
        "name": "stateFate_inVitro_clone_matrix.mtx.gz",
        "url": "https://kleintools.hms.harvard.edu/paper_websites/state_fate2020/stateFate_inVitro_clone_matrix.mtx.gz",
        "sha256": "26258702f8ccb7c98884d4f91bdcd1d6f552d7f2dd5125358efe7ade2fdcc50d",
    },
}
OUTCOMES = (
    "Baso", "Ccr7_DC", "Eos", "Erythroid", "Lymphoid", "Mast",
    "Meg", "Monocyte", "Neutrophil", "pDC", "Undifferentiated",
)


def strict_json_dump(payload: Any, path: Path) -> None:
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, allow_nan=False) + "\n",
        encoding="utf-8",
    )


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def download_verified(spec: dict[str, str], destination: Path, attempts: int = 5) -> dict[str, Any]:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() and sha256_file(destination) == spec["sha256"]:
        return {
            "path": destination.name,
            "sha256": spec["sha256"],
            "bytes": destination.stat().st_size,
            "source": spec["url"],
            "cached": True,
        }
    headers = {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 PR2-LARRY-validation/1.0",
        "Accept": "*/*",
    }
    last_error: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            request = urllib.request.Request(spec["url"], headers=headers)
            with urllib.request.urlopen(request, timeout=180) as response, destination.open("wb") as output:
                while True:
                    chunk = response.read(1024 * 1024)
                    if not chunk:
                        break
                    output.write(chunk)
            observed = sha256_file(destination)
            if observed != spec["sha256"]:
                raise RuntimeError(f"checksum mismatch for {destination.name}: {observed}")
            return {
                "path": destination.name,
                "sha256": observed,
                "bytes": destination.stat().st_size,
                "source": spec["url"],
                "cached": False,
            }
        except Exception as exc:
            last_error = exc
            destination.unlink(missing_ok=True)
            if attempt < attempts:
                time.sleep(2 ** attempt)
    raise RuntimeError(f"failed to download {spec['url']}: {last_error}")


def validate_membership(matrix: sparse.spmatrix, n_rows: int) -> sparse.csr_matrix:
    if not sparse.issparse(matrix):
        raise TypeError("clone matrix must be sparse")
    membership = matrix.tocsr()
    if membership.shape[0] != n_rows:
        raise ValueError("metadata and clone matrix rows do not align")
    if membership.data.size:
        if not np.all(np.isfinite(membership.data)) or not np.allclose(membership.data, 1.0):
            raise ValueError("clone matrix must be finite and binary")
    row_memberships = membership.getnnz(axis=1)
    if row_memberships.size and row_memberships.max() > 1:
        raise ValueError("each cell may belong to at most one clone")
    return membership


def grouped_splits(groups: np.ndarray, n_splits: int, seed: int) -> list[tuple[np.ndarray, np.ndarray]]:
    groups = np.asarray(groups)
    unique, counts = np.unique(groups, return_counts=True)
    if len(unique) < n_splits:
        raise ValueError("not enough groups for requested folds")
    rng = np.random.default_rng(seed)
    tie = rng.permutation(len(unique))
    order = sorted(range(len(unique)), key=lambda i: (-counts[i], int(tie[i])))
    fold_groups: list[list[Any]] = [[] for _ in range(n_splits)]
    fold_sizes = np.zeros(n_splits, dtype=int)
    fold_tie = rng.permutation(n_splits)
    rank = {int(fold): pos for pos, fold in enumerate(fold_tie)}
    for i in order:
        smallest = np.flatnonzero(fold_sizes == fold_sizes.min())
        fold = min(smallest.tolist(), key=lambda f: rank[int(f)])
        fold_groups[fold].append(unique[i])
        fold_sizes[fold] += counts[i]
    result = []
    seen = np.zeros(len(groups), dtype=int)
    for selected in fold_groups:
        test = np.isin(groups, selected)
        train = ~test
        if not train.any() or not test.any():
            raise RuntimeError("empty grouped fold")
        if set(groups[train].tolist()) & set(groups[test].tolist()):
            raise RuntimeError("group leakage")
        seen += test
        result.append((train, test))
    if not np.all(seen == 1):
        raise RuntimeError("grouped folds are not exhaustive")
    return result


def weighted_standardize(
    x_train: np.ndarray,
    x_test: np.ndarray,
    weights: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    mass = weights.sum()
    if mass <= 0:
        raise ValueError("training weights have no mass")
    mean = np.sum(x_train * weights[:, None], axis=0) / mass
    var = np.sum(((x_train - mean) ** 2) * weights[:, None], axis=0) / mass
    scale = np.sqrt(np.maximum(var, 1e-12))
    return (x_train - mean) / scale, (x_test - mean) / scale


def frequency_baseline(
    y: np.ndarray,
    labels: tuple[str, ...],
    weights: np.ndarray,
    n_eval: int,
    prior: float = 0.5,
) -> np.ndarray:
    counts = np.full(len(labels), prior, dtype=float)
    index = {label: i for i, label in enumerate(labels)}
    for value, weight in zip(y.tolist(), weights.tolist()):
        counts[index[str(value)]] += weight
    probability = counts / counts.sum()
    return np.repeat(probability[None, :], n_eval, axis=0)


def align_probabilities(
    raw: np.ndarray,
    classes: Sequence[str],
    labels: tuple[str, ...],
    baseline: np.ndarray,
    train_mass: float,
    prior: float,
) -> np.ndarray:
    aligned = np.zeros((raw.shape[0], len(labels)), dtype=float)
    index = {label: i for i, label in enumerate(labels)}
    for source, label in enumerate(classes):
        aligned[:, index[str(label)]] = raw[:, source]
    baseline_mass = len(labels) * prior
    state_weight = train_mass / (train_mass + baseline_mass)
    result = state_weight * aligned + (1.0 - state_weight) * baseline
    result /= result.sum(axis=1, keepdims=True)
    return result


def log_loss(y: np.ndarray, p: np.ndarray, labels: tuple[str, ...], weights: np.ndarray) -> float:
    idx = {label: i for i, label in enumerate(labels)}
    cols = np.asarray([idx[str(value)] for value in y])
    return float(
        np.average(
            -np.log(np.clip(p[np.arange(len(y)), cols], 1e-15, 1.0)),
            weights=weights,
        )
    )


def brier(y: np.ndarray, p: np.ndarray, labels: tuple[str, ...], weights: np.ndarray) -> float:
    idx = {label: i for i, label in enumerate(labels)}
    target = np.zeros_like(p)
    target[np.arange(len(y)), [idx[str(value)] for value in y]] = 1.0
    return float(np.average(np.sum((p - target) ** 2, axis=1), weights=weights))


def fit_model(
    x_train: np.ndarray,
    y_train: np.ndarray,
    w_train: np.ndarray,
    x_test: np.ndarray,
    labels: tuple[str, ...],
    baseline: np.ndarray,
    C: float,
    prior: float,
) -> np.ndarray:
    classes = np.unique(y_train)
    if len(classes) < 2:
        return baseline.copy()
    train_std, test_std = weighted_standardize(x_train, x_test, w_train)
    model = LogisticRegression(
        C=float(C), solver="lbfgs", max_iter=5000, tol=1e-7
    )
    model.fit(train_std, y_train, sample_weight=w_train)
    raw = model.predict_proba(test_std)
    return align_probabilities(
        raw,
        model.classes_,
        labels,
        baseline,
        float(w_train.sum()),
        prior,
    )


@dataclass
class CVOutput:
    probabilities: np.ndarray
    baseline: np.ndarray
    selected_c: list[float]
    repeat_log_loss: list[float]
    repeat_baseline_log_loss: list[float]
    repeat_brier: list[float]
    repeat_baseline_brier: list[float]


def nested_repeated_group_cv(
    x: np.ndarray,
    y: np.ndarray,
    groups: np.ndarray,
    labels: tuple[str, ...],
    weights: np.ndarray,
    *,
    Cs: tuple[float, ...] = (0.01, 0.1, 1.0, 10.0, 100.0),
    n_repeats: int = 5,
    outer_splits: int = 5,
    inner_splits: int = 4,
    seed: int = 1337,
    prior: float = 0.5,
) -> CVOutput:
    if any(np.sum(weights[groups == group]) <= 0 for group in np.unique(groups)):
        raise ValueError("every biological group must have positive sample-weight mass")
    repeat_predictions = []
    repeat_baselines = []
    selected_all: list[float] = []
    repeat_ll, repeat_bll, repeat_bs, repeat_bbs = [], [], [], []
    for repeat in range(n_repeats):
        outer = grouped_splits(
            groups,
            min(outer_splits, len(np.unique(groups))),
            seed + repeat * 101,
        )
        prediction = np.zeros((len(y), len(labels)), dtype=float)
        base_prediction = np.zeros_like(prediction)
        for outer_fold, (train, test) in enumerate(outer):
            baseline = frequency_baseline(
                y[train], labels, weights[train], int(test.sum()), prior
            )
            base_prediction[test] = baseline
            train_groups = groups[train]
            available_inner = min(inner_splits, len(np.unique(train_groups)))
            scores = []
            for C in Cs:
                inner_values = []
                inner_seed = seed + repeat * 1009 + outer_fold * 53
                for inner_train_rel, inner_val_rel in grouped_splits(
                    train_groups, available_inner, inner_seed
                ):
                    train_indices = np.flatnonzero(train)
                    inner_train = train_indices[inner_train_rel]
                    inner_val = train_indices[inner_val_rel]
                    inner_base = frequency_baseline(
                        y[inner_train],
                        labels,
                        weights[inner_train],
                        len(inner_val),
                        prior,
                    )
                    inner_p = fit_model(
                        x[inner_train],
                        y[inner_train],
                        weights[inner_train],
                        x[inner_val],
                        labels,
                        inner_base,
                        C,
                        prior,
                    )
                    inner_values.append(
                        log_loss(y[inner_val], inner_p, labels, weights[inner_val])
                    )
                scores.append(float(np.mean(inner_values)))
            best = float(Cs[int(np.argmin(scores))])
            selected_all.append(best)
            prediction[test] = fit_model(
                x[train],
                y[train],
                weights[train],
                x[test],
                labels,
                baseline,
                best,
                prior,
            )
        if not np.allclose(prediction.sum(axis=1), 1.0):
            raise RuntimeError("predictions do not sum to one")
        repeat_predictions.append(prediction)
        repeat_baselines.append(base_prediction)
        repeat_ll.append(log_loss(y, prediction, labels, weights))
        repeat_bll.append(log_loss(y, base_prediction, labels, weights))
        repeat_bs.append(brier(y, prediction, labels, weights))
        repeat_bbs.append(brier(y, base_prediction, labels, weights))
    return CVOutput(
        probabilities=np.mean(repeat_predictions, axis=0),
        baseline=np.mean(repeat_baselines, axis=0),
        selected_c=selected_all,
        repeat_log_loss=repeat_ll,
        repeat_baseline_log_loss=repeat_bll,
        repeat_brier=repeat_bs,
        repeat_baseline_brier=repeat_bbs,
    )


def cluster_bootstrap_improvement(
    y: np.ndarray,
    model_p: np.ndarray,
    baseline_p: np.ndarray,
    labels: tuple[str, ...],
    groups: np.ndarray,
    weights: np.ndarray,
    metric: str,
    n_boot: int = 2000,
    seed: int = 2026,
) -> dict[str, float]:
    idx = {label: i for i, label in enumerate(labels)}
    columns = np.asarray([idx[str(value)] for value in y])
    if metric == "log_loss":
        model_loss = -np.log(
            np.clip(model_p[np.arange(len(y)), columns], 1e-15, 1.0)
        )
        baseline_loss = -np.log(
            np.clip(baseline_p[np.arange(len(y)), columns], 1e-15, 1.0)
        )
    elif metric == "brier":
        target = np.zeros_like(model_p)
        target[np.arange(len(y)), columns] = 1.0
        model_loss = np.sum((model_p - target) ** 2, axis=1)
        baseline_loss = np.sum((baseline_p - target) ** 2, axis=1)
    else:
        raise ValueError(metric)
    unique = np.unique(groups)
    group_rows = {group: np.flatnonzero(groups == group) for group in unique}
    rng = np.random.default_rng(seed)
    draws = np.empty(n_boot)
    for b in range(n_boot):
        sampled = rng.choice(unique, size=len(unique), replace=True)
        numerator = 0.0
        denominator = 0.0
        for group in sampled:
            rows = group_rows[group]
            numerator += float(
                np.sum(weights[rows] * (baseline_loss[rows] - model_loss[rows]))
            )
            denominator += float(np.sum(weights[rows]))
        draws[b] = numerator / denominator
    observed = float(np.average(baseline_loss - model_loss, weights=weights))
    return {
        "estimate": observed,
        "ci_low": float(np.quantile(draws, 0.025)),
        "ci_high": float(np.quantile(draws, 0.975)),
        "probability_improvement_positive": float(np.mean(draws > 0)),
        "n_bootstrap": int(n_boot),
    }


def top_label_reliability(
    y: np.ndarray,
    p: np.ndarray,
    labels: tuple[str, ...],
    weights: np.ndarray,
    n_bins: int = 10,
) -> pd.DataFrame:
    label_index = {label: i for i, label in enumerate(labels)}
    truth = np.asarray([label_index[str(value)] for value in y])
    predicted = np.argmax(p, axis=1)
    confidence = np.max(p, axis=1)
    edges = np.linspace(0, 1, n_bins + 1)
    bins = np.minimum(
        np.digitize(confidence, edges[1:-1], right=False), n_bins - 1
    )
    rows = []
    for bin_index in range(n_bins):
        mask = bins == bin_index
        if not mask.any() or weights[mask].sum() <= 0:
            continue
        rows.append(
            {
                "bin": bin_index,
                "lower": float(edges[bin_index]),
                "upper": float(edges[bin_index + 1]),
                "n": int(mask.sum()),
                "weight": float(weights[mask].sum()),
                "mean_confidence": float(
                    np.average(confidence[mask], weights=weights[mask])
                ),
                "accuracy": float(
                    np.average(
                        (predicted[mask] == truth[mask]).astype(float),
                        weights=weights[mask],
                    )
                ),
            }
        )
    return pd.DataFrame(rows)


def fit_empirical_bayes_dirichlet(counts: np.ndarray) -> np.ndarray:
    counts = np.asarray(counts, dtype=float)
    if counts.ndim != 2 or counts.shape[1] < 2 or np.any(counts < 0):
        raise ValueError("invalid count matrix")
    if not np.allclose(counts, np.rint(counts)):
        raise ValueError("counts must be integers")
    totals = counts.sum(axis=0) + 0.5
    mean = totals / totals.sum()

    def objective(log_alpha: np.ndarray) -> float:
        alpha = np.exp(log_alpha)
        total_alpha = alpha.sum()
        n = counts.sum(axis=1)
        value = np.sum(gammaln(total_alpha) - gammaln(total_alpha + n))
        value += np.sum(
            gammaln(counts + alpha[None, :]) - gammaln(alpha[None, :])
        )
        return -float(value)

    candidates = []
    bounds = [(math.log(1e-5), math.log(1e5))] * counts.shape[1]
    for concentration in (0.5, 1.0, 5.0, 20.0, 100.0):
        start = np.log(np.clip(mean * concentration, 1e-4, None))
        candidates.append(
            minimize(
                objective,
                start,
                method="L-BFGS-B",
                bounds=bounds,
                options={"maxiter": 5000, "ftol": 1e-12},
            )
        )
    best = min(candidates, key=lambda result: result.fun)
    if not np.isfinite(best.fun):
        raise RuntimeError(
            f"empirical-Bayes Dirichlet optimization failed: {best.message}"
        )
    return np.exp(best.x)


def hierarchical_posterior(
    counts: np.ndarray,
    labels: tuple[str, ...],
) -> tuple[dict[str, Any], pd.DataFrame, pd.DataFrame]:
    alpha = fit_empirical_bayes_dirichlet(counts)
    concentration = counts + alpha[None, :]
    total = concentration.sum(axis=1, keepdims=True)
    mean = concentration / total
    variance = concentration * (total - concentration) / (
        total ** 2 * (total + 1)
    )
    low = beta.ppf(0.025, concentration, total - concentration)
    high = beta.ppf(0.975, concentration, total - concentration)
    predictive_entropy = -np.sum(
        np.where(mean > 0, mean * np.log(mean), 0), axis=1
    )
    expected_entropy = digamma(total[:, 0] + 1) - np.sum(
        mean * digamma(concentration + 1), axis=1
    )
    epistemic = np.maximum(predictive_entropy - expected_entropy, 0)
    unit = pd.DataFrame(
        {
            "n_observations": counts.sum(axis=1).astype(int),
            "predictive_entropy_nats": predictive_entropy,
            "expected_latent_entropy_nats": expected_entropy,
            "epistemic_mutual_information_nats": epistemic,
        }
    )
    probability = pd.DataFrame(
        {
            "unit_row": np.repeat(np.arange(len(counts)), len(labels)),
            "outcome": np.tile(labels, len(counts)),
            "count": counts.astype(int).reshape(-1),
            "posterior_mean": mean.reshape(-1),
            "posterior_variance": variance.reshape(-1),
            "credible_low": low.reshape(-1),
            "credible_high": high.reshape(-1),
        }
    )
    summary = {
        "method": "empirical-Bayes Dirichlet-multinomial hierarchy",
        "alpha": {
            label: float(value) for label, value in zip(labels, alpha)
        },
        "prior_concentration": float(alpha.sum()),
        "prior_mean": {
            label: float(value)
            for label, value in zip(labels, alpha / alpha.sum())
        },
        "median_predictive_entropy_nats": float(
            np.median(predictive_entropy)
        ),
        "median_expected_latent_entropy_nats": float(
            np.median(expected_entropy)
        ),
        "median_epistemic_mutual_information_nats": float(
            np.median(epistemic)
        ),
    }
    return summary, unit, probability


def prepare_horizon(
    metadata: pd.DataFrame,
    membership: sparse.csr_matrix,
    horizon: int,
) -> tuple[dict[str, Any], pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    timepoint = metadata["Time point"]
    early = timepoint.eq(2).to_numpy()
    target = timepoint.eq(horizon).to_numpy()
    row_memberships = membership.getnnz(axis=1)
    early_counts_all = np.asarray(membership[early].sum(axis=0)).ravel().astype(int)
    clone_ids = np.flatnonzero(early_counts_all > 0)
    all_counts = np.zeros((membership.shape[1], len(OUTCOMES)), dtype=int)
    outcome_values = metadata["Cell type annotation"].astype(str).replace(
        {"undiff": "Undifferentiated"}
    ).to_numpy()
    unknown = sorted(set(outcome_values[target]) - set(OUTCOMES))
    if unknown:
        raise ValueError(f"undeclared outcomes at day {horizon}: {unknown}")
    for index, label in enumerate(OUTCOMES):
        rows = target & (outcome_values == label)
        all_counts[:, index] = np.asarray(
            membership[rows].sum(axis=0)
        ).ravel().astype(int)
    counts = all_counts[clone_ids]

    early_rows = np.flatnonzero(early & (row_memberships == 1))
    early_clone_ids = membership[early_rows].indices
    state = (
        pd.DataFrame(
            {
                "clone_id": early_clone_ids,
                "SPRING_x": pd.to_numeric(
                    metadata.iloc[early_rows]["SPRING-x"], errors="coerce"
                ).to_numpy(float),
                "SPRING_y": pd.to_numeric(
                    metadata.iloc[early_rows]["SPRING-y"], errors="coerce"
                ).to_numpy(float),
            }
        )
        .groupby("clone_id", as_index=False)
        .agg(
            mean_day2_SPRING_x=("SPRING_x", "mean"),
            mean_day2_SPRING_y=("SPRING_y", "mean"),
            n_day2_cloned_cells=("clone_id", "size"),
        )
    )
    audit = pd.DataFrame(
        {
            "clone_id": clone_ids,
            "n_early": early_counts_all[clone_ids],
            "n_horizon_observed": counts.sum(axis=1),
            "has_horizon_observation": counts.sum(axis=1) > 0,
        }
    ).merge(state, on="clone_id", how="left", validate="one_to_one")

    target_rows = np.flatnonzero(target & (row_memberships == 1))
    target_clone_ids = membership[target_rows].indices
    keep = np.isin(target_clone_ids, clone_ids)
    target_rows, target_clone_ids = target_rows[keep], target_clone_ids[keep]
    descendants = pd.DataFrame(
        {
            "metadata_row": target_rows,
            "clone_id": target_clone_ids,
            "outcome": outcome_values[target_rows],
            "Well": metadata.iloc[target_rows]["Well"].astype(str).to_numpy(),
        }
    ).merge(state, on="clone_id", how="left", validate="many_to_one")
    feature_columns = [
        "mean_day2_SPRING_x",
        "mean_day2_SPRING_y",
        "n_day2_cloned_cells",
    ]
    if descendants[feature_columns].isna().any().any():
        raise RuntimeError("missing day-2 state for linked descendants")

    observed_counts = (
        descendants.groupby(["clone_id", "outcome"]).size().unstack(fill_value=0)
        .reindex(index=clone_ids, columns=OUTCOMES, fill_value=0)
        .to_numpy(int)
    )
    if not np.array_equal(observed_counts, counts):
        raise RuntimeError("descendant rows do not reproduce count matrix")

    n_target_total = int(target.sum())
    n_target_cloned = int(np.sum(row_memberships[target] == 1))
    n_linked = int(counts.sum())
    n_horizon_only = int(all_counts[early_counts_all == 0].sum())
    summary = {
        "horizon_day": horizon,
        "n_cells_total_dataset": int(len(metadata)),
        "n_total_clones": int(membership.shape[1]),
        "n_clones_with_day2_state": int(len(clone_ids)),
        "n_day2_clones_with_horizon_observation": int(
            np.sum(counts.sum(axis=1) > 0)
        ),
        "n_day2_clones_without_horizon_observation": int(
            np.sum(counts.sum(axis=1) == 0)
        ),
        "fraction_day2_clones_with_horizon_observation": float(
            np.mean(counts.sum(axis=1) > 0)
        ),
        "n_horizon_cells_total": n_target_total,
        "n_horizon_cells_cloned": n_target_cloned,
        "n_horizon_cells_linked_to_day2_clone": n_linked,
        "n_horizon_cells_from_horizon_only_clone": n_horizon_only,
        "n_horizon_cells_uncloned": n_target_total - n_target_cloned,
    }
    counts_frame = pd.DataFrame(counts, columns=OUTCOMES)
    counts_frame.insert(0, "clone_id", clone_ids)
    return summary, audit, counts_frame, descendants


def run_models(
    descendants: pd.DataFrame,
    horizon: int,
    output: Path,
) -> dict[str, Any]:
    y = descendants["outcome"].to_numpy()
    groups = descendants["clone_id"].to_numpy()
    well = pd.get_dummies(
        descendants["Well"].astype(str), prefix="Well", dtype=float
    )
    state = descendants[
        ["mean_day2_SPRING_x", "mean_day2_SPRING_y"]
    ].to_numpy(float)
    support = np.log1p(
        descendants[["n_day2_cloned_cells"]].to_numpy(float)
    )
    models = {
        "projected_state_only": state,
        "projected_state_plus_sampling": np.column_stack([state, support]),
        "projected_state_plus_context": np.column_stack(
            [state, support, well.to_numpy(float)]
        ),
    }
    clone_sizes = descendants["clone_id"].value_counts()
    weighting = {
        "descendant_weighted": np.ones(len(descendants), dtype=float),
        "clone_equal_weighted": descendants["clone_id"].map(
            lambda clone_id: 1.0 / clone_sizes.loc[clone_id]
        ).to_numpy(float),
    }
    result: dict[str, Any] = {}
    for weight_name, weights in weighting.items():
        for model_name, features in models.items():
            cv = nested_repeated_group_cv(
                features,
                y,
                groups,
                OUTCOMES,
                weights,
                seed=4100 + horizon * 100,
            )
            model_ll = log_loss(y, cv.probabilities, OUTCOMES, weights)
            baseline_ll = log_loss(y, cv.baseline, OUTCOMES, weights)
            model_brier = brier(y, cv.probabilities, OUTCOMES, weights)
            baseline_brier = brier(y, cv.baseline, OUTCOMES, weights)
            ll_ci = cluster_bootstrap_improvement(
                y,
                cv.probabilities,
                cv.baseline,
                OUTCOMES,
                groups,
                weights,
                "log_loss",
                seed=5100 + horizon,
            )
            br_ci = cluster_bootstrap_improvement(
                y,
                cv.probabilities,
                cv.baseline,
                OUTCOMES,
                groups,
                weights,
                "brier",
                seed=6100 + horizon,
            )
            reliability = top_label_reliability(
                y, cv.probabilities, OUTCOMES, weights
            )
            reliability.insert(0, "weighting", weight_name)
            reliability.insert(0, "model", model_name)
            reliability.insert(0, "horizon_day", horizon)
            reliability.to_csv(
                output
                / f"day{horizon}_{model_name}_{weight_name}_reliability.csv",
                index=False,
            )
            predictions = pd.DataFrame(
                {
                    "metadata_row": descendants["metadata_row"].to_numpy(),
                    "clone_id": groups,
                    "outcome": y,
                    "weight": weights,
                }
            )
            for index, label in enumerate(OUTCOMES):
                predictions[f"p_model_{label}"] = cv.probabilities[:, index]
                predictions[f"p_baseline_{label}"] = cv.baseline[:, index]
            predictions.to_csv(
                output
                / f"day{horizon}_{model_name}_{weight_name}_predictions.csv.gz",
                index=False,
                compression="gzip",
            )
            key = f"{model_name}__{weight_name}"
            result[key] = {
                "model": model_name,
                "weighting": weight_name,
                "n_descendants": int(len(y)),
                "n_clones": int(len(np.unique(groups))),
                "model_log_loss": model_ll,
                "baseline_log_loss": baseline_ll,
                "log_loss_improvement": ll_ci,
                "model_brier": model_brier,
                "baseline_brier": baseline_brier,
                "brier_improvement": br_ci,
                "repeat_model_log_loss": [
                    float(value) for value in cv.repeat_log_loss
                ],
                "repeat_baseline_log_loss": [
                    float(value) for value in cv.repeat_baseline_log_loss
                ],
                "repeat_model_brier": [
                    float(value) for value in cv.repeat_brier
                ],
                "repeat_baseline_brier": [
                    float(value) for value in cv.repeat_baseline_brier
                ],
                "selected_C_counts": {
                    str(C): int(sum(np.isclose(cv.selected_c, C)))
                    for C in sorted(set(cv.selected_c))
                },
                "nested_cv": {
                    "repeats": 5,
                    "outer_folds": 5,
                    "inner_folds": 4,
                    "C_grid": [0.01, 0.1, 1.0, 10.0, 100.0],
                },
            }
    return result


def make_figure(all_results: dict[str, Any], output: Path) -> None:
    fig, axes = plt.subplots(2, 2, figsize=(11, 8.5))
    horizons = [4, 6]
    observed = [
        all_results[str(h)]["audit"][
            "fraction_day2_clones_with_horizon_observation"
        ]
        for h in horizons
    ]
    axes[0, 0].bar([str(h) for h in horizons], observed)
    axes[0, 0].set_ylim(0, 1)
    axes[0, 0].set_xlabel("Exact horizon (day)")
    axes[0, 0].set_ylabel("Fraction of day-2 clones observed")
    axes[0, 0].set_title("A  Observation is horizon-dependent")

    model_order = [
        "projected_state_only",
        "projected_state_plus_sampling",
        "projected_state_plus_context",
    ]
    labels_display = [
        "state",
        "state + support",
        "state + support + context",
    ]
    positions = np.arange(len(model_order))
    for offset, horizon in [(-0.13, 4), (0.13, 6)]:
        estimates, lows, highs = [], [], []
        for model in model_order:
            item = all_results[str(horizon)]["models"][
                f"{model}__clone_equal_weighted"
            ]["log_loss_improvement"]
            estimates.append(item["estimate"])
            lows.append(item["ci_low"])
            highs.append(item["ci_high"])
        estimates = np.asarray(estimates)
        lows = np.asarray(lows)
        highs = np.asarray(highs)
        axes[0, 1].errorbar(
            positions + offset,
            estimates,
            yerr=[estimates - lows, highs - estimates],
            fmt="o",
            capsize=4,
            label=f"day {horizon}",
        )
    axes[0, 1].axhline(0, linewidth=1, linestyle="--")
    axes[0, 1].set_xticks(
        positions, labels_display, rotation=20, ha="right"
    )
    axes[0, 1].set_ylabel("Held-out log-loss improvement")
    axes[0, 1].set_title(
        "B  State information versus frequency baseline"
    )
    axes[0, 1].legend(frameon=False)

    for horizon in horizons:
        path = (
            output
            / f"day{horizon}_projected_state_only_clone_equal_weighted_reliability.csv"
        )
        frame = pd.read_csv(path)
        axes[1, 0].plot(
            frame["mean_confidence"],
            frame["accuracy"],
            marker="o",
            label=f"day {horizon}",
        )
    axes[1, 0].plot([0, 1], [0, 1], linestyle="--", linewidth=1)
    axes[1, 0].set_xlim(0, 1)
    axes[1, 0].set_ylim(0, 1)
    axes[1, 0].set_xlabel("Predicted top-label probability")
    axes[1, 0].set_ylabel("Observed accuracy")
    axes[1, 0].set_title("C  Clone-held-out reliability")
    axes[1, 0].legend(frameon=False)

    x = np.arange(3)
    width = 0.35
    for offset, horizon in [(-width / 2, 4), (width / 2, 6)]:
        hierarchical = all_results[str(horizon)]["hierarchical"]
        values = [
            hierarchical["median_predictive_entropy_nats"],
            hierarchical["median_expected_latent_entropy_nats"],
            hierarchical["median_epistemic_mutual_information_nats"],
        ]
        axes[1, 1].bar(x + offset, values, width, label=f"day {horizon}")
    axes[1, 1].set_xticks(
        x,
        ["predictive", "expected latent", "epistemic MI"],
        rotation=15,
        ha="right",
    )
    axes[1, 1].set_ylabel("Median entropy (nats)")
    axes[1, 1].set_title(
        "D  Finite counts separate uncertainty layers"
    )
    axes[1, 1].legend(frameon=False)

    fig.tight_layout()
    fig.savefig(
        output / "fig_pr2_exact_horizon_larry.png",
        dpi=220,
        bbox_inches="tight",
    )
    fig.savefig(
        output / "fig_pr2_exact_horizon_larry.pdf", bbox_inches="tight"
    )
    plt.close(fig)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("pr2_results"))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    raw = output / "_raw"
    raw.mkdir(exist_ok=True)

    provenance = {}
    for key, spec in DATA_FILES.items():
        provenance[key] = download_verified(spec, raw / spec["name"])

    metadata = pd.read_csv(
        raw / DATA_FILES["metadata"]["name"], sep="\t"
    )
    membership = validate_membership(
        mmread(raw / DATA_FILES["clone_matrix"]["name"]), len(metadata)
    )
    required = {
        "Time point",
        "Cell type annotation",
        "Well",
        "SPRING-x",
        "SPRING-y",
    }
    missing = required - set(metadata.columns)
    if missing:
        raise ValueError(f"metadata missing columns: {sorted(missing)}")

    final: dict[str, Any] = {
        "analysis": "PR2 exact-horizon LARRY calibration",
        "analysis_version": "pr2-final-v1",
        "generated_utc": pd.Timestamp.now(tz="UTC").isoformat(),
        "data": provenance,
        "software": {
            "python": sys.version,
            "platform": platform.platform(),
            "numpy": np.__version__,
            "pandas": pd.__version__,
            "scipy": scipy.__version__,
            "scikit_learn": sklearn.__version__,
        },
        "estimand": (
            "fate annotation of a randomly selected deposited descendant at "
            "an exact horizon, conditional on observation; clone "
            "observability audited separately"
        ),
        "outcomes": list(OUTCOMES),
        "horizons": {},
    }

    for horizon in (4, 6):
        audit_summary, audit, counts, descendants = prepare_horizon(
            metadata, membership, horizon
        )
        observed = counts[list(OUTCOMES)].sum(axis=1).to_numpy() > 0
        hierarchical_summary, unit, probability = hierarchical_posterior(
            counts.loc[observed, list(OUTCOMES)].to_numpy(), OUTCOMES
        )
        observed_ids = counts.loc[observed, "clone_id"].to_numpy()
        unit.insert(0, "clone_id", observed_ids)
        probability["clone_id"] = observed_ids[
            probability["unit_row"].to_numpy()
        ]
        probability.drop(columns=["unit_row"], inplace=True)
        models = run_models(descendants, horizon, output)

        audit.to_csv(
            output / f"day{horizon}_clone_observation_audit.csv", index=False
        )
        counts.to_csv(
            output / f"day{horizon}_clone_outcome_counts.csv", index=False
        )
        unit.to_csv(
            output / f"day{horizon}_hierarchical_uncertainty.csv", index=False
        )
        probability.to_csv(
            output / f"day{horizon}_hierarchical_probabilities.csv.gz",
            index=False,
            compression="gzip",
        )
        descendants.to_csv(
            output / f"day{horizon}_linked_descendant_rows.csv.gz",
            index=False,
            compression="gzip",
        )
        final["horizons"][str(horizon)] = {
            "audit": audit_summary,
            "hierarchical": hierarchical_summary,
            "models": models,
        }

    all_results = {
        horizon: final["horizons"][horizon]
        for horizon in final["horizons"]
    }
    make_figure(all_results, output)
    strict_json_dump(final, output / "pr2_exact_horizon_summary.json")
    for path in raw.iterdir():
        path.unlink()
    raw.rmdir()
    print(
        json.dumps(
            {
                "status": "complete",
                "output": str(output),
                "summary": final["horizons"],
            },
            indent=2,
            allow_nan=False,
        )
    )


if __name__ == "__main__":
    main()
