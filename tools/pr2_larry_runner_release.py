from __future__ import annotations

import argparse
import json
import platform
import sys
from pathlib import Path
from typing import Any

import matplotlib
matplotlib.use("Agg")
import numpy as np
import pandas as pd
import scipy
from scipy.io import mmread
import sklearn

import pr2_larry_runner as core


def fixed_c_split_sensitivity(
    features: np.ndarray,
    outcomes: np.ndarray,
    groups: np.ndarray,
    labels: tuple[str, ...],
    weights: np.ndarray,
    *,
    C: float,
    repeats: int,
    folds: int,
    seed: int,
    prior: float = 0.5,
) -> dict[str, Any]:
    model_log_loss: list[float] = []
    baseline_log_loss: list[float] = []
    model_brier: list[float] = []
    baseline_brier: list[float] = []
    for repeat in range(repeats):
        probability = np.zeros((len(outcomes), len(labels)), dtype=float)
        baseline_probability = np.zeros_like(probability)
        for train, test in core.grouped_splits(
            groups,
            min(folds, len(np.unique(groups))),
            seed + repeat * 173,
        ):
            baseline = core.frequency_baseline(
                outcomes[train], labels, weights[train], int(test.sum()), prior
            )
            baseline_probability[test] = baseline
            probability[test] = core.fit_model(
                features[train],
                outcomes[train],
                weights[train],
                features[test],
                labels,
                baseline,
                C,
                prior,
            )
        model_log_loss.append(
            core.log_loss(outcomes, probability, labels, weights)
        )
        baseline_log_loss.append(
            core.log_loss(outcomes, baseline_probability, labels, weights)
        )
        model_brier.append(core.brier(outcomes, probability, labels, weights))
        baseline_brier.append(
            core.brier(outcomes, baseline_probability, labels, weights)
        )
    return {
        "fixed_C": float(C),
        "repeats": int(repeats),
        "folds": int(folds),
        "model_log_loss": [float(value) for value in model_log_loss],
        "baseline_log_loss": [float(value) for value in baseline_log_loss],
        "log_loss_improvement": [
            float(base - model)
            for base, model in zip(baseline_log_loss, model_log_loss)
        ],
        "model_brier": [float(value) for value in model_brier],
        "baseline_brier": [float(value) for value in baseline_brier],
        "brier_improvement": [
            float(base - model)
            for base, model in zip(baseline_brier, model_brier)
        ],
    }


def run_models_release(
    descendants: pd.DataFrame,
    horizon: int,
    output: Path,
) -> dict[str, Any]:
    outcomes = descendants["outcome"].to_numpy()
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
    clone_weights = descendants["clone_id"].map(
        lambda clone_id: 1.0 / clone_sizes.loc[clone_id]
    ).to_numpy(float)
    descendant_weights = np.ones(len(descendants), dtype=float)
    evaluation_weights = {
        "clone_equal_weighted": clone_weights,
        "descendant_weighted": descendant_weights,
    }

    result: dict[str, Any] = {}
    for model_index, (model_name, features) in enumerate(models.items()):
        cv = core.nested_repeated_group_cv(
            features,
            outcomes,
            groups,
            core.OUTCOMES,
            clone_weights,
            n_repeats=1,
            outer_splits=5,
            inner_splits=3,
            seed=4100 + horizon * 100 + model_index * 17,
        )
        selected = np.asarray(cv.selected_c, dtype=float)
        fixed_C = float(np.exp(np.median(np.log(selected))))
        split_sensitivity = None
        if model_name == "projected_state_only":
            split_sensitivity = fixed_c_split_sensitivity(
                features,
                outcomes,
                groups,
                core.OUTCOMES,
                clone_weights,
                C=fixed_C,
                repeats=3,
                folds=5,
                seed=7100 + horizon,
            )
            primary = pd.DataFrame(
                {
                    "metadata_row": descendants["metadata_row"].to_numpy(),
                    "clone_id": groups,
                    "outcome": outcomes,
                    "clone_equal_weight": clone_weights,
                }
            )
            for index, label in enumerate(core.OUTCOMES):
                primary[f"p_model_{label}"] = cv.probabilities[:, index]
                primary[f"p_baseline_{label}"] = cv.baseline[:, index]
            primary.to_csv(
                output / f"day{horizon}_primary_predictions.csv.gz",
                index=False,
                compression="gzip",
            )

        for weighting, weights in evaluation_weights.items():
            model_ll = core.log_loss(
                outcomes, cv.probabilities, core.OUTCOMES, weights
            )
            baseline_ll = core.log_loss(
                outcomes, cv.baseline, core.OUTCOMES, weights
            )
            model_bs = core.brier(
                outcomes, cv.probabilities, core.OUTCOMES, weights
            )
            baseline_bs = core.brier(
                outcomes, cv.baseline, core.OUTCOMES, weights
            )
            ll_ci = core.cluster_bootstrap_improvement(
                outcomes,
                cv.probabilities,
                cv.baseline,
                core.OUTCOMES,
                groups,
                weights,
                "log_loss",
                n_boot=2000,
                seed=5100 + horizon + model_index,
            )
            bs_ci = core.cluster_bootstrap_improvement(
                outcomes,
                cv.probabilities,
                cv.baseline,
                core.OUTCOMES,
                groups,
                weights,
                "brier",
                n_boot=2000,
                seed=6100 + horizon + model_index,
            )
            reliability = core.top_label_reliability(
                outcomes, cv.probabilities, core.OUTCOMES, weights
            )
            reliability.insert(0, "training_weighting", "clone_equal_weighted")
            reliability.insert(0, "evaluation_weighting", weighting)
            reliability.insert(0, "model", model_name)
            reliability.insert(0, "horizon_day", horizon)
            reliability.to_csv(
                output / f"day{horizon}_{model_name}_{weighting}_reliability.csv",
                index=False,
            )
            key = f"{model_name}__{weighting}"
            result[key] = {
                "model": model_name,
                "training_weighting": "clone_equal_weighted",
                "evaluation_weighting": weighting,
                "n_descendants": int(len(outcomes)),
                "n_clones": int(len(np.unique(groups))),
                "model_log_loss": float(model_ll),
                "baseline_log_loss": float(baseline_ll),
                "log_loss_improvement": ll_ci,
                "model_brier": float(model_bs),
                "baseline_brier": float(baseline_bs),
                "brier_improvement": bs_ci,
                "selected_C_counts": {
                    str(C): int(np.count_nonzero(np.isclose(selected, C)))
                    for C in sorted(set(selected.tolist()))
                },
                "selected_C_geometric_median": fixed_C,
                "nested_cv": {
                    "repeats": 1,
                    "outer_folds": 5,
                    "inner_folds": 3,
                    "C_grid": [0.01, 0.1, 1.0, 10.0, 100.0],
                    "selection_weighting": "clone_equal_weighted",
                },
                "split_sensitivity": split_sensitivity,
            }
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path("pr2_results"))
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    raw = output / "_raw"
    raw.mkdir(exist_ok=True)

    provenance = {}
    for key, spec in core.DATA_FILES.items():
        provenance[key] = core.download_verified(spec, raw / spec["name"])
    metadata = pd.read_csv(
        raw / core.DATA_FILES["metadata"]["name"], sep="\t"
    )
    membership = core.validate_membership(
        mmread(raw / core.DATA_FILES["clone_matrix"]["name"]), len(metadata)
    )

    final: dict[str, Any] = {
        "analysis": "PR2 exact-horizon LARRY calibration",
        "analysis_version": "pr2-release-v2",
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
        "outcomes": list(core.OUTCOMES),
        "horizons": {},
    }

    for horizon in (4, 6):
        audit_summary, audit, counts, descendants = core.prepare_horizon(
            metadata, membership, horizon
        )
        observed = counts[list(core.OUTCOMES)].sum(axis=1).to_numpy() > 0
        hierarchical_summary, unit, probability = core.hierarchical_posterior(
            counts.loc[observed, list(core.OUTCOMES)].to_numpy(), core.OUTCOMES
        )
        observed_ids = counts.loc[observed, "clone_id"].to_numpy()
        unit.insert(0, "clone_id", observed_ids)
        probability["clone_id"] = observed_ids[
            probability["unit_row"].to_numpy()
        ]
        probability.drop(columns=["unit_row"], inplace=True)
        models = run_models_release(descendants, horizon, output)

        audit.to_csv(output / f"day{horizon}_clone_observation_audit.csv", index=False)
        counts.to_csv(output / f"day{horizon}_clone_outcome_counts.csv", index=False)
        unit.to_csv(output / f"day{horizon}_hierarchical_uncertainty.csv", index=False)
        probability.to_csv(
            output / f"day{horizon}_hierarchical_probabilities.csv.gz",
            index=False,
            compression="gzip",
        )
        final["horizons"][str(horizon)] = {
            "audit": audit_summary,
            "hierarchical": hierarchical_summary,
            "models": models,
        }

    core.make_figure(final["horizons"], output)
    core.strict_json_dump(final, output / "pr2_exact_horizon_summary.json")
    for path in raw.iterdir():
        path.unlink()
    raw.rmdir()
    print(json.dumps({"status": "complete", "horizons": final["horizons"]}, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
