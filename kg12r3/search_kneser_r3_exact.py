#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

N = 12
R = 3


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def canonical_data() -> tuple[list[tuple[int, ...]], list[tuple[int, int]], list[tuple[int, int, int]]]:
    vertices = list(itertools.combinations(range(N), R))
    vertex_id = {vertex: index for index, vertex in enumerate(vertices)}
    edges: list[tuple[int, int]] = []
    edge_id: dict[tuple[int, int], int] = {}
    for left, a in enumerate(vertices):
        a_set = set(a)
        for right in range(left + 1, len(vertices)):
            if a_set.isdisjoint(vertices[right]):
                edge_id[(left, right)] = len(edges)
                edges.append((left, right))
    triangles: list[tuple[int, int, int]] = []
    for first, a in enumerate(vertices):
        remaining_a = tuple(x for x in range(N) if x not in a)
        for b in itertools.combinations(remaining_a, R):
            second = vertex_id[b]
            if second <= first:
                continue
            used = set(a) | set(b)
            remaining_ab = tuple(x for x in range(N) if x not in used)
            for c in itertools.combinations(remaining_ab, R):
                third = vertex_id[c]
                if third <= second:
                    continue
                triangles.append((edge_id[(first, second)], edge_id[(first, third)], edge_id[(second, third)]))
    assert (len(vertices), len(edges), len(triangles), len(set(triangles))) == (220, 9240, 61600, 61600)
    return vertices, edges, triangles


def symmetry_units(vertices: list[tuple[int, ...]], edges: list[tuple[int, int]]) -> list[tuple[int, bool]]:
    vertex_id = {vertex: index for index, vertex in enumerate(vertices)}
    edge_id = {edge: index for index, edge in enumerate(edges)}
    a = vertex_id[(0, 1, 2)]
    b = vertex_id[(3, 4, 5)]
    c = vertex_id[(6, 7, 8)]
    def edge(left: int, right: int) -> int:
        return edge_id[tuple(sorted((left, right)))]
    return [(edge(a, b), True), (edge(a, c), False), (edge(b, c), False)]


def generate(outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    vertices, edges, triangles = canonical_data()
    units = symmetry_units(vertices, edges)
    clause_count = 2 * len(triangles) + len(units)
    cnf_path = outdir / "kg12_3_no_mono_triangle.cnf"
    with cnf_path.open("w", encoding="ascii", newline="\n") as handle:
        handle.write("c KG(12,3) red-blue edge coloring with no monochromatic triangle\n")
        handle.write(f"p cnf {len(edges)} {clause_count}\n")
        for x, y, z in triangles:
            handle.write(f"{x + 1} {y + 1} {z + 1} 0\n")
            handle.write(f"-{x + 1} -{y + 1} -{z + 1} 0\n")
        for variable, value in units:
            literal = variable + 1 if value else -(variable + 1)
            handle.write(f"{literal} 0\n")
    metadata = {
        "vertices": len(vertices), "edges_boolean_variables": len(edges),
        "kneser_triangles": len(triangles), "cnf_clauses": clause_count,
        "symmetry_units_zero_based": [{"edge_id": v, "red": b} for v, b in units],
        "vertex_order_sha256": sha256_bytes(stable_json(vertices)),
        "edge_order_sha256": sha256_bytes(stable_json(edges)),
        "triangle_order_sha256": sha256_bytes(stable_json(triangles)),
        "cnf_sha256": sha256_bytes(cnf_path.read_bytes()),
    }
    (outdir / "instance-metadata.json").write_bytes(stable_json(metadata))
    print(json.dumps(metadata, indent=2, sort_keys=True))


def parse_model(path: Path, variable_count: int) -> tuple[str, list[bool] | None]:
    status = None
    assignments: dict[int, bool] = {}
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.strip()
        if line.startswith("s "):
            if "UNSATISFIABLE" in line:
                status = "UNSAT"
            elif "SATISFIABLE" in line:
                status = "SAT"
        elif line.startswith("v "):
            for token in line[2:].split():
                literal = int(token)
                if literal:
                    assignments[abs(literal)] = literal > 0
    if status is None:
        raise ValueError("missing solver status")
    if status == "UNSAT":
        return status, None
    missing = set(range(1, variable_count + 1)) - assignments.keys()
    if missing:
        raise ValueError(f"incomplete model: {len(missing)} missing variables")
    return status, [assignments[i] for i in range(1, variable_count + 1)]


def verify(model_path: Path, outdir: Path) -> None:
    vertices, edges, triangles = canonical_data()
    units = symmetry_units(vertices, edges)
    status, colors = parse_model(model_path, len(edges))
    if status == "UNSAT":
        record = {"solver_status": "UNSAT", "mathematical_claim": "none without an independently checked proof trace"}
        (outdir / "solver-status.json").write_bytes(stable_json(record))
        print(json.dumps(record, indent=2))
        return
    assert colors is not None
    for variable, value in units:
        assert colors[variable] is value
    one_red = two_red = 0
    for x, y, z in triangles:
        count = int(colors[x]) + int(colors[y]) + int(colors[z])
        if count == 1:
            one_red += 1
        elif count == 2:
            two_red += 1
        else:
            raise AssertionError((x, y, z, count))
    bits = "".join("1" if value else "0" for value in colors)
    certificate = {
        "solver_status": "SAT", "independent_verification": "PASS",
        "edges": len(edges), "triangles_checked": len(triangles),
        "monochromatic_triangles": 0,
        "triangles_with_one_red_edge": one_red,
        "triangles_with_two_red_edges": two_red,
        "red_edges": sum(colors), "blue_edges": len(edges) - sum(colors),
        "edge_color_bitstring_sha256": sha256_bytes(bits.encode()),
        "red_edge_ids_zero_based": [i for i, value in enumerate(colors) if value],
    }
    (outdir / "sat-certificate.json").write_bytes(stable_json(certificate))
    (outdir / "edge-colors.bits").write_text(bits + "\n", encoding="ascii")
    short = dict(certificate)
    short.pop("red_edge_ids_zero_based")
    print(json.dumps(short, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    subs = parser.add_subparsers(dest="command", required=True)
    gp = subs.add_parser("generate")
    gp.add_argument("outdir", type=Path)
    vp = subs.add_parser("verify")
    vp.add_argument("model", type=Path)
    vp.add_argument("outdir", type=Path)
    args = parser.parse_args()
    if args.command == "generate":
        generate(args.outdir)
    else:
        verify(args.model, args.outdir)


if __name__ == "__main__":
    main()
