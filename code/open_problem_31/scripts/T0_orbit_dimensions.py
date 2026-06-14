#!/usr/bin/env python3
"""T0 - exact orbit-dimension certificate for det_3 and perm_3.

The computation uses integer polynomial arithmetic only.  Cubics are stored as
maps from exponent tuples to integer coefficients.  The Lie algebra tangent
space is spanned by the 81 cubics x_a * d(f)/d(x_b), written on the full
degree-3 monomial basis of Q[x_11,...,x_33].  Ranks are computed by a
fraction-free Bareiss elimination.
"""

from __future__ import annotations

import hashlib
import json
import random
from itertools import permutations
from pathlib import Path

random.seed(42)

N = 9
DEG = 3


def var_index(row: int, col: int) -> int:
    return 3 * row + col


def parity(perm: tuple[int, ...]) -> int:
    inversions = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                inversions += 1
    return -1 if inversions % 2 else 1


def monomial_for_perm(perm: tuple[int, ...]) -> tuple[int, ...]:
    exp = [0] * N
    for row, col in enumerate(perm):
        exp[var_index(row, col)] += 1
    return tuple(exp)


def det3() -> dict[tuple[int, ...], int]:
    out: dict[tuple[int, ...], int] = {}
    for perm in permutations(range(3)):
        out[monomial_for_perm(perm)] = parity(perm)
    return out


def perm3() -> dict[tuple[int, ...], int]:
    return {monomial_for_perm(perm): 1 for perm in permutations(range(3))}


def degree_monomials(nvars: int, degree: int) -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []

    def rec(pos: int, remaining: int, acc: list[int]) -> None:
        if pos == nvars - 1:
            out.append(tuple(acc + [remaining]))
            return
        for value in range(remaining, -1, -1):
            rec(pos + 1, remaining - value, acc + [value])

    rec(0, degree, [])
    return out


def act_xa_dxb(poly: dict[tuple[int, ...], int], a: int, b: int) -> dict[tuple[int, ...], int]:
    out: dict[tuple[int, ...], int] = {}
    for exp, coeff in poly.items():
        power = exp[b]
        if power == 0:
            continue
        new_exp = list(exp)
        new_exp[b] -= 1
        new_exp[a] += 1
        new_exp_t = tuple(new_exp)
        out[new_exp_t] = out.get(new_exp_t, 0) + coeff * power
    return {exp: coeff for exp, coeff in out.items() if coeff}


def tangent_matrix(poly: dict[tuple[int, ...], int], basis: list[tuple[int, ...]]) -> tuple[list[str], list[list[int]]]:
    col_index = {mon: i for i, mon in enumerate(basis)}
    labels: list[str] = []
    rows: list[list[int]] = []
    for a in range(N):
        for b in range(N):
            labels.append(f"x{a + 1}d{b + 1}")
            image = act_xa_dxb(poly, a, b)
            row = [0] * len(basis)
            for mon, coeff in image.items():
                row[col_index[mon]] = coeff
            rows.append(row)
    return labels, rows


def bareiss_rank(matrix: list[list[int]]) -> tuple[int, list[dict[str, int]]]:
    """Return exact rank using fraction-free Bareiss elimination."""
    if not matrix:
        return 0, []
    a = [row[:] for row in matrix]
    m = len(a)
    n = len(a[0])
    rank = 0
    prev = 1
    pivots: list[dict[str, int]] = []
    for col in range(n):
        pivot_row = None
        for row in range(rank, m):
            if a[row][col] != 0:
                pivot_row = row
                break
        if pivot_row is None:
            continue
        if pivot_row != rank:
            a[rank], a[pivot_row] = a[pivot_row], a[rank]
        pivot = a[rank][col]
        pivots.append({"step": rank + 1, "row": rank + 1, "col": col + 1, "pivot": pivot})
        for i in range(rank + 1, m):
            for j in range(col + 1, n):
                numerator = a[i][j] * pivot - a[i][col] * a[rank][j]
                if numerator % prev != 0:
                    raise ArithmeticError("Bareiss divisibility failed")
                a[i][j] = numerator // prev
            a[i][col] = 0
        prev = pivot
        rank += 1
        if rank == m:
            break
    return rank, pivots


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matrix_block(name: str, labels: list[str], basis: list[tuple[int, ...]], matrix: list[list[int]]) -> list[str]:
    lines = [f"{name} integer tangent matrix rows={len(matrix)} cols={len(basis)}"]
    lines.append("columns degree-3 exponent tuples:")
    lines.append(json.dumps([list(mon) for mon in basis]))
    lines.append("rows:")
    for label, row in zip(labels, matrix):
        lines.append(label + " " + json.dumps(row, separators=(",", ":")))
    return lines


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    log_path = root / "logs" / "T0_orbit_dimensions.log"
    cert_path = root / "certificates" / "T0_orbit_dimensions.json"
    script_path = Path(__file__).resolve()

    basis = degree_monomials(N, DEG)
    det_poly = det3()
    perm_poly = perm3()

    det_labels, det_matrix = tangent_matrix(det_poly, basis)
    perm_labels, perm_matrix = tangent_matrix(perm_poly, basis)

    det_rank, det_pivots = bareiss_rank(det_matrix)
    perm_rank, perm_pivots = bareiss_rank(perm_matrix)

    expected = {"det3": 65, "perm3": 77}
    status = {
        "det3_matches_expected": det_rank == expected["det3"],
        "perm3_matches_expected": perm_rank == expected["perm3"],
    }
    deduction = (
        "Since dim(GL9.perm3)=77 and dim(GL9.det3)=65, perm3 is not in X_det: "
        "otherwise X_perm=closure(GL9.perm3) would be contained in X_det, "
        "forcing dim(X_perm)<=dim(X_det). The GCT-relevant direction left by "
        "this dimension check is det3 in X_perm."
    )

    log_lines: list[str] = []
    log_lines.append("T0 - exact orbit dimensions")
    log_lines.append("tag: proved-alg by exact Lie-differential rank over Q")
    log_lines.append("arithmetic: integers only; Bareiss fraction-free elimination")
    log_lines.append(f"degree-3 monomial basis size = {len(basis)}")
    log_lines.extend(matrix_block("det3", det_labels, basis, det_matrix))
    log_lines.append(f"rank det3 = {det_rank}")
    log_lines.append(f"expected rank det3 = {expected['det3']}")
    log_lines.append("det3 Bareiss pivots:")
    log_lines.append(json.dumps(det_pivots))
    log_lines.extend(matrix_block("perm3", perm_labels, basis, perm_matrix))
    log_lines.append(f"rank perm3 = {perm_rank}")
    log_lines.append(f"expected rank perm3 = {expected['perm3']}")
    log_lines.append("perm3 Bareiss pivots:")
    log_lines.append(json.dumps(perm_pivots))
    log_lines.append("deduction: " + deduction)
    log_text = "\n".join(log_lines) + "\n"
    log_path.write_text(log_text, encoding="utf-8")

    cert = {
        "task": "T0",
        "tag": "proved-alg",
        "field": "Q",
        "method": "exact integer tangent matrix for gl9 action; Bareiss rank",
        "variables": [f"x{r + 1}{c + 1}" for r in range(3) for c in range(3)],
        "basis_size": len(basis),
        "matrix_shape": [81, len(basis)],
        "results": {
            "dim_GL9_orbit_det3": det_rank,
            "dim_GL9_orbit_perm3": perm_rank,
            "expected": expected,
            "status": status,
            "perm3_not_in_X_det_by_dimension": bool(det_rank < perm_rank),
        },
        "deduction": deduction,
        "limitations": "This is a dimension check only; it does not decide det3 in X_perm.",
        "artifacts": {
            "script": str(script_path),
            "log": str(log_path),
            "certificate": str(cert_path),
        },
    }
    cert_path.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(log_text, end="")
    print("certificate:", cert_path)
    print("script_sha256:", sha256_file(script_path))
    print("certificate_sha256:", sha256_file(cert_path))


if __name__ == "__main__":
    main()
