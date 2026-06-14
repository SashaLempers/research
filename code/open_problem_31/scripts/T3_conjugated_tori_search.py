#!/usr/bin/env python3
"""T3 - exact search engine for conjugated GL3xGL3 one-parameter tori.

This script implements the T3 family

    A(t)=U diag(t^a1,t^a2,t^a3) U^{-1},
    B(t)=V diag(t^b1,t^b2,t^b3) V^{-1},
    g(t)=A(t) tensor B(t),

and tests whether the initial form of g(t).perm_3 is a nonzero scalar multiple
of det_3.  The arithmetic is exact over Q.  The default command is deliberately
checkpoint-friendly and can run partial searches over a case interval; a partial
run is tagged comp-obs and is never an exhaustive failure certificate.

Interpretation of the "augmented by permutations and sign diagonals" library:
for each base U, include P*S*U where P is a 3x3 permutation matrix and S is a
diagonal sign matrix.  Right permutation of U only reorders the exponent triple,
which is already enumerated; right sign multiplication commutes with diag(t^a)
and cancels in U diag U^{-1}.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import time
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path

random.seed(42)

N3 = 3
N9 = 9

Matrix = tuple[tuple[Fraction, ...], ...]
Laurent = dict[int, Fraction]
XPoly = dict[tuple[int, ...], Laurent]


def frac(value: int | Fraction) -> Fraction:
    return value if isinstance(value, Fraction) else Fraction(value)


def fstr(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mat_from_ints(rows: list[list[int]]) -> Matrix:
    return tuple(tuple(Fraction(x) for x in row) for row in rows)


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(N3)) for j in range(N3))
        for i in range(N3)
    )


def mat_key(a: Matrix) -> tuple[tuple[str, ...], ...]:
    return tuple(tuple(fstr(x) for x in row) for row in a)


def det3_matrix(a: Matrix) -> Fraction:
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )


def mat_inv(a: Matrix) -> Matrix:
    det = det3_matrix(a)
    if det == 0:
        raise ValueError("singular matrix")
    cof = [
        [
            a[1][1] * a[2][2] - a[1][2] * a[2][1],
            -(a[1][0] * a[2][2] - a[1][2] * a[2][0]),
            a[1][0] * a[2][1] - a[1][1] * a[2][0],
        ],
        [
            -(a[0][1] * a[2][2] - a[0][2] * a[2][1]),
            a[0][0] * a[2][2] - a[0][2] * a[2][0],
            -(a[0][0] * a[2][1] - a[0][1] * a[2][0]),
        ],
        [
            a[0][1] * a[1][2] - a[0][2] * a[1][1],
            -(a[0][0] * a[1][2] - a[0][2] * a[1][0]),
            a[0][0] * a[1][1] - a[0][1] * a[1][0],
        ],
    ]
    adj = [[cof[j][i] / det for j in range(N3)] for i in range(N3)]
    return tuple(tuple(row) for row in adj)


def perm_matrix(perm: tuple[int, ...]) -> Matrix:
    rows = []
    for i in range(N3):
        rows.append([1 if perm[i] == j else 0 for j in range(N3)])
    return mat_from_ints(rows)


def sign_matrix(signs: tuple[int, ...]) -> Matrix:
    return mat_from_ints([[signs[i] if i == j else 0 for j in range(N3)] for i in range(N3)])


def base_u3() -> list[Matrix]:
    return [
        mat_from_ints([[1, 0, 0], [0, 1, 0], [0, 0, 1]]),
        mat_from_ints([[1, 1, 0], [0, 1, 1], [0, 0, 1]]),
        mat_from_ints([[1, 0, 0], [1, 1, 0], [0, 1, 1]]),
        mat_from_ints([[1, 1, 1], [0, 1, 1], [0, 0, 1]]),
    ]


def augmented_u3(limit: int | None = None) -> list[Matrix]:
    seen: set[tuple[tuple[str, ...], ...]] = set()
    out: list[Matrix] = []
    for base in base_u3():
        for perm in permutations(range(N3)):
            p = perm_matrix(perm)
            for signs in product((-1, 1), repeat=N3):
                s = sign_matrix(signs)
                u = mat_mul(mat_mul(p, s), base)
                key = mat_key(u)
                if key not in seen:
                    seen.add(key)
                    out.append(u)
                    if limit is not None and len(out) >= limit:
                        return out
    return out


def exponent_triples(bound: int, canonical_shift: bool) -> list[tuple[int, int, int]]:
    triples = list(product(range(-bound, bound + 1), repeat=3))
    if not canonical_shift:
        return [tuple(t) for t in triples]
    out: list[tuple[int, int, int]] = []
    seen: set[tuple[int, int, int]] = set()
    for triple in triples:
        mn = min(triple)
        can = tuple(x - mn for x in triple)
        if can not in seen:
            seen.add(can)
            out.append(can)
    return out


def lp_add(a: Laurent, b: Laurent) -> Laurent:
    out = dict(a)
    for exp, coeff in b.items():
        out[exp] = out.get(exp, Fraction(0)) + coeff
        if out[exp] == 0:
            del out[exp]
    return out


def lp_mul(a: Laurent, b: Laurent) -> Laurent:
    out: Laurent = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            exp = ea + eb
            out[exp] = out.get(exp, Fraction(0)) + ca * cb
            if out[exp] == 0:
                del out[exp]
    return out


def lp_from_term(exp: int, coeff: Fraction) -> Laurent:
    return {} if coeff == 0 else {exp: coeff}


def one_parameter_matrix(u: Matrix, exps: tuple[int, int, int]) -> list[list[Laurent]]:
    inv = mat_inv(u)
    out: list[list[Laurent]] = [[{} for _ in range(N3)] for _ in range(N3)]
    for i in range(N3):
        for j in range(N3):
            entry: Laurent = {}
            for k in range(N3):
                coeff = u[i][k] * inv[k][j]
                entry = lp_add(entry, lp_from_term(exps[k], coeff))
            out[i][j] = entry
    return out


def var_index(row: int, col: int) -> int:
    return 3 * row + col


def parity(perm: tuple[int, ...]) -> int:
    inversions = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                inversions += 1
    return -1 if inversions % 2 else 1


def det3_target() -> dict[tuple[int, ...], Fraction]:
    out: dict[tuple[int, ...], Fraction] = {}
    for perm in permutations(range(N3)):
        exp = [0] * N9
        for row, col in enumerate(perm):
            exp[var_index(row, col)] += 1
        out[tuple(exp)] = Fraction(parity(perm))
    return out


def add_xpoly(poly: XPoly, mon: tuple[int, ...], coeff: Laurent) -> None:
    if not coeff:
        return
    old = poly.get(mon, {})
    new = lp_add(old, coeff)
    if new:
        poly[mon] = new
    elif mon in poly:
        del poly[mon]


def multiply_by_linear(poly: XPoly, linear: list[tuple[int, Laurent]]) -> XPoly:
    out: XPoly = {}
    for mon, coeff in poly.items():
        for vidx, lcoeff in linear:
            new_mon = list(mon)
            new_mon[vidx] += 1
            add_xpoly(out, tuple(new_mon), lp_mul(coeff, lcoeff))
    return out


def transformed_variable(a_mat: list[list[Laurent]], b_mat: list[list[Laurent]], row: int, col: int) -> list[tuple[int, Laurent]]:
    linear: list[tuple[int, Laurent]] = []
    for p in range(N3):
        for q in range(N3):
            coeff = lp_mul(a_mat[row][p], b_mat[col][q])
            if coeff:
                linear.append((var_index(p, q), coeff))
    return linear


def transform_perm(a_mat: list[list[Laurent]], b_mat: list[list[Laurent]]) -> XPoly:
    total: XPoly = {}
    for sigma in permutations(range(N3)):
        term_poly: XPoly = {tuple([0] * N9): {0: Fraction(1)}}
        for row, col in enumerate(sigma):
            term_poly = multiply_by_linear(term_poly, transformed_variable(a_mat, b_mat, row, col))
        for mon, coeff in term_poly.items():
            add_xpoly(total, mon, coeff)
    return total


def initial_form(poly: XPoly) -> tuple[int | None, dict[tuple[int, ...], Fraction]]:
    min_exp = None
    for coeff in poly.values():
        for exp in coeff:
            if min_exp is None or exp < min_exp:
                min_exp = exp
    if min_exp is None:
        return None, {}
    init: dict[tuple[int, ...], Fraction] = {}
    for mon, coeff in poly.items():
        c = coeff.get(min_exp, Fraction(0))
        if c:
            init[mon] = c
    return min_exp, init


def scalar_multiple_of_det(poly: dict[tuple[int, ...], Fraction]) -> tuple[bool, Fraction | None]:
    target = det3_target()
    if set(poly) != set(target):
        return False, None
    first = next(iter(target))
    scalar = poly[first] / target[first]
    if scalar == 0:
        return False, None
    for mon, coeff in target.items():
        if poly[mon] != scalar * coeff:
            return False, None
    return True, scalar


def serialize_matrix(u: Matrix) -> list[list[str]]:
    return [[fstr(x) for x in row] for row in u]


def laurent_matrix_key(a: list[list[Laurent]]) -> tuple[tuple[tuple[tuple[int, str], ...], ...], ...]:
    return tuple(
        tuple(tuple(sorted((exp, fstr(coeff)) for exp, coeff in cell.items())) for cell in row)
        for row in a
    )


def serialize_initial(init: dict[tuple[int, ...], Fraction]) -> list[dict[str, object]]:
    return [{"exp": list(mon), "coeff": fstr(init[mon])} for mon in sorted(init)]


def run_search(args: argparse.Namespace) -> dict[str, object]:
    u_lib = augmented_u3(args.max_u)
    exp_lib = exponent_triples(args.bound, args.canonical_shift)
    if args.max_exponents is not None:
        exp_lib = exp_lib[: args.max_exponents]

    start = time.time()
    cases = 0
    found = None
    best_support_size = None
    best_record = None

    raw_precomputed = []
    for ui, u in enumerate(u_lib):
        for exps in exp_lib:
            raw_precomputed.append((ui, u, exps, one_parameter_matrix(u, exps)))

    if args.dedupe:
        dedup: dict[tuple[tuple[tuple[tuple[int, str], ...], ...], ...], dict[str, object]] = {}
        for ui, u, exps, mat in raw_precomputed:
            key = laurent_matrix_key(mat)
            if key not in dedup:
                dedup[key] = {
                    "record": (ui, u, exps, mat),
                    "covered_raw_count": 1,
                }
            else:
                dedup[key]["covered_raw_count"] = int(dedup[key]["covered_raw_count"]) + 1
        precomputed = [entry["record"] for entry in dedup.values()]
        covered_counts = [int(entry["covered_raw_count"]) for entry in dedup.values()]
    else:
        precomputed = raw_precomputed
        covered_counts = [1 for _ in precomputed]

    pair_total = len(precomputed) * len(precomputed)
    start_case = args.start_case
    if start_case < 1:
        raise ValueError("--start-case must be >= 1")
    stop_after = args.case_limit if args.case_limit is not None else args.max_families

    for left_index, (ui, u, a_exp, a_mat) in enumerate(precomputed):
        for right_index, (vi, v, b_exp, b_mat) in enumerate(precomputed):
            global_case = left_index * len(precomputed) + right_index + 1
            if global_case < start_case:
                continue
            cases += 1
            poly = transform_perm(a_mat, b_mat)
            valuation, init = initial_form(poly)
            is_match, scalar = scalar_multiple_of_det(init)
            support_size = len(init)
            if best_support_size is None or abs(support_size - 6) < abs(best_support_size - 6):
                best_support_size = support_size
                best_record = {
                    "case": global_case,
                    "U_index": ui,
                    "V_index": vi,
                    "a": list(a_exp),
                    "b": list(b_exp),
                    "valuation": valuation,
                    "initial_support_size": support_size,
                    "initial_form": serialize_initial(init),
                }
            if is_match:
                found = {
                    "case": global_case,
                    "U_index": ui,
                    "V_index": vi,
                    "U": serialize_matrix(u),
                    "V": serialize_matrix(v),
                    "a": list(a_exp),
                    "b": list(b_exp),
                    "valuation": valuation,
                    "scalar": fstr(scalar),
                    "initial_form": serialize_initial(init),
                }
                break
            if stop_after is not None and cases >= stop_after:
                break
        if found is not None or (stop_after is not None and cases >= stop_after):
            break

    last_case = start_case + cases - 1 if cases else start_case - 1
    completed_for_parameter_set = found is not None or last_case >= pair_total
    full_t3_scope = (
        args.max_u is None
        and args.max_exponents is None
        and start_case == 1
        and completed_for_parameter_set
    )
    exhausted_full_t3_scope = found is None and full_t3_scope
    tag = "qq-cert" if found else ("claimed-comp" if exhausted_full_t3_scope else "comp-obs")
    elapsed = time.time() - start
    return {
        "task": "T3",
        "tag": tag,
        "field": "Q",
        "method": "exact Laurent-polynomial initial form search for conjugated GL3xGL3 tori",
        "interpretation": "U-library generated as P*S*U_base; exponent triples optionally quotient common additive shifts.",
        "parameters": {
            "bound": args.bound,
            "canonical_shift": args.canonical_shift,
            "dedupe": args.dedupe,
            "max_u": args.max_u,
            "max_exponents": args.max_exponents,
            "max_families": args.max_families,
            "start_case": args.start_case,
            "case_limit": args.case_limit,
        },
        "library_sizes": {
            "U_library": len(u_lib),
            "exponent_triples": len(exp_lib),
            "raw_one_parameter_matrices": len(raw_precomputed),
            "precomputed_one_parameter_matrices": len(precomputed),
            "dedupe_min_raw_coverage_per_matrix": min(covered_counts) if covered_counts else 0,
            "dedupe_max_raw_coverage_per_matrix": max(covered_counts) if covered_counts else 0,
            "full_pair_count_for_this_parameter_set": pair_total,
            "scalar_shift_quotient_covers_all_exponents_in_bound": bool(args.canonical_shift),
        },
        "searched_families": cases,
        "searched_case_interval": [start_case, last_case],
        "search_completed_for_parameter_set": completed_for_parameter_set,
        "full_T3_scope_completed": full_t3_scope,
        "exhausted_full_T3_scope_without_match": exhausted_full_t3_scope,
        "found_det3_initial_form": found is not None,
        "found_family": found,
        "best_near_support_record": best_record,
        "elapsed_seconds": elapsed,
        "limitations": (
            "If search_completed_for_parameter_set is false, this is only a partial run and proves no exhaustive failure."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=4)
    parser.add_argument("--max-u", type=int, default=None)
    parser.add_argument("--max-exponents", type=int, default=None)
    parser.add_argument("--max-families", type=int, default=None)
    parser.add_argument("--start-case", type=int, default=1)
    parser.add_argument("--case-limit", type=int, default=None)
    parser.add_argument("--dedupe", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--canonical-shift", action=argparse.BooleanOptionalAction, default=True)
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    log_path = root / "logs" / "T3_conjugated_tori_search.log"
    cert_path = root / "certificates" / "T3_conjugated_tori_search.json"
    script_path = Path(__file__).resolve()

    cert = run_search(args)
    cert["artifacts"] = {
        "script": str(script_path),
        "log": str(log_path),
        "certificate": str(cert_path),
    }

    log_lines = [
        "T3 - conjugated GL3xGL3 tori exact search",
        f"tag: {cert['tag']}",
        "arithmetic: Fraction over Q and Laurent exponents in Z; no floating point",
        "IMPORTANT: partial searches are comp-obs only and prove no exhaustive failure.",
        json.dumps(cert, indent=2, sort_keys=True),
    ]
    log_text = "\n".join(log_lines) + "\n"
    log_path.write_text(log_text, encoding="utf-8")
    cert_path.write_text(json.dumps(cert, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(log_text, end="")
    print("certificate:", cert_path)
    print("script_sha256:", sha256_file(script_path))
    print("certificate_sha256:", sha256_file(cert_path))


if __name__ == "__main__":
    main()
