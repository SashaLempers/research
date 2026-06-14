#!/usr/bin/env python3
"""T4 exact checkpointable search in the (d,s,a) basis.

Family:
    g(t) = H diag(t^e)
    H = H_d direct_sum H_12 direct_sum H_13 direct_sum H_23

with H_d in the four U_3 base matrices and each H_ij in the augmented U_2
library (left multiplication by permutations and sign diagonals).  The action is
implemented exactly as the prompt states: y_i is replaced by the i-th row of
H diag(t^e) times the y-coordinate vector.

This script is designed for checkpoints.  It is not an exhaustive certificate
unless the JSON field full_T4_scope_completed is true.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import time
from fractions import Fraction
from itertools import product
from pathlib import Path

random.seed(42)

Y_NAMES = ["d1", "d2", "d3", "s12", "a12", "s13", "a13", "s23", "a23"]
DET_SUPPORT_SIZE = 11

Laurent = dict[int, Fraction]
Poly = dict[tuple[int, ...], Laurent]
Matrix = tuple[tuple[Fraction, ...], ...]


def fstr(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def mat_from_ints(rows: list[list[int]]) -> Matrix:
    return tuple(tuple(Fraction(x) for x in row) for row in rows)


def mat_mul(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    m = len(b[0])
    kdim = len(b)
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(kdim)) for j in range(m))
        for i in range(n)
    )


def mat_key(a: Matrix) -> tuple[tuple[str, ...], ...]:
    return tuple(tuple(fstr(x) for x in row) for row in a)


def u3_base() -> list[Matrix]:
    return [
        mat_from_ints([[1, 0, 0], [0, 1, 0], [0, 0, 1]]),
        mat_from_ints([[1, 1, 0], [0, 1, 1], [0, 0, 1]]),
        mat_from_ints([[1, 0, 0], [1, 1, 0], [0, 1, 1]]),
        mat_from_ints([[1, 1, 1], [0, 1, 1], [0, 0, 1]]),
    ]


def perm_matrix_2(swap: bool) -> Matrix:
    return mat_from_ints([[0, 1], [1, 0]]) if swap else mat_from_ints([[1, 0], [0, 1]])


def sign_matrix_2(signs: tuple[int, int]) -> Matrix:
    return mat_from_ints([[signs[0], 0], [0, signs[1]]])


def u2_augmented() -> list[Matrix]:
    bases = [
        mat_from_ints([[1, 0], [0, 1]]),
        mat_from_ints([[1, 1], [0, 1]]),
        mat_from_ints([[1, 0], [1, 1]]),
        mat_from_ints([[1, 1], [1, -1]]),
    ]
    out: list[Matrix] = []
    seen: set[tuple[tuple[str, ...], ...]] = set()
    for base in bases:
        for swap in (False, True):
            p = perm_matrix_2(swap)
            for signs in product((-1, 1), repeat=2):
                s = sign_matrix_2(signs)
                h = mat_mul(mat_mul(p, s), base)
                key = mat_key(h)
                if key not in seen:
                    seen.add(key)
                    out.append(h)
    return out


def block_diag(hd: Matrix, h12: Matrix, h13: Matrix, h23: Matrix) -> Matrix:
    out = [[Fraction(0) for _ in range(9)] for _ in range(9)]
    blocks = [(0, hd), (3, h12), (5, h13), (7, h23)]
    for offset, block in blocks:
        for i, row in enumerate(block):
            for j, val in enumerate(row):
                out[offset + i][offset + j] = val
    return tuple(tuple(row) for row in out)


def h_library(max_h: int | None = None) -> list[Matrix]:
    u2 = u2_augmented()
    seen: set[tuple[tuple[str, ...], ...]] = set()
    out: list[Matrix] = []
    for hd in u3_base():
        for h12 in u2:
            for h13 in u2:
                for h23 in u2:
                    h = block_diag(hd, h12, h13, h23)
                    key = mat_key(h)
                    if key not in seen:
                        seen.add(key)
                        out.append(h)
                        if max_h is not None and len(out) >= max_h:
                            return out
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


def lp_term(exp: int, coeff: Fraction) -> Laurent:
    return {} if coeff == 0 else {exp: coeff}


def poly_add_monomial(poly: Poly, mon: tuple[int, ...], coeff: Laurent) -> None:
    if not coeff:
        return
    old = poly.get(mon, {})
    new = lp_add(old, coeff)
    if new:
        poly[mon] = new
    elif mon in poly:
        del poly[mon]


def multiply_by_linear(poly: Poly, linear: list[tuple[int, Laurent]]) -> Poly:
    out: Poly = {}
    for mon, coeff in poly.items():
        for var_idx, lcoeff in linear:
            new_mon = list(mon)
            new_mon[var_idx] += 1
            poly_add_monomial(out, tuple(new_mon), lp_mul(coeff, lcoeff))
    return out


def sparse_poly_from_terms(terms: list[tuple[Fraction, list[int]]]) -> dict[tuple[int, ...], Fraction]:
    out: dict[tuple[int, ...], Fraction] = {}
    for coeff, factors in terms:
        exp = [0] * 9
        for idx in factors:
            exp[idx] += 1
        exp_t = tuple(exp)
        out[exp_t] = out.get(exp_t, Fraction(0)) + coeff
        if out[exp_t] == 0:
            del out[exp_t]
    return out


def perm_y() -> dict[tuple[int, ...], Fraction]:
    q = Fraction(1, 4)
    return sparse_poly_from_terms(
        [
            (Fraction(1), [0, 1, 2]),
            (q, [0, 7, 7]),
            (q, [1, 5, 5]),
            (q, [2, 3, 3]),
            (-q, [0, 8, 8]),
            (-q, [1, 6, 6]),
            (-q, [2, 4, 4]),
            (q, [3, 5, 7]),
            (-q, [3, 6, 8]),
            (q, [5, 4, 8]),
            (-q, [7, 4, 6]),
        ]
    )


def det_y() -> dict[tuple[int, ...], Fraction]:
    q = Fraction(1, 4)
    return sparse_poly_from_terms(
        [
            (Fraction(1), [0, 1, 2]),
            (-q, [0, 7, 7]),
            (-q, [1, 5, 5]),
            (-q, [2, 3, 3]),
            (q, [0, 8, 8]),
            (q, [1, 6, 6]),
            (q, [2, 4, 4]),
            (q, [3, 5, 7]),
            (-q, [3, 6, 8]),
            (q, [5, 4, 8]),
            (-q, [7, 4, 6]),
        ]
    )


def linear_forms(h: Matrix, exponents: tuple[int, ...]) -> list[list[tuple[int, Laurent]]]:
    forms: list[list[tuple[int, Laurent]]] = []
    for i in range(9):
        linear = []
        for j in range(9):
            coeff = h[i][j]
            if coeff:
                linear.append((j, lp_term(exponents[j], coeff)))
        forms.append(linear)
    return forms


def transform_poly(poly_q: dict[tuple[int, ...], Fraction], h: Matrix, exponents: tuple[int, ...]) -> Poly:
    forms = linear_forms(h, exponents)
    total: Poly = {}
    for mon, coeff in poly_q.items():
        term_poly: Poly = {tuple([0] * 9): {0: coeff}}
        for var_idx, power in enumerate(mon):
            for _ in range(power):
                term_poly = multiply_by_linear(term_poly, forms[var_idx])
        for out_mon, out_coeff in term_poly.items():
            poly_add_monomial(total, out_mon, out_coeff)
    return total


def initial_form(poly: Poly) -> tuple[int | None, dict[tuple[int, ...], Fraction]]:
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


def scalar_multiple(poly: dict[tuple[int, ...], Fraction], target: dict[tuple[int, ...], Fraction]) -> tuple[bool, Fraction | None]:
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


def monomial_label(mon: tuple[int, ...]) -> str:
    pieces = []
    for name, power in zip(Y_NAMES, mon):
        if power == 1:
            pieces.append(name)
        elif power > 1:
            pieces.append(f"{name}^{power}")
    return "*".join(pieces) if pieces else "1"


def serialize_sparse(poly: dict[tuple[int, ...], Fraction], max_terms: int | None = None) -> list[dict[str, object]]:
    terms = [
        {"monomial": monomial_label(mon), "exp": list(mon), "coeff": fstr(poly[mon])}
        for mon in sorted(poly, key=monomial_label)
    ]
    if max_terms is not None:
        return terms[:max_terms]
    return terms


def exponent_count(bound: int, canonical_shift: bool) -> int:
    if not canonical_shift:
        return (2 * bound + 1) ** 9
    return (2 * bound + 1) ** 9 - (2 * bound) ** 9


def exponent_generator(bound: int, canonical_shift: bool):
    if canonical_shift:
        rng = range(0, 2 * bound + 1)
        for exps in product(rng, repeat=9):
            if min(exps) == 0:
                yield tuple(exps)
    else:
        rng = range(-bound, bound + 1)
        for exps in product(rng, repeat=9):
            yield tuple(exps)


def run_search(args: argparse.Namespace) -> dict[str, object]:
    start_time = time.time()
    h_lib = h_library(args.max_h)
    exp_total = exponent_count(args.bound, args.canonical_shift)
    pair_total = len(h_lib) * exp_total

    target = det_y()
    source = perm_y()
    cases = 0
    found = None
    filtered_by_size = 0
    passed_size_filter = 0
    exact_support_matches = 0
    quasi_matches = []
    best_record = None
    best_distance = None

    start_case = args.start_case
    if start_case < 1:
        raise ValueError("--start-case must be >= 1")

    for h_index, h in enumerate(h_lib):
        for exp_index, exps in enumerate(exponent_generator(args.bound, args.canonical_shift)):
            global_case = h_index * exp_total + exp_index + 1
            if global_case < start_case:
                continue
            if args.case_limit is not None and cases >= args.case_limit:
                break
            cases += 1

            transformed = transform_poly(source, h, exps)
            valuation, init = initial_form(transformed)
            support_size = len(init)
            distance = abs(support_size - DET_SUPPORT_SIZE)
            if best_distance is None or distance < best_distance:
                best_distance = distance
                best_record = {
                    "case": global_case,
                    "H_index": h_index,
                    "exponent_index": exp_index,
                    "exponents": list(exps),
                    "valuation": valuation,
                    "initial_support_size": support_size,
                    "support_filter": "passed_size" if support_size == DET_SUPPORT_SIZE else "rejected_size",
                    "initial_form_sample": serialize_sparse(init, max_terms=20),
                }

            # Conservative early filter: a signed permutation cannot change support cardinality.
            if support_size != DET_SUPPORT_SIZE:
                filtered_by_size += 1
                continue
            passed_size_filter += 1

            if set(init) == set(target):
                exact_support_matches += 1
                is_match, scalar = scalar_multiple(init, target)
                record = {
                    "case": global_case,
                    "H_index": h_index,
                    "exponent_index": exp_index,
                    "exponents": list(exps),
                    "valuation": valuation,
                    "scalar": fstr(scalar) if scalar is not None else None,
                    "initial_form": serialize_sparse(init),
                }
                if is_match:
                    found = record
                    break
                if len(quasi_matches) < args.max_quasi:
                    record["reason"] = "same support as det_y, coefficients not a scalar multiple"
                    quasi_matches.append(record)
        if found is not None or (args.case_limit is not None and cases >= args.case_limit):
            break

    last_case = start_case + cases - 1 if cases else start_case - 1
    full_completed = found is None and args.max_h is None and start_case == 1 and last_case >= pair_total
    tag = "comp-obs"
    if full_completed:
        tag = "claimed-comp"
    if found is not None:
        tag = "comp-obs"

    return {
        "task": "T4",
        "tag": tag,
        "field": "Q",
        "method": "exact Laurent-polynomial checkpoint search in (d,s,a) block family",
        "parameters": {
            "bound": args.bound,
            "canonical_shift": args.canonical_shift,
            "max_h": args.max_h,
            "start_case": args.start_case,
            "case_limit": args.case_limit,
            "max_quasi": args.max_quasi,
        },
        "library_sizes": {
            "U3_base_size": len(u3_base()),
            "U2_augmented_size": len(u2_augmented()),
            "H_library_size": len(h_lib),
            "exponent_vector_count": exp_total,
            "full_case_count_for_parameter_set": pair_total,
            "scalar_shift_quotient_covers_all_exponents_in_bound": bool(args.canonical_shift),
        },
        "searched_cases": cases,
        "searched_case_interval": [start_case, last_case],
        "support_filter": {
            "description": "Conservative cardinality filter only: reject only if support size differs from det_y support size 11; signed permutations preserve cardinality.",
            "filtered_by_size": filtered_by_size,
            "passed_size_filter": passed_size_filter,
            "exact_det_support_matches": exact_support_matches,
        },
        "found_exact_match_requiring_T5": found is not None,
        "found_match": found,
        "quasi_matches": quasi_matches,
        "best_near_support_record": best_record,
        "full_T4_scope_completed": full_completed,
        "limitations": "Partial checkpoints are comp-obs and do not prove exhaustive T4 failure.",
        "elapsed_seconds": time.time() - start_time,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=6)
    parser.add_argument("--canonical-shift", action=argparse.BooleanOptionalAction, default=True)
    parser.add_argument("--max-h", type=int, default=None)
    parser.add_argument("--start-case", type=int, default=1)
    parser.add_argument("--case-limit", type=int, default=1000)
    parser.add_argument("--max-quasi", type=int, default=20)
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    log_path = root / "logs" / "T4_blocks_search.log"
    cert_path = root / "certificates" / "T4_blocks_search.json"
    script_path = Path(__file__).resolve()

    cert = run_search(args)
    cert["artifacts"] = {
        "script": str(script_path),
        "log": str(log_path),
        "certificate": str(cert_path),
    }

    log_lines = [
        "T4 block-family exact checkpoint search",
        f"tag: {cert['tag']}",
        "arithmetic: Fraction over Q and Laurent exponents in Z; no floating point",
        "support filter: conservative cardinality filter only",
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
