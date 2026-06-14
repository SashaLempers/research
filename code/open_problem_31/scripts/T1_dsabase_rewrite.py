#!/usr/bin/env python3
"""T1 - exact rewrite of det_3 and perm_3 in the (d,s,a) basis."""

from __future__ import annotations

import hashlib
import json
import random
from fractions import Fraction
from itertools import permutations
from pathlib import Path

random.seed(42)

N = 9
Y_NAMES = ["d1", "d2", "d3", "s12", "a12", "s13", "a13", "s23", "a23"]


def var_index(row: int, col: int) -> int:
    return 3 * row + col


def parity(perm: tuple[int, ...]) -> int:
    inversions = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                inversions += 1
    return -1 if inversions % 2 else 1


def x_var(idx: int) -> dict[tuple[int, ...], Fraction]:
    exp = [0] * N
    exp[idx] = 1
    return {tuple(exp): Fraction(1)}


def const(value: Fraction | int) -> dict[tuple[int, ...], Fraction]:
    return {tuple([0] * N): Fraction(value)}


def add(*polys: dict[tuple[int, ...], Fraction]) -> dict[tuple[int, ...], Fraction]:
    out: dict[tuple[int, ...], Fraction] = {}
    for poly in polys:
        for mon, coeff in poly.items():
            out[mon] = out.get(mon, Fraction(0)) + coeff
    return {mon: coeff for mon, coeff in out.items() if coeff}


def scale(poly: dict[tuple[int, ...], Fraction], scalar: Fraction | int) -> dict[tuple[int, ...], Fraction]:
    scalar = Fraction(scalar)
    return {mon: coeff * scalar for mon, coeff in poly.items() if coeff * scalar}


def mul(*polys: dict[tuple[int, ...], Fraction]) -> dict[tuple[int, ...], Fraction]:
    out = const(1)
    for poly in polys:
        new: dict[tuple[int, ...], Fraction] = {}
        for mon_a, coeff_a in out.items():
            for mon_b, coeff_b in poly.items():
                mon = tuple(a + b for a, b in zip(mon_a, mon_b))
                new[mon] = new.get(mon, Fraction(0)) + coeff_a * coeff_b
        out = {mon: coeff for mon, coeff in new.items() if coeff}
    return out


def monomial_poly(indices: list[int], coeff: int) -> dict[tuple[int, ...], Fraction]:
    exp = [0] * N
    for idx in indices:
        exp[idx] += 1
    return {tuple(exp): Fraction(coeff)}


def det3_x() -> dict[tuple[int, ...], Fraction]:
    terms = []
    for perm in permutations(range(3)):
        terms.append(monomial_poly([var_index(row, col) for row, col in enumerate(perm)], parity(perm)))
    return add(*terms)


def perm3_x() -> dict[tuple[int, ...], Fraction]:
    terms = []
    for perm in permutations(range(3)):
        terms.append(monomial_poly([var_index(row, col) for row, col in enumerate(perm)], 1))
    return add(*terms)


def y_linear_forms() -> dict[str, dict[tuple[int, ...], Fraction]]:
    x = [x_var(i) for i in range(N)]
    return {
        "d1": x[var_index(0, 0)],
        "d2": x[var_index(1, 1)],
        "d3": x[var_index(2, 2)],
        "s12": add(x[var_index(0, 1)], x[var_index(1, 0)]),
        "a12": add(x[var_index(0, 1)], scale(x[var_index(1, 0)], -1)),
        "s13": add(x[var_index(0, 2)], x[var_index(2, 0)]),
        "a13": add(x[var_index(0, 2)], scale(x[var_index(2, 0)], -1)),
        "s23": add(x[var_index(1, 2)], x[var_index(2, 1)]),
        "a23": add(x[var_index(1, 2)], scale(x[var_index(2, 1)], -1)),
    }


def term(forms: dict[str, dict[tuple[int, ...], Fraction]], coeff: Fraction, factors: list[str]) -> dict[tuple[int, ...], Fraction]:
    return scale(mul(*(forms[name] for name in factors)), coeff)


def det_guess(forms: dict[str, dict[tuple[int, ...], Fraction]]) -> dict[tuple[int, ...], Fraction]:
    q = Fraction(1, 4)
    return add(
        term(forms, 1, ["d1", "d2", "d3"]),
        term(forms, -q, ["d1", "s23", "s23"]),
        term(forms, -q, ["d2", "s13", "s13"]),
        term(forms, -q, ["d3", "s12", "s12"]),
        term(forms, q, ["d1", "a23", "a23"]),
        term(forms, q, ["d2", "a13", "a13"]),
        term(forms, q, ["d3", "a12", "a12"]),
        term(forms, q, ["s12", "s13", "s23"]),
        term(forms, -q, ["s12", "a13", "a23"]),
        term(forms, q, ["s13", "a12", "a23"]),
        term(forms, -q, ["s23", "a12", "a13"]),
    )


def perm_guess(forms: dict[str, dict[tuple[int, ...], Fraction]]) -> dict[tuple[int, ...], Fraction]:
    q = Fraction(1, 4)
    return add(
        term(forms, 1, ["d1", "d2", "d3"]),
        term(forms, q, ["d1", "s23", "s23"]),
        term(forms, q, ["d2", "s13", "s13"]),
        term(forms, q, ["d3", "s12", "s12"]),
        term(forms, -q, ["d1", "a23", "a23"]),
        term(forms, -q, ["d2", "a13", "a13"]),
        term(forms, -q, ["d3", "a12", "a12"]),
        term(forms, q, ["s12", "s13", "s23"]),
        term(forms, -q, ["s12", "a13", "a23"]),
        term(forms, q, ["s13", "a12", "a23"]),
        term(forms, -q, ["s23", "a12", "a13"]),
    )


def sub(poly_a: dict[tuple[int, ...], Fraction], poly_b: dict[tuple[int, ...], Fraction]) -> dict[tuple[int, ...], Fraction]:
    return add(poly_a, scale(poly_b, -1))


def frac_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def monomial_label(factors: list[str]) -> str:
    counts: dict[str, int] = {}
    for factor in factors:
        counts[factor] = counts.get(factor, 0) + 1
    pieces = []
    for name in Y_NAMES:
        if name not in counts:
            continue
        power = counts[name]
        pieces.append(name if power == 1 else f"{name}^{power}")
    return "*".join(pieces)


def support_entry(coeff: Fraction, factors: list[str]) -> dict[str, str]:
    return {"monomial": monomial_label(factors), "coefficient": frac_str(coeff)}


def y_supports() -> dict[str, list[dict[str, str]]]:
    q = Fraction(1, 4)
    common = [
        support_entry(Fraction(1), ["d1", "d2", "d3"]),
        support_entry(q, ["s12", "s13", "s23"]),
        support_entry(-q, ["s12", "a13", "a23"]),
        support_entry(q, ["s13", "a12", "a23"]),
        support_entry(-q, ["s23", "a12", "a13"]),
    ]
    sign_different = [
        support_entry(-q, ["d1", "s23", "s23"]),
        support_entry(-q, ["d2", "s13", "s13"]),
        support_entry(-q, ["d3", "s12", "s12"]),
        support_entry(q, ["d1", "a23", "a23"]),
        support_entry(q, ["d2", "a13", "a13"]),
        support_entry(q, ["d3", "a12", "a12"]),
    ]
    det_plus_perm = [
        support_entry(Fraction(2), ["d1", "d2", "d3"]),
        support_entry(Fraction(1, 2), ["s12", "s13", "s23"]),
        support_entry(Fraction(-1, 2), ["s12", "a13", "a23"]),
        support_entry(Fraction(1, 2), ["s13", "a12", "a23"]),
        support_entry(Fraction(-1, 2), ["s23", "a12", "a13"]),
    ]
    det_minus_perm = [
        support_entry(Fraction(-1, 2), ["d1", "s23", "s23"]),
        support_entry(Fraction(-1, 2), ["d2", "s13", "s13"]),
        support_entry(Fraction(-1, 2), ["d3", "s12", "s12"]),
        support_entry(Fraction(1, 2), ["d1", "a23", "a23"]),
        support_entry(Fraction(1, 2), ["d2", "a13", "a13"]),
        support_entry(Fraction(1, 2), ["d3", "a12", "a12"]),
    ]
    return {
        "common_support_same_coefficients": common,
        "support_with_opposite_signs_listed_as_det_coefficients": sign_different,
        "det3_plus_perm3": det_plus_perm,
        "det3_minus_perm3": det_minus_perm,
    }


def poly_to_sparse_strings(poly: dict[tuple[int, ...], Fraction]) -> list[dict[str, object]]:
    out = []
    for mon in sorted(poly):
        out.append({"exp": list(mon), "coeff": frac_str(poly[mon])})
    return out


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    log_path = root / "logs" / "T1_dsabase_rewrite.log"
    cert_path = root / "certificates" / "T1_dsabase_rewrite.json"
    script_path = Path(__file__).resolve()

    forms = y_linear_forms()
    det_formula = det_guess(forms)
    perm_formula = perm_guess(forms)
    det_exact = det3_x()
    perm_exact = perm3_x()

    det_diff = sub(det_formula, det_exact)
    perm_diff = sub(perm_formula, perm_exact)
    det_ok = det_diff == {}
    perm_ok = perm_diff == {}
    supports = y_supports()

    log_lines = [
        "T1 - exact rewrite in (d,s,a) basis",
        "tag: proved-alg by exact expansion over Q",
        "arithmetic: Fraction over Q; no floating point",
        f"expand(det_guess - det3) == 0: {det_ok}",
        f"expand(perm_guess - perm3) == 0: {perm_ok}",
        "det_guess - det3 sparse remainder:",
        json.dumps(poly_to_sparse_strings(det_diff), indent=2),
        "perm_guess - perm3 sparse remainder:",
        json.dumps(poly_to_sparse_strings(perm_diff), indent=2),
        "common support and sign-different support in (d,s,a):",
        json.dumps(supports, indent=2),
    ]
    log_text = "\n".join(log_lines) + "\n"
    log_path.write_text(log_text, encoding="utf-8")

    cert = {
        "task": "T1",
        "tag": "proved-alg",
        "field": "Q",
        "method": "exact expansion from (d,s,a) linear forms back to x_ij",
        "equalities": {
            "det_guess_minus_det3_is_zero": det_ok,
            "perm_guess_minus_perm3_is_zero": perm_ok,
        },
        "supports": supports,
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
