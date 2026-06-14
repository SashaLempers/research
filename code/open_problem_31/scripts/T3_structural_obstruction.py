#!/usr/bin/env python3
"""T3 structural obstruction certificate.

This script certifies, by exact integer polynomial arithmetic, the lemma:

For P,Q in GL_3 and F_{P,Q}(Y)=perm_3(P Y Q^T), the coefficient of every
permutation monomial M_rho=prod_i y_{i,rho(i)} is perm(P)*perm(Q), independent
of rho.

The computation uses no floating point arithmetic.  Polynomial identities are
checked as exact equality of dictionaries of integer monomials.
"""

from __future__ import annotations

import hashlib
import json
import random
from itertools import permutations
from pathlib import Path

random.seed(42)

N = 3
PQ_VARS = [f"p{i + 1}{j + 1}" for i in range(N) for j in range(N)] + [
    f"q{i + 1}{j + 1}" for i in range(N) for j in range(N)
]

Poly = dict[tuple[int, ...], int]


def p_index(i: int, j: int) -> int:
    return 3 * i + j


def q_index(i: int, j: int) -> int:
    return 9 + 3 * i + j


def y_index(i: int, j: int) -> int:
    return 3 * i + j


def monomial_var(var_idx: int) -> Poly:
    exp = [0] * 18
    exp[var_idx] = 1
    return {tuple(exp): 1}


def add(a: Poly, b: Poly) -> Poly:
    out = dict(a)
    for mon, coeff in b.items():
        out[mon] = out.get(mon, 0) + coeff
        if out[mon] == 0:
            del out[mon]
    return out


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, {mon: -coeff for mon, coeff in b.items()})


def mul(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            mon = tuple(x + y for x, y in zip(ma, mb))
            out[mon] = out.get(mon, 0) + ca * cb
            if out[mon] == 0:
                del out[mon]
    return out


def product_polys(polys: list[Poly]) -> Poly:
    out: Poly = {tuple([0] * 18): 1}
    for poly in polys:
        out = mul(out, poly)
    return out


def perm_matrix_poly(prefix: str) -> Poly:
    """Permanent of the formal P or Q matrix."""
    terms: Poly = {}
    for sigma in permutations(range(N)):
        factors = []
        for i, j in enumerate(sigma):
            if prefix == "p":
                factors.append(monomial_var(p_index(i, j)))
            elif prefix == "q":
                factors.append(monomial_var(q_index(i, j)))
            else:
                raise ValueError(prefix)
        terms = add(terms, product_polys(factors))
    return terms


def coeff_m_rho(rho: tuple[int, ...]) -> Poly:
    """Coefficient of M_rho in perm(PYQ^T)."""
    total: Poly = {}
    for sigma in permutations(range(N)):
        # tau chooses which Y-row appears in each of the three permanent factors.
        for tau in permutations(range(N)):
            factors = []
            for i in range(N):
                y_row = tau[i]
                y_col = rho[y_row]
                factors.append(monomial_var(p_index(i, y_row)))
                factors.append(monomial_var(q_index(sigma[i], y_col)))
            total = add(total, product_polys(factors))
    return total


def format_monomial(mon: tuple[int, ...]) -> str:
    pieces = []
    for name, power in zip(PQ_VARS, mon):
        if power == 1:
            pieces.append(name)
        elif power > 1:
            pieces.append(f"{name}^{power}")
    return "*".join(pieces) if pieces else "1"


def poly_terms(poly: Poly) -> list[dict[str, object]]:
    return [
        {"monomial": format_monomial(mon), "coefficient": coeff}
        for mon, coeff in sorted(poly.items(), key=lambda item: format_monomial(item[0]))
    ]


def permutation_name(perm: tuple[int, ...]) -> str:
    return "".join(str(x + 1) for x in perm)


def weight_vector_for_m_rho(rho: tuple[int, ...]) -> tuple[int, ...]:
    # Coordinates are a1,a2,a3,b1,b2,b3.  M_rho has weight sum_i a_i+b_{rho(i)}.
    counts = [1, 1, 1, 0, 0, 0]
    for i in range(N):
        counts[3 + rho[i]] += 1
    return tuple(counts)


def weight_label(vec: tuple[int, ...]) -> str:
    names = ["a1", "a2", "a3", "b1", "b2", "b3"]
    terms = []
    for name, count in zip(names, vec):
        terms.extend([name] * count)
    return "+".join(terms)


def theorem_tex() -> str:
    return r"""\begin{theorem}[T3 structural obstruction]
Let \(P,Q\in GL_3\), let \(F_{P,Q}(Y)=\operatorname{perm}_3(PYQ^T)\), and let
\(M_\rho=\prod_i y_{i,\rho(i)}\) for \(\rho\in S_3\). Then
\[
  [M_\rho]F_{P,Q}=\operatorname{perm}(P)\operatorname{perm}(Q)
\]
for every \(\rho\in S_3\). In particular the six coefficients are independent
of \(\rho\).

Consequently no one-parameter torus conjugated inside \(GL_3\times GL_3\),
\[
 A(t)=U\operatorname{diag}(t^{a_i})U^{-1},\qquad
 B(t)=V\operatorname{diag}(t^{b_j})V^{-1},
\]
can degenerate \(\operatorname{perm}_3\) to a nonzero scalar multiple of
\(\operatorname{det}_3\).
\end{theorem}

\begin{proof}
Expanding \(F_{P,Q}\), the coefficient of \(M_\rho\) is obtained by choosing a
permutation \(\tau\) of the \(Y\)-rows in the three factors of the permanent and
a permutation \(\sigma\) from the outer permanent:
\[
 \sum_{\sigma,\tau\in S_3}\prod_i p_{i,\tau(i)}q_{\sigma(i),\rho(\tau(i))}.
\]
The \(p\)-part is \(\operatorname{perm}(P)\), and, after reindexing, the
\(q\)-part is \(\operatorname{perm}(Q)\); the column permutation \(\rho\) does
not change a permanent. Thus all six coefficients are equal to
\(\operatorname{perm}(P)\operatorname{perm}(Q)\).

For a conjugated torus \(A(t)\otimes B(t)\), every \(M_\rho\) has toric weight
\(\sum_i a_i+\sum_j b_j\). Hence the six permutation monomials survive or
disappear together in any initial form. If their common coefficient is nonzero,
the six coefficients are equal and cannot be proportional to the alternating
signs of \(\det_3\). If it is zero, all six are zero, while \(\det_3\) has all
six coefficients nonzero. Therefore no such initial form is \(c\det_3\) with
\(c\ne0\).
\end{proof}"""


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    log_path = root / "logs" / "T3_structural_obstruction.log"
    cert_path = root / "certificates" / "T3_structural_obstruction.json"
    script_path = Path(__file__).resolve()

    perm_p = perm_matrix_poly("p")
    perm_q = perm_matrix_poly("q")
    target = mul(perm_p, perm_q)

    coefficient_checks = []
    all_zero = True
    for rho in permutations(range(N)):
        coeff = coeff_m_rho(rho)
        diff = sub(coeff, target)
        is_zero = diff == {}
        all_zero = all_zero and is_zero
        coefficient_checks.append(
            {
                "rho": permutation_name(rho),
                "coefficient_term_count": len(coeff),
                "target_term_count": len(target),
                "difference_is_zero": is_zero,
                "difference_terms": poly_terms(diff),
            }
        )

    weight_checks = []
    common_weight = None
    same_weight = True
    for rho in permutations(range(N)):
        vec = weight_vector_for_m_rho(rho)
        if common_weight is None:
            common_weight = vec
        same_weight = same_weight and vec == common_weight
        weight_checks.append(
            {
                "rho": permutation_name(rho),
                "weight_vector_a1a2a3b1b2b3": list(vec),
                "weight": weight_label(vec),
            }
        )

    cert = {
        "task": "T3_structural_obstruction",
        "tag": "proved-alg",
        "field": "Q",
        "method": "exact integer polynomial identities in the formal entries of P and Q",
        "lemma": {
            "statement": "[M_rho] perm_3(PYQ^T) = perm(P)*perm(Q), independent of rho in S3",
            "all_six_coefficient_identities_verified": all_zero,
            "coefficient_checks": coefficient_checks,
        },
        "toric_weight_check": {
            "all_six_weights_equal": same_weight,
            "common_weight": weight_label(common_weight or tuple()),
            "weight_checks": weight_checks,
        },
        "consequence": (
            "No degeneration perm_3 -> det_3 by a one-parameter torus conjugated "
            "inside GL3xGL3, i.e. by A(t) tensor B(t) with A=U diag(t^a) U^-1 "
            "and B=V diag(t^b) V^-1."
        ),
        "scope": (
            "Specific to conjugated GL3xGL3 tori. This does not apply to T4 "
            "families acting on (s_ij,a_ij) blocks, because those can distinguish "
            "x_ij from x_ji and the equal-coefficient lemma no longer holds."
        ),
        "theorem_proof_tex": theorem_tex(),
        "artifacts": {
            "script": str(script_path),
            "log": str(log_path),
            "certificate": str(cert_path),
        },
    }

    log_lines = [
        "T3 structural obstruction certificate",
        "tag: proved-alg",
        "arithmetic: integer polynomial dictionaries over Q; no floating point",
        "Identity target perm(P)*perm(Q):",
        json.dumps(poly_terms(target), indent=2),
        "Coefficient checks [M_rho]F - perm(P)*perm(Q):",
        json.dumps(coefficient_checks, indent=2),
        "Toric weight checks:",
        json.dumps(weight_checks, indent=2),
        "Scope limitation:",
        cert["scope"],
        "TeX theorem/proof:",
        theorem_tex(),
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
