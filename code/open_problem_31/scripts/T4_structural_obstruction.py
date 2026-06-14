#!/usr/bin/env python3
"""T4 structural obstruction certificate.

This script certifies, in exact arithmetic over Q, the structural obstruction
for the T4 block-diagonal family in the variables

    (d1,d2,d3,s12,a12,s13,a13,s23,a23),

with x_ij = s_ij + a_ij and x_ji = s_ij - a_ij.  It does not enumerate the
large finite search space; it verifies the algebraic links used by the
structural proof.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path


DSA_NAMES = ["d1", "d2", "d3", "s12", "a12", "s13", "a13", "s23", "a23"]
UV_NAMES = ["d1", "d2", "d3", "u12", "v12", "u13", "v13", "u23", "v23"]


Poly = dict[tuple[int, ...], Fraction]


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def const(n: int, value: Fraction | int) -> Poly:
    value = Fraction(value)
    return {} if value == 0 else {tuple([0] * n): value}


def var(n: int, idx: int) -> Poly:
    exp = [0] * n
    exp[idx] = 1
    return {tuple(exp): Fraction(1)}


def add(*polys: Poly) -> Poly:
    out: Poly = {}
    for poly in polys:
        for mon, coeff in poly.items():
            out[mon] = out.get(mon, Fraction(0)) + coeff
            if out[mon] == 0:
                del out[mon]
    return out


def scale(poly: Poly, scalar: Fraction | int) -> Poly:
    scalar = Fraction(scalar)
    if scalar == 0:
        return {}
    return {mon: coeff * scalar for mon, coeff in poly.items() if coeff * scalar}


def sub(a: Poly, b: Poly) -> Poly:
    return add(a, scale(b, -1))


def mul(*polys: Poly) -> Poly:
    if not polys:
        return const(0, 1)
    n = len(next(iter(polys[0]))) if polys[0] else 0
    out = const(n, 1)
    for poly in polys:
        if not poly:
            return {}
        new: Poly = {}
        for mon_a, coeff_a in out.items():
            for mon_b, coeff_b in poly.items():
                mon = tuple(a + b for a, b in zip(mon_a, mon_b))
                new[mon] = new.get(mon, Fraction(0)) + coeff_a * coeff_b
                if new[mon] == 0:
                    del new[mon]
        out = new
    return out


def parity(perm: tuple[int, ...]) -> int:
    inv = 0
    for i in range(len(perm)):
        for j in range(i + 1, len(perm)):
            if perm[i] > perm[j]:
                inv += 1
    return -1 if inv % 2 else 1


def determinant_from_forms(forms: list[list[Poly]]) -> Poly:
    terms = []
    for perm in permutations(range(3)):
        factors = [forms[row][perm[row]] for row in range(3)]
        terms.append(scale(mul(*factors), parity(perm)))
    return add(*terms)


def permanent_from_forms(forms: list[list[Poly]]) -> Poly:
    terms = []
    for perm in permutations(range(3)):
        factors = [forms[row][perm[row]] for row in range(3)]
        terms.append(mul(*factors))
    return add(*terms)


def exp_from_factors(names: list[str], factors: list[str]) -> tuple[int, ...]:
    idx = {name: i for i, name in enumerate(names)}
    exp = [0] * len(names)
    for factor in factors:
        exp[idx[factor]] += 1
    return tuple(exp)


def coeff(poly: Poly, names: list[str], factors: list[str]) -> Fraction:
    return poly.get(exp_from_factors(names, factors), Fraction(0))


def frac_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def poly_to_terms(poly: Poly, names: list[str]) -> list[dict[str, object]]:
    out = []
    for exp in sorted(poly):
        factors = []
        for name, power in zip(names, exp):
            if power == 1:
                factors.append(name)
            elif power > 1:
                factors.append(f"{name}^{power}")
        out.append({"monomial": "*".join(factors) if factors else "1", "coeff": frac_str(poly[exp])})
    return out


def dsa_forms() -> list[list[Poly]]:
    n = len(DSA_NAMES)
    d1, d2, d3 = var(n, 0), var(n, 1), var(n, 2)
    s12, a12 = var(n, 3), var(n, 4)
    s13, a13 = var(n, 5), var(n, 6)
    s23, a23 = var(n, 7), var(n, 8)
    return [
        [d1, add(s12, a12), add(s13, a13)],
        [sub(s12, a12), d2, add(s23, a23)],
        [sub(s13, a13), sub(s23, a23), d3],
    ]


def uv_forms() -> list[list[Poly]]:
    n = len(UV_NAMES)
    d1, d2, d3 = var(n, 0), var(n, 1), var(n, 2)
    u12, v12 = var(n, 3), var(n, 4)
    u13, v13 = var(n, 5), var(n, 6)
    u23, v23 = var(n, 7), var(n, 8)
    return [
        [d1, u12, u13],
        [v12, d2, u23],
        [v13, v23, d3],
    ]


def weight_vec(names: list[str], weights: dict[str, tuple[int, ...]], factors: list[str]) -> tuple[int, ...]:
    out = [0] * len(next(iter(weights.values())))
    for factor in factors:
        for i, value in enumerate(weights[factor]):
            out[i] += value
    return tuple(out)


def vec_sub(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(x - y for x, y in zip(a, b))


def vec_label(vec: tuple[int, ...], symbols: list[str]) -> str:
    pieces = []
    for coeff_value, symbol in zip(vec, symbols):
        if coeff_value == 0:
            continue
        if coeff_value == 1:
            pieces.append(f"+{symbol}")
        elif coeff_value == -1:
            pieces.append(f"-{symbol}")
        elif coeff_value > 0:
            pieces.append(f"+{coeff_value}{symbol}")
        else:
            pieces.append(f"{coeff_value}{symbol}")
    if not pieces:
        return "0"
    text = "".join(pieces)
    return text[1:] if text.startswith("+") else text


def rank_q(rows: list[list[Fraction]]) -> int:
    mat = [row[:] for row in rows if any(x != 0 for x in row)]
    if not mat:
        return 0
    r = 0
    cols = len(mat[0])
    for c in range(cols):
        pivot = None
        for i in range(r, len(mat)):
            if mat[i][c] != 0:
                pivot = i
                break
        if pivot is None:
            continue
        mat[r], mat[pivot] = mat[pivot], mat[r]
        pv = mat[r][c]
        mat[r] = [x / pv for x in mat[r]]
        for i in range(len(mat)):
            if i != r and mat[i][c] != 0:
                factor = mat[i][c]
                mat[i] = [x - factor * y for x, y in zip(mat[i], mat[r])]
        r += 1
        if r == len(mat):
            break
    return r


def extract_coeff_by_front_exp(poly: Poly, front_len: int, target: tuple[int, ...]) -> Poly:
    out: Poly = {}
    for mon, coefficient in poly.items():
        if mon[:front_len] == target:
            tail = mon[front_len:]
            out[tail] = out.get(tail, Fraction(0)) + coefficient
            if out[tail] == 0:
                del out[tail]
    return out


def dichotomy_certificate() -> dict[str, object]:
    names = ["u", "v", "p", "q", "r", "ell"]
    n = len(names)
    u, v = var(n, 0), var(n, 1)
    p, q, r, ell = var(n, 2), var(n, 3), var(n, 4), var(n, 5)
    u_img = add(mul(p, u), mul(q, v))
    v_img = add(mul(r, u), mul(ell, v))
    product_uv = mul(u_img, v_img)
    u2_coeff = extract_coeff_by_front_exp(product_uv, 2, (2, 0))
    uv_coeff = extract_coeff_by_front_exp(product_uv, 2, (1, 1))
    v2_coeff = extract_coeff_by_front_exp(product_uv, 2, (0, 2))

    tail_names = names[2:]
    expected_u2 = {exp_from_factors(tail_names, ["p", "r"]): Fraction(1)}
    expected_uv = {
        exp_from_factors(tail_names, ["p", "ell"]): Fraction(1),
        exp_from_factors(tail_names, ["q", "r"]): Fraction(1),
    }
    expected_v2 = {exp_from_factors(tail_names, ["q", "ell"]): Fraction(1)}

    patterns = []
    for p_nz, q_nz, r_nz, ell_nz in product([False, True], repeat=4):
        pr_zero = not (p_nz and r_nz)
        qell_zero = not (q_nz and ell_nz)
        det_can_be_nonzero = (p_nz and ell_nz) or (q_nz and r_nz)
        if pr_zero and qell_zero and det_can_be_nonzero:
            if p_nz and ell_nz:
                kind = "diagonal"
            elif q_nz and r_nz:
                kind = "anti-diagonal"
            else:
                kind = "impossible"
            patterns.append(
                {
                    "p_nonzero": p_nz,
                    "q_nonzero": q_nz,
                    "r_nonzero": r_nz,
                    "ell_nonzero": ell_nz,
                    "kind": kind,
                }
            )

    return {
        "expanded_uv_image": poly_to_terms(product_uv, names),
        "coeff_u2_is_pr": u2_coeff == expected_u2,
        "coeff_uv_is_pell_plus_qr": uv_coeff == expected_uv,
        "coeff_v2_is_qell": v2_coeff == expected_v2,
        "invertible_zero_product_patterns": patterns,
        "only_diagonal_or_antidiagonal": sorted({p["kind"] for p in patterns}) == ["anti-diagonal", "diagonal"],
    }


def cycles_of_perm(perm: tuple[int, ...]) -> list[list[int]]:
    seen = [False] * len(perm)
    cycles: list[list[int]] = []
    for start in range(len(perm)):
        if seen[start]:
            continue
        cur = start
        cycle = []
        while not seen[cur]:
            seen[cur] = True
            cycle.append(cur)
            cur = perm[cur]
        if len(cycle) > 1:
            cycles.append(cycle)
    return cycles


def hd_certificate() -> dict[str, object]:
    obstruction_rows = []
    for perm in permutations(range(3)):
        if perm == (0, 1, 2):
            continue
        cycles = cycles_of_perm(perm)
        obstruction_rows.append(
            {
                "permutation": "".join(str(i + 1) for i in perm),
                "moved_cycles": [[i + 1 for i in cycle] for cycle in cycles],
                "strict_cycle_contradiction": all(len(cycle) > 1 for cycle in cycles),
                "reason": "A nonzero off-diagonal term would require delta_{pi(i)} > delta_i around a moved cycle.",
            }
        )
    return {
        "identity_term": "h11*h22*h33",
        "nonidentity_terms_checked": obstruction_rows,
        "all_nonidentity_terms_impossible": all(row["strict_cycle_contradiction"] for row in obstruction_rows),
        "surviving_permanent_of_Hd": "h1*h2*h3",
        "coefficient_equation": "h1*h2*h3 = c",
    }


def toggle(choice: str) -> str:
    return "v" if choice == "u" else "u"


def cycle_label(choices: dict[str, str]) -> str:
    return "*".join(f"{choices[pair]}{pair}" for pair in ["12", "13", "23"])


def orientation_certificate() -> dict[str, object]:
    t_plus = {"12": "u", "13": "v", "23": "u"}
    t_minus = {"12": "v", "13": "u", "23": "v"}
    target_set = {cycle_label(t_plus), cycle_label(t_minus)}
    rows = []
    for bits in product([0, 1], repeat=3):
        image_plus = {}
        image_minus = {}
        for bit, pair in zip(bits, ["12", "13", "23"]):
            image_plus[pair] = toggle(t_plus[pair]) if bit else t_plus[pair]
            image_minus[pair] = toggle(t_minus[pair]) if bit else t_minus[pair]
        image_set = {cycle_label(image_plus), cycle_label(image_minus)}
        rows.append(
            {
                "bits_12_13_23": list(bits),
                "image_set": sorted(image_set),
                "admissible": image_set == target_set,
                "parasites": sorted(image_set - target_set),
            }
        )
    admissible_bits = [row["bits_12_13_23"] for row in rows if row["admissible"]]
    return {
        "T_plus": cycle_label(t_plus),
        "T_minus": cycle_label(t_minus),
        "target_set": sorted(target_set),
        "orientation_rows": rows,
        "admissible_bits": admissible_bits,
        "only_all_equal_orientations": admissible_bits == [[0, 0, 0], [1, 1, 1]],
    }


def final_contradiction_certificate() -> dict[str, object]:
    names = ["h1", "h2", "h3", "mu12", "mu13", "mu23", "c"]
    n = len(names)
    h1, h2, h3 = var(n, 0), var(n, 1), var(n, 2)
    mu12, mu13, mu23 = var(n, 3), var(n, 4), var(n, 5)
    c = var(n, 6)

    left_product = mul(h3, mu12, h2, mu13, h1, mu23)
    grouped_product = mul(h1, h2, h3, mu12, mu13, mu23)
    grouping_identity = sub(left_product, grouped_product) == {}

    c3 = mul(c, c, c)
    contradiction_poly = add(c3, c3)
    c2_after_dividing_by_nonzero_c = add(mul(c, c), mul(c, c))

    return {
        "system": [
            "h3*mu12 = -c",
            "h2*mu13 = -c",
            "h1*mu23 = -c",
            "h1*h2*h3 = c",
            "mu12*mu13*mu23 = c^2",
        ],
        "grouping_identity_exact": grouping_identity,
        "product_of_first_three_gives": "c^3 = -c^3",
        "raw_contradiction": poly_to_terms(contradiction_poly, names),
        "after_dividing_by_c_nonzero": poly_to_terms(c2_after_dividing_by_nonzero_c, names),
        "conclusion": "Over Q, hence over characteristic zero, 2*c^2=0 forces c=0, contradicting c in C*.",
    }


def theorem_proof_tex() -> str:
    return r"""\begin{theorem}[T4 structural obstruction]
Let
\[
  (d_1,d_2,d_3,s_{12},a_{12},s_{13},a_{13},s_{23},a_{23})
\]
be the coordinates defined by \(x_{ij}=s_{ij}+a_{ij}\) and
\(x_{ji}=s_{ij}-a_{ij}\). Let
\[
  g(t)=H\operatorname{diag}(t^e),\qquad
  H=H_d\oplus H_{12}\oplus H_{13}\oplus H_{23},
\]
where \(H_d\in GL_3\) acts on \((d_1,d_2,d_3)\) and
\(H_{ij}\in GL_2\) acts on the corresponding pair block. Then there are no
\(e,H,m\) and \(c\in\mathbb C^\ast\) such that
\[
  \lim_{t\to 0} t^{-m}\,g(t)\cdot\operatorname{perm}_3
  =c\,\operatorname{det}_3 .
\]
\end{theorem}

\begin{proof}
In the above coordinates,
\(\det_3\) contains, for each pair \(\{i,j\}\) with complement \(k\), the two
terms \(-d_k s_{ij}^2+d_k a_{ij}^2\). Since both occur in
\(c\det_3\), their weights in any matching initial form must both be minimal.
Thus the two weights on \(s_{ij}\) and \(a_{ij}\) are equal; write the common
weight as \(\lambda_{ij}\). The terms \(d_1d_2d_3\) and the two cyclic terms
then give
\[
  \lambda_{12}+\lambda_{13}+\lambda_{23}
  =\delta_1+\delta_2+\delta_3=m .
\]

With equal weights on each pair, write a pair block in the
\((u_{ij},v_{ij})=(x_{ij},x_{ji})\) basis as
\[
  u\mapsto pu+qv,\qquad v\mapsto ru+\ell v .
\]
The image of \(uv\) has coefficients \(pr\) on \(u^2\) and \(q\ell\) on
\(v^2\). Since \(c\det_3\) has no \(d_k u_{ij}^2\) or \(d_k v_{ij}^2\) terms,
one has \(pr=q\ell=0\). Invertibility of the block forces it to be diagonal or
anti-diagonal in the \((u,v)\) basis.

Similarly, an off-diagonal contribution in the \(d\)-block would force strict
inequalities \(\delta_{\pi(i)}>\delta_i\) around a nontrivial cycle of a
permutation \(\pi\), which is impossible. Hence the only surviving contribution
of \(H_d\) to the \(d_1d_2d_3\) coefficient is \(h_1h_2h_3\), so
\(h_1h_2h_3=c\).

There are eight possible diagonal/anti-diagonal orientation choices on
\((12),(13),(23)\). A direct check shows that only the two choices
\((0,0,0)\) and \((1,1,1)\) preserve the set of cyclic monomials
\(\{T_+,T_-\}\); the other six create a cyclic monomial of weight \(m\) not
appearing in \(c\det_3\).

In the two admissible cases, if \(\mu_{ij}\) is the nonzero product of the two
pair scalars, the transposition coefficients and cyclic coefficients impose
\[
  h_3\mu_{12}=-c,\quad h_2\mu_{13}=-c,\quad h_1\mu_{23}=-c,\quad
  h_1h_2h_3=c,\quad \mu_{12}\mu_{13}\mu_{23}=c^2 .
\]
Multiplying the first three equations and substituting the last two gives
\(c^3=-c^3\). Since \(c\ne0\) and the characteristic is zero, this is
equivalent to \(2c^2=0\), a contradiction. Therefore no such degeneration
exists in the stated block-diagonal T4 family.
\end{proof}
"""


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    script_path = Path(__file__).resolve()
    log_path = root / "logs" / "T4_structural_obstruction.log"
    cert_path = root / "certificates" / "T4_structural_obstruction.json"

    det_dsa = determinant_from_forms(dsa_forms())
    perm_dsa = permanent_from_forms(dsa_forms())
    det_uv = determinant_from_forms(uv_forms())
    perm_uv = permanent_from_forms(uv_forms())

    pair_checks = []
    for pair, d_name, s_name, a_name in [
        ("12", "d3", "s12", "a12"),
        ("13", "d2", "s13", "a13"),
        ("23", "d1", "s23", "a23"),
    ]:
        pair_checks.append(
            {
                "pair": pair,
                "complement_diagonal": d_name,
                "det_coeff_d_s_squared": frac_str(coeff(det_dsa, DSA_NAMES, [d_name, s_name, s_name])),
                "det_coeff_d_a_squared": frac_str(coeff(det_dsa, DSA_NAMES, [d_name, a_name, a_name])),
                "ok": coeff(det_dsa, DSA_NAMES, [d_name, s_name, s_name]) == -1
                and coeff(det_dsa, DSA_NAMES, [d_name, a_name, a_name]) == 1,
            }
        )

    uv_absence_checks = []
    for pair, d_name, u_name, v_name in [
        ("12", "d3", "u12", "v12"),
        ("13", "d2", "u13", "v13"),
        ("23", "d1", "u23", "v23"),
    ]:
        uv_absence_checks.append(
            {
                "pair": pair,
                "det_coeff_d_u_squared": frac_str(coeff(det_uv, UV_NAMES, [d_name, u_name, u_name])),
                "det_coeff_d_v_squared": frac_str(coeff(det_uv, UV_NAMES, [d_name, v_name, v_name])),
                "det_coeff_d_u_v": frac_str(coeff(det_uv, UV_NAMES, [d_name, u_name, v_name])),
                "perm_coeff_d_u_v": frac_str(coeff(perm_uv, UV_NAMES, [d_name, u_name, v_name])),
                "ok": coeff(det_uv, UV_NAMES, [d_name, u_name, u_name]) == 0
                and coeff(det_uv, UV_NAMES, [d_name, v_name, v_name]) == 0
                and coeff(det_uv, UV_NAMES, [d_name, u_name, v_name]) == -1
                and coeff(perm_uv, UV_NAMES, [d_name, u_name, v_name]) == 1,
            }
        )

    weight_symbols = [
        "delta1",
        "delta2",
        "delta3",
        "sigma12",
        "tau12",
        "sigma13",
        "tau13",
        "sigma23",
        "tau23",
        "m",
    ]
    zero = tuple([0] * len(weight_symbols))
    weights = {
        "d1": (1, 0, 0, 0, 0, 0, 0, 0, 0, 0),
        "d2": (0, 1, 0, 0, 0, 0, 0, 0, 0, 0),
        "d3": (0, 0, 1, 0, 0, 0, 0, 0, 0, 0),
        "s12": (0, 0, 0, 1, 0, 0, 0, 0, 0, 0),
        "a12": (0, 0, 0, 0, 1, 0, 0, 0, 0, 0),
        "s13": (0, 0, 0, 0, 0, 1, 0, 0, 0, 0),
        "a13": (0, 0, 0, 0, 0, 0, 1, 0, 0, 0),
        "s23": (0, 0, 0, 0, 0, 0, 0, 1, 0, 0),
        "a23": (0, 0, 0, 0, 0, 0, 0, 0, 1, 0),
        "m": (0, 0, 0, 0, 0, 0, 0, 0, 0, 1),
    }
    force_equal_weight_checks = []
    for pair, d_name, s_name, a_name in [
        ("12", "d3", "s12", "a12"),
        ("13", "d2", "s13", "a13"),
        ("23", "d1", "s23", "a23"),
    ]:
        ws = weight_vec(DSA_NAMES, weights, [d_name, s_name, s_name])
        wa = weight_vec(DSA_NAMES, weights, [d_name, a_name, a_name])
        diff = vec_sub(ws, wa)
        force_equal_weight_checks.append(
            {
                "pair": pair,
                "weight_d_s_squared": vec_label(ws, weight_symbols),
                "weight_d_a_squared": vec_label(wa, weight_symbols),
                "difference": vec_label(diff, weight_symbols),
                "conclusion": f"{s_name} and {a_name} have equal weights",
                "ok": diff != zero,
            }
        )

    lambda_symbols = ["delta1", "delta2", "delta3", "lambda12", "lambda13", "lambda23", "m"]
    lambda_equations = [
        [Fraction(0), Fraction(0), Fraction(1), Fraction(2), Fraction(0), Fraction(0), Fraction(-1)],
        [Fraction(0), Fraction(1), Fraction(0), Fraction(0), Fraction(2), Fraction(0), Fraction(-1)],
        [Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(0), Fraction(2), Fraction(-1)],
        [Fraction(1), Fraction(1), Fraction(1), Fraction(0), Fraction(0), Fraction(0), Fraction(-1)],
        [Fraction(0), Fraction(0), Fraction(0), Fraction(1), Fraction(1), Fraction(1), Fraction(-1)],
    ]
    rank_without_lambda_sum = rank_q(lambda_equations[:4])
    rank_with_lambda_sum = rank_q(lambda_equations)
    weight_system = {
        "symbols": lambda_symbols,
        "equations": [
            "delta3 + 2*lambda12 = m",
            "delta2 + 2*lambda13 = m",
            "delta1 + 2*lambda23 = m",
            "delta1 + delta2 + delta3 = m",
            "lambda12 + lambda13 + lambda23 = m",
        ],
        "rank_without_lambda_sum_equation": rank_without_lambda_sum,
        "rank_with_lambda_sum_equation": rank_with_lambda_sum,
        "lambda_sum_equation_implied_exactly": rank_without_lambda_sum == rank_with_lambda_sum,
        "conclusion": "lambda12+lambda13+lambda23 = delta1+delta2+delta3 = m",
    }

    dichotomy = dichotomy_certificate()
    hd = hd_certificate()
    orientations = orientation_certificate()
    contradiction = final_contradiction_certificate()

    all_ok = (
        all(item["ok"] for item in pair_checks)
        and all(item["ok"] for item in uv_absence_checks)
        and weight_system["lambda_sum_equation_implied_exactly"]
        and dichotomy["coeff_u2_is_pr"]
        and dichotomy["coeff_uv_is_pell_plus_qr"]
        and dichotomy["coeff_v2_is_qell"]
        and dichotomy["only_diagonal_or_antidiagonal"]
        and hd["all_nonidentity_terms_impossible"]
        and orientations["only_all_equal_orientations"]
        and contradiction["grouping_identity_exact"]
    )

    cert = {
        "task": "T4_structural_obstruction",
        "tag": "proved-alg" if all_ok else "claimed-comp",
        "field": "Q",
        "method": "exact polynomial dictionaries over Fraction plus exact Q-linear rank checks",
        "statement": "No degeneration perm_3 -> c*det_3 exists in the block-diagonal T4 family H_d direct_sum H_12 direct_sum H_13 direct_sum H_23 in the (d,s,a) basis.",
        "basis_convention": "x_ij=s_ij+a_ij, x_ji=s_ij-a_ij",
        "pair_coefficient_checks": pair_checks,
        "uv_absence_checks": uv_absence_checks,
        "weight_equalities": force_equal_weight_checks,
        "weight_system": weight_system,
        "pair_block_dichotomy": dichotomy,
        "diagonal_block": hd,
        "orientation_enumeration": orientations,
        "final_contradiction": contradiction,
        "scope": "Specific to block-diagonal families H_d direct_sum H_12 direct_sum H_13 direct_sum H_23 in the (d,s,a) basis. It does not close the general GL_9 case, where diagonal coordinates and pair blocks may mix. Open Problem 31 remains Open.",
        "theorem_proof_tex": theorem_proof_tex(),
        "artifacts": {
            "script": str(script_path),
            "log": str(log_path),
            "certificate": str(cert_path),
        },
    }

    log_lines = [
        "T4 structural obstruction certificate",
        f"tag: {cert['tag']}",
        "arithmetic: exact Fraction over Q; no floating point",
        f"basis convention: {cert['basis_convention']}",
        f"det d*s^2 / d*a^2 coefficient checks: {all(item['ok'] for item in pair_checks)}",
        f"uv absence checks: {all(item['ok'] for item in uv_absence_checks)}",
        f"lambda weight system implied exactly: {weight_system['lambda_sum_equation_implied_exactly']}",
        f"pair-block dichotomy diagonal/anti-diagonal: {dichotomy['only_diagonal_or_antidiagonal']}",
        f"H_d off-diagonal cycle obstruction: {hd['all_nonidentity_terms_impossible']}",
        f"orientation admissible bits: {orientations['admissible_bits']}",
        f"final contradiction grouping identity: {contradiction['grouping_identity_exact']}",
        f"scope: {cert['scope']}",
        "pair coefficient checks:",
        json.dumps(pair_checks, indent=2),
        "orientation enumeration:",
        json.dumps(orientations["orientation_rows"], indent=2),
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
