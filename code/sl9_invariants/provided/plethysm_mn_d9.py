#!/usr/bin/env python3
"""
Exact Murnaghan--Nakayama plethysm check.

Computes:
    < h_D[h_3], s_{(K^9)} >

where K = D/3 and target partition is (K,K,...,K) with 9 parts.

No floating point arithmetic is used.
Tag of the output is only claimed-comp exact-MN unless independently cross-certified.
"""

from fractions import Fraction
from functools import lru_cache
from collections import defaultdict
from math import factorial
import time

D = 9
N = 9
INNER = 3

if D % 3 != 0:
    raise SystemExit("No rectangular SL_9 weight: D must be divisible by 3.")

K = D // 3
TARGET = tuple([K] * N)
TOTAL = D * INNER


def partitions(n, max_part=None):
    if n == 0:
        yield ()
        return
    if max_part is None or max_part > n:
        max_part = n
    for first in range(max_part, 0, -1):
        if n - first == 0:
            yield (first,)
        else:
            for rest in partitions(n - first, min(first, n - first)):
                yield (first,) + rest


def z_value(part):
    counts = defaultdict(int)
    for p in part:
        counts[p] += 1
    z = 1
    for i, m in counts.items():
        z *= (i ** m) * factorial(m)
    return z


def normalize(shape):
    return tuple(x for x in shape if x > 0)


@lru_cache(None)
def cells(shape):
    return frozenset((r, c) for r, row in enumerate(shape) for c in range(row))


@lru_cache(None)
def subpartitions_of_size(shape, remove_k):
    """All partitions mu <= shape with |shape|-|mu| = remove_k."""
    shape = tuple(shape)
    target_size = sum(shape) - remove_k
    if target_size < 0:
        return tuple()

    out = []

    def rec(i, prev, rem, acc):
        if i == len(shape):
            if rem == 0:
                out.append(normalize(tuple(acc)))
            return
        for v in range(min(shape[i], prev, rem), -1, -1):
            acc.append(v)
            rec(i + 1, v, rem - v, acc)
            acc.pop()

    rec(0, 10**9, target_size, [])
    return tuple(sorted(set(out), reverse=True))


def is_connected(cellset):
    if not cellset:
        return False
    start = next(iter(cellset))
    seen = {start}
    stack = [start]
    while stack:
        r, c = stack.pop()
        for nb in ((r + 1, c), (r - 1, c), (r, c + 1), (r, c - 1)):
            if nb in cellset and nb not in seen:
                seen.add(nb)
                stack.append(nb)
    return len(seen) == len(cellset)


def has_2x2(cellset):
    for r, c in cellset:
        if (r + 1, c) in cellset and (r, c + 1) in cellset and (r + 1, c + 1) in cellset:
            return True
    return False


@lru_cache(None)
def rim_hooks(shape, k):
    """Return (remaining_shape, height) for rim hooks of size k."""
    shape = tuple(shape)
    lam_cells = cells(shape)
    out = []
    for mu in subpartitions_of_size(shape, k):
        diff = lam_cells - cells(mu)
        if len(diff) == k and is_connected(diff) and not has_2x2(diff):
            height = len({r for r, c in diff}) - 1
            out.append((mu, height))
    return tuple(out)


@lru_cache(None)
def chi(shape, cycle_type):
    """Irreducible symmetric-group character by Murnaghan--Nakayama."""
    shape = tuple(shape)
    cycle_type = tuple(cycle_type)

    if not cycle_type:
        return 1 if sum(shape) == 0 else 0
    if sum(shape) != sum(cycle_type):
        return 0

    k = cycle_type[0]
    total = 0
    for mu, height in rim_hooks(shape, k):
        total += ((-1) ** height) * chi(mu, cycle_type[1:])
    return total


@lru_cache(None)
def p_j_h_inner_terms(j):
    """
    p_j[h_3] = sum_{mu partition 3} p_{j*mu}/z_mu.
    Returned as dict partition -> Fraction coefficient.
    """
    out = defaultdict(Fraction)
    for mu in partitions(INNER):
        part = tuple(sorted((j * a for a in mu), reverse=True))
        out[part] += Fraction(1, z_value(mu))
    return dict(out)


def multiply_p_terms(A, B):
    C = defaultdict(Fraction)
    for pa, ca in A.items():
        for pb, cb in B.items():
            part = tuple(sorted(pa + pb, reverse=True))
            C[part] += ca * cb
    return dict(C)


def plethysm_hD_h3_p_coeffs(D):
    """
    Expansion of h_D[h_3] in the p-basis:
        h_D[h_3] = sum_rho coeff[rho] p_rho.
    """
    coeffs = defaultdict(Fraction)
    for alpha in partitions(D):
        term = {(): Fraction(1)}
        for j in alpha:
            term = multiply_p_terms(term, p_j_h_inner_terms(j))

        alpha_coeff = Fraction(1, z_value(alpha))
        for rho, c in term.items():
            coeffs[rho] += alpha_coeff * c

    return dict(coeffs)


def scalar_hD_h3_s_target():
    coeffs = plethysm_hD_h3_p_coeffs(D)
    val = Fraction(0)
    for rho, c in coeffs.items():
        val += c * chi(TARGET, rho)
    return val, coeffs


def orthogonality_check():
    total = Fraction(0)
    count = 0
    for rho in partitions(TOTAL):
        cr = chi(TARGET, rho)
        total += Fraction(cr * cr, z_value(rho))
        count += 1
    return total, count


def main():
    t0 = time.time()
    print(f"D = {D}")
    print(f"N = {N}")
    print(f"INNER = {INNER}")
    print(f"target partition/weight = {TARGET}")
    print(f"total degree = {TOTAL}")

    val, coeffs = scalar_hD_h3_s_target()
    print(f"support p-coeff size = {len(coeffs)}")
    print(f"scalar <h_{D}[h_3], s_{TARGET}> = {val}")

    ortho, nparts = orthogonality_check()
    print(f"partitions({TOTAL}) = {nparts}")
    print(f"orthogonality check for chi^{TARGET} = {ortho}")

    if ortho != 1:
        raise SystemExit("ERROR: character orthogonality check failed.")

    print(f"RESULT claimed-comp exact-MN = {val}")
    print(f"elapsed seconds = {time.time() - t0:.3f}")


if __name__ == "__main__":
    main()
