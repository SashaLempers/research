#!/usr/bin/env python3
"""
Generate the stacked highest-weight raising-operator matrix for

    M = Sym^d(Sym^3 C^9)

at the rectangular SL_9 candidate weight (k^9), k=d/3.

Sparse integer text output:
    first line: rows cols nnz
    following lines: r c val
with r,c 1-indexed.

No floating point arithmetic is used.
The source basis consists of sorted tuples of cubic-monomial indices,
with repetitions preserved.
"""

from collections import defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement
import argparse
import time

N = 9
INNER = 3


def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("--d", type=int, default=6, help="outer symmetric degree d")
    p.add_argument("--out", type=str, default="sparse.txt", help="output sparse text file")
    p.add_argument("--dims-only", action="store_true", help="only print weight-space dimensions")
    return p.parse_args()


args = parse_args()
D = args.d

if D % 3 != 0:
    raise SystemExit("No rectangular SL_9 candidate: d must be divisible by 3.")

K = D // 3
TARGET = tuple([K] * N)

triples = list(combinations_with_replacement(range(N), INNER))
triple_to_idx = {t: i for i, t in enumerate(triples)}

tr_wts = []
for t in triples:
    v = [0] * N
    for a in t:
        v[a] += 1
    tr_wts.append(tuple(v))


def leq(a, b):
    return all(x <= y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


# For recursion, choose a currently positive coordinate i and only use cubic
# monomials containing i. This reduces branching without quotienting the HW space.
cand_by_first_positive_coord = [[] for _ in range(N)]
for idx, t in enumerate(triples):
    for i in set(t):
        cand_by_first_positive_coord[i].append((idx, tr_wts[idx]))


@lru_cache(maxsize=None)
def gen_weight_space_cached(deg):
    """
    Return all multisets of cubic monomials with total multidegree deg.
    Each monomial is a sorted tuple of cubic indices; repetitions are preserved.
    """
    deg = tuple(deg)
    total = sum(deg)

    if total == 0:
        return ((),)
    if total % INNER != 0:
        return tuple()

    try:
        i = next(j for j, x in enumerate(deg) if x > 0)
    except StopIteration:
        return ((),)

    out = set()
    for tidx, w in cand_by_first_positive_coord[i]:
        if leq(w, deg):
            for rest in gen_weight_space_cached(sub(deg, w)):
                out.add(tuple(sorted((tidx,) + rest)))
    return tuple(sorted(out))


def raise_triple(tr, i):
    """Action of E_{i,i+1}: replace one occurrence of i+1 by i."""
    tr = list(tr)
    out = []
    for pos, a in enumerate(tr):
        if a == i + 1:
            nt = tr[:]
            nt[pos] = i
            nt.sort()
            out.append(tuple(nt))
    return out


raise_triple_cache = {
    (tidx, i): tuple(triple_to_idx[rt] for rt in raise_triple(t, i))
    for tidx, t in enumerate(triples)
    for i in range(N - 1)
}


def raise_monomial(mon, i):
    """
    Leibniz action on a product of D cubic monomials.
    Repeated factors are handled by iterating through positions, not by a set.
    """
    coeffs = defaultdict(int)
    mon = list(mon)
    for pos, tidx in enumerate(mon):
        for ridx in raise_triple_cache[(tidx, i)]:
            nm = mon[:]
            nm[pos] = ridx
            nm.sort()
            coeffs[tuple(nm)] += 1
    return coeffs


def neighbor_weight(i):
    nb = list(TARGET)
    nb[i] += 1
    nb[i + 1] -= 1
    return tuple(nb)


def main():
    t0 = time.time()
    print(f"N = {N}")
    print(f"INNER = {INNER}")
    print(f"d = {D}")
    print(f"k = {K}")
    print(f"source target weight = {TARGET}")

    source_basis = list(gen_weight_space_cached(TARGET))
    cols = len(source_basis)
    print(f"source weight dim = {cols}")

    neighbor_bases = []
    row_offsets = []
    rows = 0
    for i in range(N - 1):
        nb = neighbor_weight(i)
        tbasis = list(gen_weight_space_cached(nb))
        neighbor_bases.append(tbasis)
        row_offsets.append(rows)
        rows += len(tbasis)
        print(f"E_{i},{i+1}: target weight {nb}, target dim = {len(tbasis)}")

    if args.dims_only:
        print("dims-only mode: no sparse matrix written")
        print(f"total stacked rows = {rows}")
        print(f"cols = {cols}")
        return

    out_path = args.out
    nnz = 0

    with open(out_path, "w", encoding="utf-8") as f:
        # Placeholder header; overwritten at the end.
        f.write(f"{rows} {cols} 0\n")

        for i in range(N - 1):
            print(f"Building E_{i},{i+1} ...")
            target_index = {m: r for r, m in enumerate(neighbor_bases[i])}
            row_offset = row_offsets[i]

            for c, mon in enumerate(source_basis):
                img = raise_monomial(mon, i)
                for m2, val in img.items():
                    r = target_index.get(m2)
                    if r is not None and val:
                        # 1-indexed sparse output
                        f.write(f"{row_offset + r + 1} {c + 1} {val}\n")
                        nnz += 1

            print(f"  cumulative nnz = {nnz}")

    # Rewrite exact header with nnz. Keep the file flat and Macaulay2-readable.
    with open(out_path, "r+", encoding="utf-8") as f:
        lines = f.readlines()
        f.seek(0)
        f.truncate()
        f.write(f"{rows} {cols} {nnz}\n")
        f.writelines(lines[1:])

    print(f"rows = {rows}")
    print(f"cols = {cols}")
    print(f"nnz = {nnz}")
    print(f"wrote {out_path}")
    print(f"elapsed seconds = {time.time() - t0:.3f}")


if __name__ == "__main__":
    main()
