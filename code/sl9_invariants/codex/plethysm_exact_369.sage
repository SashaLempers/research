#!/usr/bin/env sage
"""
Exact Sage plethysm check for the three rectangular coefficients

    <h_d[h_3], s_((d/3)^9)>, d in {3, 6, 9}.

All calculations are over QQ.
"""

Sym = SymmetricFunctions(QQ)
h = Sym.homogeneous()
s = Sym.schur()

for d in (3, 6, 9):
    target = Partition([d // 3] * 9)
    expansion = s(h[d].plethysm(h[3]))
    coefficient = expansion.coefficient(target)
    print(f"d = {d}")
    print(f"target = {tuple(target)}")
    print(f"scalar = {coefficient}")
    assert coefficient == 0

print("RESULT Sage exact plethysm d={3,6,9} = 0")
