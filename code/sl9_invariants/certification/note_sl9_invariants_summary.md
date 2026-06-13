# SL9 invariant vanishing certification note

Date: 2026-06-13

This is a lightweight repository note distilled from the local all-in-one PDF. It intentionally omits large code blocks and unpublished manuscript material.

## Mathematical scope

Let V = C^9 and M_d = Sym^d(Sym^3 V). The algebraic equivalence used in the manuscript patch is:

- if 9 does not divide 3d, then dim M_d^{SL_9} = 0;
- if 3d = 9k, then dim M_d^{SL_9} = < h_d[h_3], s_(k^9) >.

The equivalence is a Proved-Alg statement, separate from the exact coefficient computations.

## Certified values

Exact computations give:

- <h_3[h_3], s_(1^9)> = 0;
- <h_6[h_3], s_(2^9)> = 0;
- <h_9[h_3], s_(3^9)> = 0.

## Tags

- d = 3: qq-cert. The plethystic computation agrees with an independent direct highest-weight kernel computation over QQ.
- d = 6: claimed-comp. MN, Sage, and M2 SchurRings agree, but they are redundant plethystic computations.
- d = 9: claimed-comp. Same reason as d = 6; no direct HW rank computation is claimed.

The combined assertion dim M_d^{SL_9} = 0 for d in {3,6,9} is therefore tagged by its weakest computational component: claimed-comp.

## HW direct check for d = 3

The exact highest-weight matrix check used a 1400 x 280 integer matrix with 2240 nonzero entries. The exact QQ rank is 280 and the nullity is 0.

The sparse matrix itself is deliberately excluded from the repository. Only its SHA-256 certificate is included.

## Repository hygiene

The heavy all-in-one PDF, the patched unpublished manuscript, article PDFs, manuscript sources, source diffs, extracted manuscript text, sparse matrices, and Tectonic build logs are not included in this commit candidate.
