# Open Problem 31 exact-computation run

Date: 2026-06-14

This directory contains the current reproducibility artifacts for the prompt
requesting an exact-arithmetic attack on whether `det_3 in X_perm`.

Original protected inputs were read only:

- `C:\Users\sashack\Downloads\prompt.txt`
- `C:\Users\sashack\srmt_github\AGENTS.md`
- `C:\Users\sashack\srmt_github\code`

No file in `C:\Users\sashack\srmt_github` was modified.

## Environment

- Windows host Python: 3.12.0.
- SymPy is not installed on the host or Codex bundled Python.
- T0-T4 structural certificates use standalone Python standard library exact
  arithmetic.
- Docker container available with approval: `pensive_einstein`, image
  `srmt-research:latest`.
- In the container: SageMath 10.8 and Macaulay2 1.19.1 are available.

## Artifact layout

- `scripts/`: one standalone script per completed task.
- `logs/`: execution log for each script.
- `certificates/`: JSON certificate for each completed task.
- `SHA256SUMS.txt`: SHA-256 hashes for scripts, logs, and certificates.

## Produced task artifacts

| Task | Tag | Result | Verdict on `det_3 in X_perm` |
|---|---|---|---|
| T0 | proved-alg | Exact Lie-differential ranks: `dim GL9.det3 = 65`, `dim GL9.perm3 = 77`. Hence `perm3 notin X_det` by dimension. | Does not decide `det_3 in X_perm`; it identifies this as the remaining GCT-relevant direction. |
| T1 | proved-alg | Exact expansion verifies the supplied `(d,s,a)` formulas for both `det3` and `perm3`; supports and `det3 +/- perm3` are recorded. | No containment decision. |
| T2 | proved-alg | Row-column torus weights are all equal on the six permutation monomials; diagonal `(d,s,a)` scaling is incompatible by the equation `2*c^3 = 0` with `c != 0`. | Eliminates these poor families only; no containment decision. |
| T3 | proved-alg | Structural obstruction certified: for `F_{P,Q}(Y)=perm_3(PYQ^T)`, all six coefficients `[M_rho]F_{P,Q}` equal `perm(P)*perm(Q)`, and all six toric weights are `a1+a2+a3+b1+b2+b3`. | No degeneration `perm_3 -> det_3` by conjugated `GL_3 x GL_3` tori. This closes T3 only. |
| T4 | proved-alg | Structural obstruction certified for block-diagonal `H_d direct_sum H_12 direct_sum H_13 direct_sum H_23` in the `(d,s,a)` basis. Pair weights force diagonal/anti-diagonal pair blocks; only two orientations survive; both give `2*c^2=0` with `c != 0`. | No degeneration `perm_3 -> det_3` in this T4 block family. This does not close general `GL_9`. |
| T4 search | comp-obs | Historical checkpoint engine searched cases `1..1000`; no exact match; one same-support quasi-match at the identity. | Superseded by the T4 structural obstruction for the block family. |
| T6 d=2..5 | claimed-comp | Sage direct expansions `s(h[d].plethysm(h[3]))`: support sizes `2,5,12,28`; for `d=3`, rectangular coefficient `(1^9)` is `0`; for `d=2,4,5`, no `(k^9)` target exists. | Plethystic data only; not a containment decision. |

## Current scientific status

No degeneration `perm3 -> det3` has been certified in this run.  The T3
conjugated-`GL_3 x GL_3` torus route and the T4 block-diagonal `(d,s,a)` route
are now closed by structural `proved-alg` obstructions, each with its stated
scope.

No representation-theoretic obstruction separating `det3` from `X_perm` has
been constructed. The current status after these scoped closures is therefore:

`det_3 in X_perm` remains Open within this run.

## Next tasks

The prompt priority after the T3 and T4 structural closures is:

1. Do not relaunch T4; the block-diagonal T4 family is closed by the structural certificate.
2. Continue Route B. T6 for `d=2,3,4,5` has been run by direct Sage expansion.
3. For T6 at `d=12`, do not expand `h_12[h_3]`; use targeted Molien-Weyl / character projection and the Macaulay2 Schur-rings route, then compare.
4. Continue later tasks only with careful tags: one plethystic engine is `claimed-comp`, not `qq-cert`.

Sage and Macaulay2 are available in Docker, so the exact plethysm/rank parts can
be attempted in the container. For T6, direct Schur expansion has been used for
`d=2,3,4,5`; the `d=12` coefficient of `s_(4^9)` must not be computed by
expanding `s(h[12].plethysm(h[3]))`. It must use targeted Molien-Weyl/character
projection and the Macaulay2 Schur-rings route, then compare the two.

Large exhaustive searches should be checkpointed and tagged carefully as
`claimed-comp` or `comp-obs` unless they produce a hand-checkable exact
certificate.
