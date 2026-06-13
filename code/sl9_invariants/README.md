# SL9 invariant vanishing reproducibility bundle

This folder contains source-level reproducibility material for the exact checks of scalar SL9-invariant vanishing in degrees d = 3, 6, 9 for Sym^d(Sym^3 C^9).

## Layout

- `provided/`: scripts or notes supplied as inputs for the certification run.
- `codex/`: small scripts created by Codex during the certification run.
- `logs_light/`: lightweight exact-arithmetic logs, copied as `.txt` so repository-wide `*.log` ignore rules remain effective.
- `certification/`: certification note and SHA-256 certificates for scripts and lightweight artifacts.

## Status summary

- d = 3: `qq-cert`, because the plethystic computation and the independent direct highest-weight kernel computation agree.
- d = 6: `claimed-comp`, because MN, Sage, and Macaulay2 SchurRings are redundant plethystic engines rather than independent mathematical methods.
- d = 9: `claimed-comp`, same reason as d = 6. No direct highest-weight rank computation is claimed for d = 9.

All certified arithmetic is exact over QQ. No floating-point arithmetic is used for certified statements.

## Deliberately excluded

The unpublished manuscript source/PDF, manuscript diffs, build products, extracted manuscript text, sparse matrices, and heavy build logs are deliberately not included in this tracked bundle.
