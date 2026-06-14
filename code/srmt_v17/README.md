# Combined SRMT/GCT + Jacobian Homology Lab (v1.7 — certified outputs)

This folder contains **certified output artifacts** from the SRMT/GCT v1.7 pipeline run.

> **Note:** The generator script `srmt_gct_combined_lab.m2` lives in the
> [`srmt-reproducibility`](https://github.com/SashaLempers/srmt-reproducibility) repository
> (at `macaulay2/srmt_gct_combined_lab.m2`). This folder contains only the
> certified outputs and is presented as a **partial certified output bundle**.

## Contents

| Output file | Contents |
|---|---|
| `srmt_gct_results.csv` | Representation table |
| `srmt_gct_report.md` | Markdown report |
| `srmt_gct_table.tex` | LaTeX table |
| `jacobian_pdim_summary.md` | Homology summary |
| `certificates/det_resolution_certificate.m2` | det certificate |
| `certificates/perm_resolution_certificate.m2` | perm certificate |
| `VALIDATION.md` | Validation tiers |
| `COMBINED_SUMMARY.md` | Combined summary |
| `CITATION.cff` | Citation metadata |

## Reproducibility

To reproduce these outputs, run the generator script from `srmt-reproducibility`:

```bash
M2 --script macaulay2/srmt_gct_combined_lab.m2
```
