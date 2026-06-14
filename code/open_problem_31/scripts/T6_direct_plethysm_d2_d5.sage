#!/usr/bin/env sage
"""
T6 direct Sage plethysm for d = 2, 3, 4, 5 only.

This script intentionally does not compute d = 12.  The d = 12 rectangular
coefficient must be handled by targeted Molien-Weyl / Schur-rings methods, not
by expanding h_12[h_3].
"""

import json
import time

started = time.time()

Sym = SymmetricFunctions(QQ)
h = Sym.homogeneous()
s = Sym.schur()


def partition_list(partition):
    return [int(x) for x in partition]


def coefficient_string(value):
    return str(value)


def sorted_schur_terms(expansion):
    coeffs = expansion.monomial_coefficients()
    rows = []
    for partition, coefficient in coeffs.items():
        rows.append(
            {
                "partition": partition_list(partition),
                "coefficient": coefficient_string(coefficient),
            }
        )
    rows.sort(key=lambda row: row["partition"], reverse=True)
    return rows


results = []
for d in [2, 3, 4, 5]:
    t0 = time.time()
    expansion = s(h[d].plethysm(h[3]))
    terms = sorted_schur_terms(expansion)
    rectangular = {
        "applicable": False,
        "reason": "3*d is not divisible by 9, so no rectangular (k^9) SL9-invariant target exists.",
        "target": None,
        "coefficient": None,
    }
    if (3 * d) % 9 == 0:
        k = (3 * d) // 9
        target = Partition([k] * 9)
        rectangular = {
            "applicable": True,
            "reason": "3*d = 9*k, so Theorem 6.1 reduces the SL9 invariant multiplicity to this rectangular coefficient.",
            "target": partition_list(target),
            "coefficient": coefficient_string(expansion.coefficient(target)),
        }
    results.append(
        {
            "d": int(d),
            "total_degree": int(3 * d),
            "support_size": int(len(terms)),
            "rectangular_coefficient": rectangular,
            "schur_expansion_terms": terms,
            "elapsed_seconds": float(time.time() - t0),
        }
    )

certificate = {
    "task": "T6_direct_plethysm_d2_d5",
    "tag": "claimed-comp",
    "field": "QQ",
    "engine": "SageMath",
    "method": "direct Schur expansion s(h[d].plethysm(h[3])) for d=2,3,4,5",
    "degrees": [int(d) for d in [2, 3, 4, 5]],
    "forbidden_degree_12_expansion": "not executed",
    "results": results,
    "elapsed_seconds": float(time.time() - started),
    "limitations": "Single exact plethystic engine. Per AGENTS.md this is not qq-cert by itself.",
}

print("T6 direct Sage plethysm d=2,3,4,5")
print("tag: claimed-comp")
print("field: QQ")
print("method: s(h[d].plethysm(h[3])) in the Schur basis")
for row in results:
    rect = row["rectangular_coefficient"]
    if rect["applicable"]:
        rect_msg = "target={} coefficient={}".format(rect["target"], rect["coefficient"])
    else:
        rect_msg = rect["reason"]
    print("d={} support_size={} rectangular={}".format(row["d"], row["support_size"], rect_msg))
print("d=12 direct expansion: NOT EXECUTED")
print("JSON_CERT_BEGIN")
print(json.dumps(certificate, indent=2, sort_keys=True))
print("JSON_CERT_END")
