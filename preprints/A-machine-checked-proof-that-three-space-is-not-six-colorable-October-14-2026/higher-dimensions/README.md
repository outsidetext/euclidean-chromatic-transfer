# Density certificates in dimensions 4, 6, 7, 8, 10

`verify_rd.py cert_dN_final.json` checks, in ball arithmetic (python-flint), a certificate for m₁(ℝᴺ) ≤ μ built from
Davies's derivative constraints (arXiv:2610.12301, Lemma 9.2) plus triangle / hypermetric correlation-polytope cuts:
G(0) + 1 ≤ μ and G(t) ≤ μ for all t > 0 (Taylor cells on (0, L], Hankel tail bound DLMF §10.17(iii) beyond).
`check_float.py` is an independent floating-point re-check of the same inequalities.

| file | bound | χ ≥ |
|---|---|---|
| cert_d4_v2_final.json | m₁(ℝ⁴) ≤ 0.0901868 | 12 |
| cert_d6_final.json | m₁(ℝ⁶) ≤ 0.0182084 | 55 |
| cert_d7_final.json | m₁(ℝ⁷) ≤ 0.0091408 | 110 |
| cert_d8_final.json | m₁(ℝ⁸) ≤ 0.0050689 | 198 |
| cert_d10_final.json | m₁(ℝ¹⁰) ≤ 0.0013170 | 760 |
