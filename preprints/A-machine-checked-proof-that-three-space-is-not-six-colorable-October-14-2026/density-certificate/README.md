# Certificate for m₁(ℝ³) ≤ 0.1485113

`python3 verify_cert.py cert_final.json` checks in ball arithmetic (python-flint) that the 23 correlation-polytope cuts and
multipliers in `cert_final.json` give m₁(ℝ³) ≤ 0.14851123: the cut inequalities by exact enumeration, G(t) ≤ μ on Taylor
cells for t ∈ (0, 2806], and |sin x / x| ≤ 1/x beyond. `python3 xcheck.py cert_final.json` is an independent
re-implementation written from scratch. `cert_onecut.json` is the single-cut certificate m₁(ℝ³) ≤ 0.158035 < 1/6.
`m1lib.py` holds shared helpers.
