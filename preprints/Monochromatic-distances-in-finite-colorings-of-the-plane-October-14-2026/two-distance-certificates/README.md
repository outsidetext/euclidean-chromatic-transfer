# Two-distance certificates

`interval_cert.py target dlo dhi` certifies χ(ℝ², {1, d}) ≥ target for all algebraic d ∈ [dlo, dhi] via
h_d(t) = 1 + a J₀(t) + b J₀(d t) ≥ 0, uniformly in d and t, with 1 + a + b > target − 1. The `cover_*.npy` files store
the interval covers; `c*.log` and `cert7_7_10000.log` are the runs.

| command | statement |
|---|---|
| `python3 interval_cert.py 7 1.77 1.92` | χ ≥ 7 for d ∈ [1.77, 1.92] |
| `python3 interval_cert.py 7 7 10000` | χ ≥ 7 for d ∈ [7, 10⁴] |
| `python3 interval_cert.py 8 16 10000` | χ ≥ 8 for d ∈ [16, 10⁴] |
| `python3 interval_cert.py 9 40 10000` | χ ≥ 9 for d ∈ [40, 10⁴] |
| `python3 interval_cert.py 10 150 10000` | χ ≥ 10 for d ∈ [150, 10⁴] |

Larger d are handled analytically in the paper. `independent-arb-check/` re-verifies the certificates from scratch with
every Bessel value in ball arithmetic (python-flint); see `run.log` and `run2.log`.
