# Fourier (Delsarte) certificates for small explicit distance sets

`certify.py kind N` checks rigorously that h(t) = 1 + Σ_d v_d J₀(d t) ≥ 0 for all t ≥ 0 (float grid with an explicit
Lipschitz margin on [0, T], Bessel tail bound |J₀(x)| ≤ √(2/(πx)) beyond). This gives m_D(ℝ²) ≤ 1/(1 + Σ v) and hence,
by the transfer, χ_D(ℝ²) ≥ 1 + Σ v.

| command | certificate | statement |
|---|---|---|
| `python3 certify.py odd 4` | cert_odd_4.json | every 6-colouring of ℝ² has a monochromatic pair at a distance in {1, 3, 5, 7} |
| `python3 certify.py odd 8` | cert_odd_8.json | every 8-colouring: a monochromatic odd distance ≤ 15 |
| `python3 certify.py prime 10` | cert_prime_10.json | every 10-colouring: a monochromatic distance in {2, 3, 5, 7} |
| `python3 certify.py pow2 6` | cert_pow2_6.json | every 16-colouring: a monochromatic distance in {1, 2, 4, …, 32} |
| `python3 certify.py sq 8` | cert_sq_8.json | every 18-colouring: a monochromatic square distance ≤ 64 |

`twodist.py` implements the uniform-in-d two-distance certificate of the paper. `lacunary.py`, `lacunary3.py`, `odd3.py`,
`oddsum.py` and `verify_opt.py` are supporting numerics for analytic proofs in the paper; they are not certificates.
