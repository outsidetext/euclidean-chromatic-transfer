# Certificate for m₁(ℝ³) ≤ 0.1484362

`cert_0148436.json` holds 106 correlation-polytope cuts on configurations of 3 to 12 points, with their multipliers.

**What the checks establish:** m₁(ℝ³) ≤ (μ + √(μ² − 4 Σ y β))/2 = 0.14843610000005 ≤ 0.1484362, with μ = 0.1484361. The checks, done in ball arithmetic (python-flint):
- each cut inequality by exact enumeration;
- G(t) ≤ μ on Taylor cells for t ∈ (0, 4709];
- |sin x / x| ≤ 1/x beyond that.

**The two verifiers:**
- `python3 verify_cert.py cert_0148436.json`
- `python3 xcheck.py cert_0148436.json`, an independent re-implementation written from scratch before this certificate existed.

Both report `CERTIFIED`, with a margin of μ − max G of about 7e-9.

**Older certificates:**
- `cert_final.json` is the earlier 23-cut certificate for m₁(ℝ³) ≤ 0.1485113.
- `cert_onecut.json` is the single-cut certificate for m₁(ℝ³) ≤ 0.158035 < 1/6.

`m1lib.py` holds shared helpers.
