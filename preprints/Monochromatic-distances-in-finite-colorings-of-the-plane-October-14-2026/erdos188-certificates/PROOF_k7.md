# Erdős #188: k ≥ 7 (every admissible coloring has a blue unit-step 6-AP)

Status: proof modulo the transfer/rigidity input (OpenAI Thm 2.3, Lean-verified; one-label
transfer, paper/transfer.tex Prop. "One-label transfer"). The finite part is an exact
certificate checked by `verify188.py cert_k7_nice.json` (exact rationals + arb ball arithmetic).

## Setup
Suppose the plane is red/blue colored, red unit-distance-free, no blue 6-term AP with unit step.
Restrict to the algebraic points E and Følner-average over E ⋊ K: we get an invariant probability
on colorings of E in which both rules hold on every finite configuration. Let δ = P(red at x).
By the one-label transfer plus rigidity, for x ≠ y in E,
P(x, y both red) = F(|x−y|), F(r) = a0 + ∫_{(0,∞)} J0(tr) dν(t), ν ≥ 0,
with a0 = μ({0}) ≥ δ² (Cauchy–Schwarz: ⟨Πp,1⟩ = E p = δ, Π = projection on ℝ²-invariant vectors)
and a0 + ν(0,∞) = F(0) = E p² ≤ δ.

## The finite configuration: 7 collinear points 0,u,…,6u (|u| = 1)
Let s ∈ {0,1}^7 be the red indicator. Admissible strings: no two adjacent 1s, and each of the
windows s0..s5, s1..s6 contains a 1 (31 strings). Define
Q(s) = −15 + 5s0 + 15(s1+…+s5) + 5s6
       − 5(s0s2 + s4s6 + s0s3 + s3s6 + s0s4 + s2s6) − (s0s5 + s1s6) + 5 s0s6
       − 14(s1s3 + s3s5 + s1s4 + s2s5) − 2 s1s5 − 10 s2s4.
**Lemma 1 (exact enumeration).** Q(s) ≥ 0 on all 31 admissible strings (20 are tight).

Taking expectations (E s_i = δ, E s_i s_j = F(j−i), F(1) = 0):
0 ≤ −15 + 85δ + Σ_n Y_n F(n), with Y = (Y1,…,Y6) = (−339/4, −48, −38, −12, −2, 5),
where Y1 multiplies F(1) = 0 and is a free parameter.

**Lemma 2 (arb).** h(t) = Σ_{n=1}^6 Y_n J0(nt) ≤ λ = 126/5 for all t ≥ 0
(adaptive Taylor cells on [0,24]; tail via |J0(x)| ≤ √(2/(πx)), Watson §13.74).

Then Σ Y_n F(n) = a0·h(0) + ∫ h dν ≤ a0 B + λ(δ − a0) ≤ λδ + δ²(B − λ), with B = h(0) = −719/4,
since B ≤ λ and a0 ≥ δ². Hence
0 ≤ q(δ) = −15 + (85 + λ)δ + (B − λ)δ² = −15 + 110.2 δ − 204.95 δ².
The discriminant 110.2² − 4·15·204.95 = −152.96 < 0, so q(δ) < 0 for every δ. Contradiction. ∎

Remarks
- The atom bound a0 ≥ δ² is essential: with a0 ≥ 0 only, the LP is feasible on δ ∈ [0.225, 0.33].
- Window 6 (one AP) is not enough (feasible on [0.245, 0.285]); window 7 (two overlapping APs) is.
- For ℓ7 (k ≥ 8) line windows give nothing beyond w = 8: feasible δ ∈ [0.22, 0.285] for w = 8..14.

## Upgrade: k ≥ 8 (every admissible coloring has a blue unit-step 7-AP)
Same argument with the configuration = 2×12 strip of the unit triangular lattice
{m + nω : 0 ≤ m < 12, n ∈ {0,1}} (24 points, 12 seven-term APs along the two rows, 5206 valid patterns).
Pair distances are √(m²+mn+n²). Four rational certificates (quadratic forms per pattern + one λ)
cover δ ∈ [0,1]: `certs_k8_strip2x12.json`, checked by `verify2d.py certs_k8_strip2x12.json 7`
(log `verify_k8_strip2x12.log`). The strip's off-row pairs (distances √3, √7, √13, …) are what
close the 1D gap: the 7-point line windows alone leave δ ∈ [0.22, 0.285] feasible for ℓ7.

## Limits observed for ℓ8 (k ≥ 9)
Strips 2×14 and 3×10 leave δ = 0.20, 0.22, 0.24, 0.26 feasible. No sign of closure at this size.

Files: lp1d.py, lp2.py (1D LPs), dualcert.py, gen_certs.py, verify188.py (1D certificates),
lp2d.py, dual2d.py, gen2d.py, verify2d.py (lattice configurations).
