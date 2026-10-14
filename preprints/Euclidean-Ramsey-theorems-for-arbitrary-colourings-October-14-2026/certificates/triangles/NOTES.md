# Monochromatic triangles in arbitrary 2-colourings of the plane (Erdős #173 / EGMRSS conjecture)

**Theorem.** Let T be a (possibly degenerate) triangle with side lengths a, b, c whose ratios are algebraic.
If S_T(t) = J0(at) + J0(bt) + J0(ct) > -1 for all t >= 0, then every red/blue colouring of R^2 (no regularity)
contains a monochromatic congruent copy of T.

**Proof.** Scale so a, b, c are algebraic; then T has a copy with algebraic vertices. Følner-average the colouring
over E ⋊ K (E algebraic points, K algebraic rotations) to an invariant random colouring of E; let σ = ±1 spin at 0.
σ is K-fixed, so by OpenAI Thm 2.3 the component orthogonal to continuous vectors has zero correlation at every z ≠ 0;
hence C(z) = E σ(0)σ(z) = a0 + ∫ J0(|z|t) dν(t) for z ≠ 0, a0 >= 0, a0 + ν(0,∞) <= ||σ||^2 = 1.
P(copy monochromatic) = (1 + C(a) + C(b) + C(c))/4 >= (1 + min(0, inf S_T))/4 > 0. A pattern of positive probability
occurs in some isometric image of the original colouring.  ∎  (Measurable case: Shkredov, arXiv 1507.02727, Thm 9.)

**Certified consequences** (Lipschitz grids + Bessel tail |J0(x)| <= sqrt(2/(pi x)), J0 >= -0.4027594):
- `collinear.py`: inf over t >= 0 and all ratios of J0(t)+J0(kt)+J0((1+k)t) >= -0.73458 (worst k = 1, the unit 3-AP).
  => every 2-colouring of the plane has a monochromatic copy of every collinear triple {0, a, a+b} with a/b algebraic
  (Currier–Moore–Yip 2024: {0,1,2}).
- `triangles.py`: all triangles with shortest side <= 0.654 x longest side satisfy inf S_T > -1 (78% of cells of the
  shape space certified; the uncertified ones are near-equilateral, all sides >= 0.655 x longest). Equilateral fails
  (3 min J0 = -1.208), consistent with the strip colouring avoiding monochromatic unit equilateral triangles.
