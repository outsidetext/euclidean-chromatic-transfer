# E^3 -> (l2, lk): pattern LP + Omega_3 certificates

Statement targeted: every red/blue coloring of R^3 with no two red points at distance 1 contains a blue
unit-step k-term AP (a blue congruent copy of l_k = {0,1,...,k-1}).
Known before: k = 6 (Arman–Tsaturian, E^3 -> (l2, l6)); our finite-graph argument (transfer.tex, end of
Section "finite graphs") gives blue translates of every 6-point set.

## 1. The random set (transfer in R^3 -- differs from the plane!)

In the plane (monochromatic.tex, Section 188) the pair correlation of the *original* Følner-averaged
coloring is F(|x-y|) = a0 + int J0 dnu, because rigidity kills the discontinuous part of f = 1[0 red]
at every z != 0. In R^3 this is NOT what the one-label transfer gives:

* G = V ⋊ K acts with K = algebraic rotations about ONE axis (the torus K^m, m = 1), not SO(3).
  So the law is not rotation-invariant, and correlations are not radial a priori.
* The block step gives <f, T_a f> = <g, T_a g> only for generic a, and the axis step does not give
  <g, T_a g> = <p, T_a p> pointwise: with w = g - p (discontinuous along the axis), only the invariant-mean
  average of <w, T_{a(t)} w> along curves t -> (rho(t)u, t) vanishes. The proposition's conclusion is
  about p = Qf, not about the original coloring.

So we use a derived random set instead. Let mu be the G-invariant Følner limit on colorings of the
algebraic points V = E x F (closed constraints: no red algebraic unit pair; every algebraic unit-step
k-AP has a red point), f = 1[0 red], p = Qf (Prop. "One-label transfer").

1. p in [0,1], <p, T_u p> = 0 for unit u, hence p * T_u p = 0 a.s. for algebraic unit u (both >= 0).
2. Q is a conditional expectation (Lemma factor) commuting with every T_a, a in V (Lemma comm), so
   sum_{i<k} T_{iu} p = Q(sum_{i<k} T_{iu} f) >= Q1 = 1 for algebraic unit u.
3. f' := 1[p > 0] is measurable w.r.t. the factor sigma-algebra, so f' in H_c(T) (translation-continuous).
   For algebraic unit u (T_u is a genuine Koopman composition): f' T_u f' = 0 a.s. and
   sum_{i<k} T_{iu} f' >= 1 a.s.  So the random set {x in V : T_x f' = 1} is unit-distance-free and
   meets every algebraic unit-step k-AP, its law is V-invariant, and delta' := E f' >= E p = E f.
4. Pattern probabilities pi_X(S) = E prod_{i in S} T_{x_i} f' prod_{i not in S} (1 - T_{x_i} f') are uniformly
   continuous in X in V^N (f' in H_c, factors bounded by 1), so they extend to all X in (R^3)^N. Each single
   constraint (one unit pair both red has probability 0; one unit-step k-AP all blue has probability 0)
   passes to real X by approximating X with algebraic X_n that keep that one pair/AP exact (algebraic unit
   vectors are dense in S^2). Translation invariance passes to real translations by continuity.
5. Average over Haar-random rho in O(3): pibar_X = int pi_{rho X} d rho. This is a consistent family of laws,
   invariant under all isometries of R^3, still a.s. unit-distance-free and k-AP-covering.
6. c(a) = pi_{0,a}(both red) is continuous positive definite on R^3, c = 0 on the unit sphere. Bochner +
   spherical average: F(r) = int Omega_3(|xi| r) dsigma(xi) = a0 + int_(0,inf) Omega_3(r t) dnu(t),
   a0 = sigma({0}) = ||Pi f'||^2 >= <f', 1>^2 = delta'^2 (Pi = projection on translation-invariant vectors,
   mean ergodic theorem), and a0 + nu(0,inf) = c(0) = E f'^2 = delta' (EQUALITY, since f' is 0/1).

Conclusion: the representation the task assumed holds exactly, but for the derived set f' (density
delta' >= delta), not for the original coloring. Since the certificates refute every delta' in [0, cap],
this is all that is needed. Isometry invariance (including reflections) justifies congruence equalities.

## 2. The cap delta' <= 0.14851123

research/m1r3/cert_final.json (verifier research/m1r3/verify_cert.py) proves: if g(r) = F(r)/delta' has
g = a0' + int Omega_3 da, a >= 0, a0' + int da = 1, a0' >= delta' and g(1) = 0, and pair marginals of an
invariant random set are delta' g, then delta' <= mu = 0.14851122983162682 (homogeneous cuts, sum y beta = 0).
Our pibar satisfies this with a0' = a0/delta' >= delta' and a0' + int da = 1 (by the equality in 6).
The verifier there assumes a0' = delta' (periodic case) but its derivation only uses a0' >= delta'
(mu - G(0) >= 1 gives a0' G(0) + (1 - a0') mu <= mu - a0' <= mu - delta'). Cap used: 1485113/10^7 > mu.

## 3. Pattern LP and certificates
See verify3d.py docstring for the exact certificate conditions (C1)-(C3) and the soundness chain.

## 4. Results (2026-10-14)

Certified (verify3d.py, exact rationals + arb; plus the imported cap of Section 2):
* E^3 -> (l2, l10): cert_k10_line13.json — one block, 13 collinear unit-spaced points, 4 ten-APs, 598 patterns,
  translation congruence s[0..11] ~ s[1..12]; 4 certificates cover delta in [0, 0.14865] ⊇ [0, cap].
* E^3 -> (l2, l11): cert_k11_line14.json — 14 collinear points, 975 patterns, 5 certificates cover [0, 0.14890].
  `venv/bin/python research/ramsey3d/verify3d.py research/ramsey3d/cert_k11_line14.json 11`
  (and `venv/bin/python research/m1r3/verify_cert.py research/m1r3/cert_final.json` for the cap).

LP (uncertified, primal, t-grid 3000 on (0,60] + t = inf):
* lines only, no cap: k=8 (11 pts) infeasible on [0,0.18]; k=9 on [0,0.16]; feasible above (lines do not bound delta).
* k=12: lines (15..20 pts, cong) + cap leave [0.135, 0.1486]; adding the 23 m1 cuts leaves ~[0.141, 0.1485].
  Not closed by: FCC clusters (ball:2, tball:2.5, oball:2.5), triangular 2-row strip tri2:13 (feasible at 0.145),
  adaptive triangle cuts (none violated at 0.145), adaptive 5-7 point hypermetric cuts (none found at 0.145),
  square strip sq2:13 (111522 patterns; feasible at 0.145), line:16 + tri2:13 jointly (feasible at 0.145, 0.1475).
  Fine window with line:15 + m1 cuts: infeasible at 0.140, feasible 0.141..0.148, infeasible at 0.1485.
* k=13: lines + cap leave [0.13, 0.1486].
So with this method ℓ12 would follow from lines alone if m1(R^3) <= ~0.140 were proven (Fourier bound saturates
at 0.1485 for 2-point constraints).

Cap-free variant not pursued: the m1 point sets have distances down to 0.0064, so h must be controlled out to
t ~ 3000 over ~370 distances; the cap is instead imported from the separately verified m1 certificate.
