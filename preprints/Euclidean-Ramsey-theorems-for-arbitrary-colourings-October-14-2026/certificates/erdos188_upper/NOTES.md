# Erdős #188 — explicit periodic upper bounds (work in progress)

Problem: least k such that R^2 can be 2-coloured with no red unit distance and no blue
unit-step k-AP (x, x+u, ..., x+(k-1)u, |u|=1).  Known: 8 <= k (ours, ../erdos188) and
k <= 6330 (Currier–Mody–Xie–Zhang, random hexagonal-cell colouring).

## Model

RED = union of OPEN discs of radius 1/2 centred at a P-periodic point set (P a lattice,
n centres per period), with every two distinct centres at distance >= 2.
* No red unit distance: inside one open disc all distances are < 1; points of two
  different open discs are at distance > |c - c'| - 1 >= 1.
* (Any red set whose components are convex is a union of convex pieces of diameter
  <= 1 that are pairwise >= 1 apart; discs maximise width for given diameter, so the
  disc model is natural.)

Blocking condition: for every unit u, union_{j<k} (R - j u) = R^2.

## Structural facts used / learned

1. Corridors: a straight blue strip gives an infinite blue AP.  A single convex body
   per lattice (K + P) ALWAYS has a corridor when diam K < 1 and the copies are >= 1
   apart (Minkowski on L and L*, plus Mahler: vol(D+B1) vol(D°) <= 16 is impossible
   with D = K - K inside the unit disc).  So several discs per period are needed.
2. Line-blocking only needs the finitely many lattice directions lam with
   |lam| < covol/(2 r_eff): projections of the centres onto lam^perp (circle of length
   covol/|lam|) must leave no gap > 2 r_eff.  We minimise r* = max half-gap with a
   sequential LP subject to separation (slp.py, slp3.py).  r*/dmin < 1/4 is needed;
   dense configurations reach r*/dmin ~ 0.155–0.17.
3. Generic directions behave like random coverings: N ~ ln(area/eps)/density.  The hex
   lattice of discs (spacing 2, density 0.227) has N(theta) <= 13 for theta in
   [14°, 46°] (mod 60°) but corridors at 0° (and near-zero-width ones at 30°).
   Corridor-free configurations found so far have median N ~ 30 (density ~0.19).
4. Worst directions are near-corridor / near-resonant directions (small drift of the
   orbit j u mod P), not necessarily short lattice vectors.

## Certification (certify.py)

(a) exact rational check of all centre separations >= 1 + 2r.
(b) all directions theta in [0, pi]: rational unit vectors u_m (from dyadic
    t = tan(theta/2)), arc [u_m, u_{m+1}] assigned to u_m with erosion j*|u_{m+1}-u_m|
    at step j; starts x in the closed fundamental parallelogram; strips in the
    perpendicular coordinate with chords intersected over the strip (convexity);
    1-D interval cover check; adaptive refinement of strips and arcs.  float64 with
    1e-9 margins on every radius / cover comparison.

## Results log

(see below)

### 2026-10-14 log
* corridor annealing (free lattice, n=3..6): r*/dmin >= 0.26 -- corridors persist.
* SLP (slp.py) hex torus L1=6,n=20: r*/dmin=0.167 but density 0.126, raster max ~108,
  median ~48 (low density => poor generic coverage).  Integer |lambda| (e.g. L1=12)
  gives resonant infinite APs -- avoid integer/low-denominator lattice lengths.
* dense SLP from jittered expanded hex supercells (slp3.py): (a,b)=(4,1), sigma=1.1,
  n=21, scaled density 0.954 (orig density 0.187), r*/dmin=0.168..0.174.
  raster max 98, median 32.
* ABC-domain and CSL-bicrystal constructions (domains.py, bicrystal.py): density
  ~0.19-0.20 but interfaces create corridors / long near-corridor paths; medians 35+.
  Not better than SLP configs.
* **CERTIFIED k = 130 and then k = 105** for cand_41a.json (slp3_4_1_1.10.json[2]
  scaled x2, rationalised).  `python3 certify.py cand_41a.json 105 0.0005`
  (6312 arcs, 28 splits, ~3 min).  Consistency: certifier rejects k=95 at
  theta=120.367 deg, so for this colouring the true sup N is in [96, 105].
  MC check (mc_check.py) max observed 87.
* witness LP optimiser (witness.py, raster-based): from the k=105 colouring, raster
  sample max 98 -> 62 in ~15 min.  BUT the certifier then failed at k=66 near
  theta=70.70 deg: the true N there is 74 (exact witness start found by exactn.py),
  while 20000 random MC starts only see 62 and the 3000-direction raster sample missed
  the peak (width ~0.01 deg).  Lesson: raster sampling of theta is too coarse for
  peaks; the optimiser now (Opt2) checks a direction set with the exact strip method
  and extracts exact witness starts.

## Why float64 + 1e-9 margins is rigorous in certify.py (error analysis)

Inputs are rationals of size <= ~10^3 (coordinates of lifted centres and of F, |x| <= X ~ 300).
Converting to float64 and forming t = x.u, s = x.u^perp costs absolute error
eps0 <= 8 X 2^-53 < 1e-12 per coordinate (u is the float of an exact rational unit vector;
|u.u - 1| <= 4e-16, so the step-j point has t-coordinate t(x) + j up to j*4e-16 < 1e-13).

Chord half-length.  The dangerous operation is h = sqrt(rho^2 - dlt^2) near tangency (sqrt
amplifies absolute errors), so the margin is put on the RADIUS, not only on h:
rho_c = rho_true - j e - 1e-9 (e already rounded up), dlt_c >= dlt_true - 2e-12.  Then
  rho_c^2 - dlt_c^2 <= rho_true^2 - dlt_true^2 - 2 rho (0.9e-9) + 2 dlt (2e-12) + 1e-16
                    <  rho_true^2 - dlt_true^2        (since dlt < rho and rho >= 0.1),
including the float rounding of squaring/subtracting (relative 2^-53 on numbers <= 1).
sqrt is correctly rounded and monotone, so the computed radicand never exceeds the true
one and h_c <= h_true (1 + 2^-53); we further subtract 1e-9 from h_c.  Hence every
interval [tc - h - j, tc + h - j] used is contained in the true open chord interval
(endpoint errors ~1e-12 << 1e-9).

Cover test.  Comparisons are done in coordinates relative to the strip's tlo (values < 300,
error < 1e-12) and require overlaps >= 1e-9 (gaps) and run >= span - 1e-11 at the end, the
latter covered by the 1e-9 outward rounding of [tlo, thi].  Strips: a true point (s_true)
lies within 2e-12 of its computed s, absorbed in the dlt budget above; the strip family
covers [smin - 1e-9, smax + 1e-9].

Directions: arcs between consecutive EXACT rational unit vectors; e_m is an upper bound of
|u_{m+1} - u_m| (float sqrt inflated by 1e-12 relative).  (a) is exact rational arithmetic.

So all float errors (< 1e-11 total) are dominated by the 1e-9 margins.  An independent
second implementation (indep_claude/cert2.py, coordinator) re-certified the k=105 colouring.

### certified k = 85, then k = 74
* cand_w63.json (witness-optimised, raster sample said 62): certify FAILS at k=66 (true N
  near 70.70 deg is 74, a near-resonance with the shortest period vectors |lambda| = 10.082,
  ~0.2 deg off lambda-hat); CERTIFIED k = 85.
* Certifier-driven loop (run_w4.py: full arc pass -> failing directions -> exact witnesses
  -> LP; acceptance requires no increase of failures on the accumulated direction set and
  of the coarse raster max).  The same colouring passes k = 74 at arc depth 5; certify.py on
  the rationalised version: **CERTIFIED k = 74** (cand_w74.json, 4603 arcs, 115 splits).
* Global rescaling of an optimised colouring (to move |lambda| = 10.08 away from 10) makes
  it much worse (least passing k >= 90 at |lambda| = 10.37): the optimum is tuned to its
  lattice; scale has to be chosen before optimising.

## How low can periodic disc colourings go? (heuristic floor)

* Generic directions.  For the hexagonal lattice of discs (spacing 2, density 0.227)
  N(theta) <= 13 on [14, 46] deg (mod 60) -- the translates R - j u of a single lattice
  orbit form a near-lattice covering.  For corridor-free configurations (n ~ 13-27 discs per
  period, density 0.17-0.19) the translates behave like random coverings: median N ~ 30,
  consistent with N ~ ln(area / eps) / (-ln(1 - density)) (area ~ 90, eps ~ 1e-2 gives ~45;
  structured coverage gets ~30).  Corridor-freeness forces n >= ~12 (SLP: r*/dmin < 1/4 only
  reached for n >= 12 at useful densities; single-orbit colourings always have corridors).
* Resonances.  For a period vector lambda with |lambda| = L and m L within eta of an integer
  q, directions u ~ lambda/q give orbits that drift by ~ m*eta per q steps, and a blue comb
  can survive ~ q * (extent of the blue comb region) / (m eta) steps.  With L ~ 10 and n ~ 20,
  every colouring we optimised was finally limited by the shortest vectors (here
  |lambda| = 10.08, eta = 0.08, worst direction 0.2 deg off lambda-hat).  By Dirichlet one
  cannot keep m*L away from integers for all m <= k/L, so the comb condition (the q
  translates along lambda/q must cover T) has to be met geometrically for small q.
* Our best guess: periodic disc colourings with ~20 discs per period should reach k ~ 40-50
  with better optimisation (median 30 + resonance penalty); going to ~20 would need
  lattice-like generic coverage AND no corridors, which we could not reconcile
  (ABC-domain / bicrystal / corrugated constructions all lost on interfaces).
  So the realistic floor for this family is ~ 30-50; the true answer to #188 (>= 8) is
  presumably much lower and needs non-periodic or non-disc ideas.

### certified k = 72  (best.json = cand_w72.json)
run_w6.py (certifier-driven; acceptance also re-checks EXACTLY the raster's 16 worst
directions and feeds their witnesses back; witnesses collected at k-8, failures counted at
k-1 resp. k-3) moved the k=74 colouring to one passing k=72.
`python3 certify.py cand_w72.json 72 0.0007` -> CERTIFIED (4630 arcs, 142 splits, 79 s);
independent `indep_claude/cert2.py cand_w72.json 72 4000` -> ALL ARCS OK.

### certified k = 68  (best.json = cand_w68.json)
Start: slp3 (a,b)=(3,3), sigma=1.1 (27 discs/period, hexagonal period lattice with
|lambda_1| = 11.43, i.e. far from integers -- weaker resonance), raster witness optimisation
(raster max 67->65) then run_w6 certifier-driven loop: passes 72, 70, 68 quickly; 66 fails
(386 arcs).  certify.py: CERTIFIED k=68 (4499 arcs, 11 splits, 55 s); cert2.py: ALL ARCS OK
(k=68); k=67 not certified (true sup N of this colouring is 68).
