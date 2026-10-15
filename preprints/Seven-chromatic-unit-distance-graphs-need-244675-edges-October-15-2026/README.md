# 7-chromatic unit-distance graphs need at least 244,675 edges

An explicit periodic 6-colouring of the plane (a curved refinement of Pritikin's pentagonal rod tiling; 90 convex pieces with exact rational coordinates, `PRfine_exact.json`) has monochromatic unit-pair density

p₆ ≤ 4.0870626204·10⁻⁶ (rigorous; ball arithmetic).

By the de Grey–Parts argument (arXiv 2303.14714), every 7-chromatic unit-distance graph then has at least ⌈1/p₆⌉ = **244,675 edges** (previously 232,646) and at least 6,705 vertices (this vertex bound does not beat Parts' v₇ > 6,992).

- `check_p6.py`: independent checker (Green's theorem twice → edge-pair log-distance integrals, arb rigorous integration; exact input validation). Run: `python3 check_p6.py PRfine_exact.json`.
- `PRbest_exact.json` (42 pieces): p₆ = 4.1024135075·10⁻⁶ ⇒ e₇ ≥ 243,759.
- `p6_REPORT.md`: verification report (self-tests, negative tests, Monte Carlo cross-check). `CERT.md`: construction notes.

Note: the colouring is on a knife-edge (rows exactly ½ high); the bound is exact for the rational data given.
