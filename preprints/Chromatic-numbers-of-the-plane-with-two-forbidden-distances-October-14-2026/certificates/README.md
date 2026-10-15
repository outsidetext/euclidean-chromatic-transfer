# Certificates

Python 3 with `sympy`, `mpmath` and `python-sat` (and `python-flint` for `e6-lower-bound/`); DRAT proofs are checked with
[drat-trim](https://github.com/marijnheule/drat-trim). Unpack `.xz` files first (`xz -dk`).

| Folder | Result | Check |
|---|---|---|
| `seven-colors/` | χ(ℝ², {1, (√2+√6)/2}) ≥ 7: V8 gadget and chains A, B | `python verify_exact.py` (exact quadratic-tower arithmetic, plus SAT caps); `drat-trim v8cert.cnf v8cert.drat`, same for `capA`, `capB` |
| `g26/` | 26-vertex 6-chromatic {1, (√2+√6)/2}-graph | `python verify117best.py deneve117_min.json`; `drat-trim record26.cnf record26.drat` |
| `g30/` | 30-vertex 6-chromatic {1, √3}-graph | `python verify30.py`; `drat-trim record30.cnf record30.drat` |
| `e5-2257/` | the 509-vertex graph stays non-4-colorable with 2257 unit edges | `drat-trim edge2257.cnf edge2257.drat` (binary DRAT, about 30 s); `python check_unit.py parts509_coordinates.vtx edge2257_graph.json` (the edges are unit distances) |
| `e6-lower-bound/` | a periodic 5-coloring with monochromatic unit-segment probability p ≤ 0.0031083, hence e₆ ≥ 322 and v₆ ≥ 62 | `python certify.py c5_best.json` (needs `python-flint`; exact tiling check plus ball-arithmetic bound on p, about 15–20 min with `CERT_WORKERS=3`); `python certify.py hex4_11335.json` (calibration: 1/p₄ = 98.4956, de Grey–Parts' e₅ ≥ 99); independent float check: `cc -O2 -o pmono pmono.c -lm && python dump.py c5_best.json rows \| ./pmono 4000` |
| `forced-density/` | forced monochromatic density 1/67 at distance 1 under √3-proper 5-colorings | `python verify67.py record67_graph.json [path/to/drat-trim]` (or set `DRAT_TRIM`); `drat-trim record67.cnf record67.drat` |
| `six-coloring-continuum/` | X₆ ⊇ [0.657, 0.667504532081] | `python verify_continuum.py` (interval coverage); `python verify_all.py` re-derives all 59 exact tiling certificates (several minutes) |

All of these passed on 2026-10-14; `e5-2257/` and `e6-lower-bound/` on 2026-10-15.
