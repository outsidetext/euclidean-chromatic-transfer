# Certificates

Python 3 with `sympy` and `python-sat`; DRAT proofs are checked with
[drat-trim](https://github.com/marijnheule/drat-trim). Unpack `.xz` files first (`xz -dk`).

| Folder | Result | Check |
|---|---|---|
| `seven-colors/` | χ(ℝ², {1, (√2+√6)/2}) ≥ 7: V8 gadget and chains A, B | `python verify_exact.py` (exact quadratic-tower arithmetic, plus SAT caps); `drat-trim v8cert.cnf v8cert.drat`, same for `capA`, `capB` |
| `g26/` | 26-vertex 6-chromatic {1, (√2+√6)/2}-graph | `python verify117best.py deneve117_min.json`; `drat-trim record26.cnf record26.drat` |
| `g30/` | 30-vertex 6-chromatic {1, √3}-graph | `python verify30.py`; `drat-trim record30.cnf record30.drat` |
| `e5-2278/` | the 509-vertex graph stays non-4-colorable with 2278 unit edges | `drat-trim edge2278.cnf edge2278.drat` (about 10 s) |
| `forced-density/` | forced monochromatic density 1/67 at distance 1 under √3-proper 5-colorings | `python verify67.py record67_graph.json`; `drat-trim record67.cnf record67.drat` |
| `six-coloring-continuum/` | X₆ ⊇ [0.657, 0.667504532081] | `python verify_continuum.py` (interval coverage); `python verify_all.py` re-derives all 59 exact tiling certificates (several minutes) |

All of these passed on 2026-10-14.
