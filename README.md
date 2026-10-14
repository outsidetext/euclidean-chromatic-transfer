# Euclidean chromatic numbers: transfer theorems and records

A small manuscript collection on the chromatic number of Euclidean spaces, with Lean
formalizations and machine-checkable certificates. The layout follows
[openai/math](https://github.com/openai/math).

- [**CONTENTS.md**](CONTENTS.md): the result families and their manuscripts.
- [`preprints/`](preprints/): one folder per manuscript (`paper.pdf`, `paper.tex`, and any certificates).
- [`lean/`](lean/): the Lean 4 / Mathlib development and its catalog [`formalization.yaml`](lean/formalization.yaml).
- [**history.md**](history.md): dated record of the results and of related work.

**Status.** Nothing here has been refereed. The Lean statements are machine-checked
with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Numerical
density bounds from the literature appear as explicit hypotheses.

## Build and check
```
cd lean
lake exe cache get              # Mathlib oleans (pinned commit d13f23b)
lake build OAI.HNN.Corollary OAI.HN3.Finite OAI.HN3.IndepFolner OAI.Soifer.Main
lake env lean CheckN.lean       # n-dimensional transfer and corollaries: prints axioms
lake env lean CheckRepair.lean  # chi(R^n) = measurable chi(R^n), n >= 2: prints axioms
lake env lean Check3.lean       # three-dimensional development
lake env lean CheckIndep.lean   # finite graphs attain the density in R^3
lake env lean CheckSoifer.lean  # monochromatic 2^n and n! distances (Soifer, Kahle)
```
Certificates for the record graphs are checked by the scripts beside them; see
[`preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/certificates/README.md`](preprints/Chromatic-numbers-of-the-plane-with-two-forbidden-distances-October-14-2026/certificates/README.md).

## License
Lean sources and scripts: Apache License 2.0 (see [LICENSE](LICENSE)). The modules under
`lean/OAI/{Analysis,Geometry,MeasureTheory}` are from github.com/openai/math, used
unmodified under the Apache License 2.0 (see `lean/LICENSE-openai-math`).
