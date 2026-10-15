# Certificates for the Euclidean Ramsey manuscript

Python 3 with numpy, scipy and python-flint. Run each command inside its folder.

| folder | statement | commands |
|---|---|---|
| `triangles/` | monochromatic collinear triples (all algebraic ratios) and triangles with shortest/longest ≤ 0.80 in every 2-colouring of ℝ² | `python3 collinear.py`; `python3 triangles.py` (≤ 0.654, see NOTES.md); 0.65–0.80 by 333 box certificates: `python3 verify_box.py regions/<file>.json` for each file (ball arithmetic), independent `TMAX=600 A0=13/20 A1=4/5 python3 check_boxes.py regions/*.json` (Lipschitz enclosures plus coverage of the whole region); (4,5,6), (5,6,7), (7,8,9), (3,3,4): `python3 verify173.py t4_5_6.json t567.json t7_8_9.json t334.json`, independent `python3 check173.py t4_5_6.json t567.json t7_8_9.json t334.json` |
| `erdos188_lower/` | every red/blue colouring of ℝ² with no red unit pair has a blue unit-step 7-term progression (k ≥ 8) | `python3 verify188.py cert_k7_nice.json`; `python3 verify2d.py certs_k8_strip2x12.json 7`; independent: `python3 check_k7.py`, `python3 check_k8.py certs_k8_strip2x12.json 7` |
| `erdos188_upper/` | a periodic colouring with no red unit pair and no blue unit-step 49-term progression (k ≤ 49) | `python3 certify.py cand_w49.json 49 0.0007`; independent: `python3 cert2.py cand_w49.json 49 4000` |
| `ramsey3d/` | E³ → (ℓ₂, ℓ₁₁) | `python3 verify3d.py cert_k11_line14.json 11`; independent: `python3 check3d.py cert_k11_line14.json` (uses m₁(ℝ³) ≤ 0.1485113, certified in the three-space manuscript) |
| `erdos214/` | partial results on Erdős #214 | `python3 verify_small.py`; `python3 verify_ST.py cert_ST_R10.json 10 6/5`; `python3 verify_ST.py cert_ST_delsarte_R20.json 20 2/5 0.2873` |
