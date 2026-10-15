# Erdős #173: shortest/longest ρ ∈ [0.86125, 0.88465], and the single ratio ρ = 0.886

**Claim.** For every algebraic ρ ∈ [689/800, 17693/20000] = [0.86125, 0.88465] and every algebraic b ∈ [ρ, 1],
every red/blue colouring of ℝ² contains a monochromatic congruent copy of the triangle (ρ, b, 1). Equivalently,
every triangle with algebraic side ratios whose shortest/longest ratio lies in [0.86125, 0.88465]. Together with the
593 boxes in `../regions/` (0.65 ≤ ρ ≤ 0.86125) and Theorem 2.1 (ρ ≤ 0.654), this gives every triangle with
algebraic side ratios and shortest side ≤ 0.88465 × longest. In addition, `iso0886_cfg17.json` shows that every
triangle with algebraic side ratios in which some two sides are in ratio 443/500 = 0.886 is monochromatic.

**Why one interval of ρ covers every middle side b** (paper, paragraph "From 0.86125 to 0.88465"). If a colouring
has no monochromatic copy of T = (ρ, b, 1), the Følner-averaged colouring σ has C(r) = a₀ + ∫J₀(rt) dν with
a₀ + |ν| ≤ 1, and almost surely no monochromatic copy of T. So C(ρ) + C(b) + C(1) = −1, while equilateral
triangles give C ≥ −1/3 at each side; hence C(ρ) = C(b) = C(1) = −1/3. Each triangle with sides in {ρ, 1}
(a triangle since 2ρ > 1) then has pair sum ≥ −1 with mean −1, so it is almost surely not monochromatic. The
certificates use only the J₀-mixture form of C and this property, so b never enters. (This concerns the averaged
law; it does not say that the original colouring avoids monochromatic (ρ, 1, 1).)

## Files

| file | content | ρ-range | sha256 |
|---|---|---|---|
| `strip_086125_0869.json` | 7 strip boxes `[[a0,a1],[1,1]]` (triangle (a,1,1), aux triples) | [0.86125, 0.869] | `ce8c63a73e52ecc407b0d9b38718f159e53d1134d97e120a03685ac77fc9e832` |
| `strip_0869_0879.json` | 9 strip boxes | [0.869, 0.870484375] | `7fd89be1abb878f6e0442c0d01336ccc3d0fd1f822602cc0bfc67ab352e746b2` |
| `int2_band_A.json` | 15 `173-pattern-int-v2` interval certificates | [0.870426, 0.8779] | `57aa0f4f3d99546b2add95aafef2272f649dfb8e7ac0908a0c3b4ece245be72d` |
| `int2_band_B.json` | 22 `173-pattern-int-v2` interval certificates | [0.8779, 0.88465] | `d448986fb28f5b91d0786d6011adca1b61bccdc0b4eeba7c9aa82cbe59d0e80f` |
| `iso0886_cfg17.json` | single shape ρ = 443/500, 17 glued 7-point configurations (`173-pattern-v1`) | {0.886} | `18fe99042bc35748b80ca5b9c548269fab6a4bedfc1aa26cd9a5fa4382bff4c1` |

Each interval certificate consists of (ρ,1,1) and six 7-point configurations glued from triangles with sides in
{ρ, 1} by exact rotations ((1−m²) + 2mi)/(1+m²), m ∈ ℚ, with pair weights, auxiliary triples and a value Λ that does
not depend on ρ. It is valid when sup f(t; ρ) < Λ over t ≥ 0 and ρ in the interval.

Checkers:

* `check_beyond173.py`: the referee checker, written from the definitions and sharing no code with the others. It
  evaluates the geometry as second-order arb power series in ρ and bounds f on adaptive 2-D cells in (t, ρ) with a
  joint second-order Taylor bound. J₀ comes from `../j0fast.py` (error ≤ 1e-14 per value, added explicitly). Tail
  t ≥ T: |J₀(x)| ≤ √(2/(πx)). It also checks coverage in exact rationals. `--tamper DIR` runs 23 negative controls.
* `check_beyond.py`: the authors' checker for the pattern certificates. It uses second-order Taylor bounds in ρ about
  the midpoint of each interval, with r′, r″ from forward automatic differentiation in arb, and second-order Taylor
  bounds in t on cells.
* `verify_box.py`: the authors' arb checker for box certificates, used here for the strips. It is identical to
  `../verify_box.py`.
* `cover1d.py`: 1-D coverage of the union of the ρ-intervals, in exact rationals.
* `verify_all.sh`: runs `verify_box.py`, `check_beyond.py` and `cover1d.py` on all files.

Both checkers come from the research repository: `check_beyond173.py` from `verify_mine/` (commit adc3478), the
others from `research/triangles173_beyond/` and `research/triangles173_lp/`. Only paths were changed: the J₀
library import in `check_beyond173.py` and the directories in `verify_all.sh`. The docstrings still name the
research-repository paths.

## Running

You need Python 3 with numpy and python-flint. First build the J₀ table once, in the parent folder:

```
cd .. && python3 gen_table.py && clang -O3 -fPIC -shared -o libj0fast.dylib j0fast.c && cd beyond0886
```

(On Linux use `-o libj0fast.dylib` anyway, since `j0fast.py` loads that file name.)

**Referee checker** (about 1 s):

```
python3 check_beyond173.py --quiet strip_086125_0869.json strip_0869_0879.json int2_band_A.json int2_band_B.json
```

It prints one `PASS` line for each of the 53 certificates, and then:

```
COVERAGE of [689/800, 17693/20000] by 53 verified intervals: COMPLETE
ALL PASS  [1s]
```

The smallest margin Λ − max f is 3.0·10⁻³, at `int2_band_B[21]`, where max f(centres) = 0.996995. The smallest tail
margin is 2.4·10⁻³ (tail 0.9976 at `int2_band_B[15]`). The single shapes are checked with
`python3 check_beyond173.py --quiet --nocover iso0886_cfg17.json ../beyond/iso088_cfg.json ../beyond/iso0885_cfg.json`.
All three pass, with max f(centres) 0.999771, 0.980247 and 0.998177 against Λ = 1, and the run ends with `ALL PASS`.
The negative controls are run with `python3 check_beyond173.py --tamper .` and end with
`NEGATIVE CONTROLS: all behaved as expected`. In those controls, the tampered certificates that should fail (moved or
widened intervals, a changed rotation, a flipped reflection, a relabelled template, a doubled weight, removed or
invalid aux rows, a lowered T, a moved strip, a dropped interval) fail. Three small perturbations that remain
genuinely valid pass.

**Authors' checker** (`PY=python3 sh verify_all.sh`, tens of minutes). Expected output:

```
strip_086125_0869.json: ALL 7 BOX CERTIFICATES VERIFIED
strip_0869_0879.json: ALL 9 BOX CERTIFICATES VERIFIED
int2_band_A.json: 15 interval certificates VERIFIED
int2_band_B.json: 22 interval certificates VERIFIED
53 intervals; contiguous coverage from 0.86125 up to 0.884650 (17693/20000)  COVERS TARGET
iso0886_cfg17.json: VERIFIED (every 2-colouring of the plane contains a monochromatic copy of T = ('443/500', '1', '1'))
```

The single shape ρ = 0.886 is also accepted by the older referee checker in `../beyond/`:
`python3 ../beyond/check_173_patterns.py iso0886_cfg17.json`, which reports margin 2.32e-04.

**Limit.** The certified range ends at 0.88465, where the admissible interval width has fallen to about 6·10⁻⁶.
Numerically these 7-point pattern constraints stop near ρ ≈ 0.887.
