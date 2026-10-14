import OAI.Soifer.Embed

/-!
# Furstenberg–Katznelson–Weiss (weak form) in the plane

A measurable set `A ⊆ ℝ²` whose density in the squares `[-T,T]²` is at least `c > 0` for
arbitrarily large `T` realises some distance of every unbounded set `S` of positive reals.

Proof: put `a = 4c/9`, `K = 1600/a² + 1`, `J = ⌊2/a⌋ + 1`, choose radii `r_0 < r_1 < …` in `S`
with `r_{j+1} > 4K r_j`, and a square `[-T,T]²` with `T > r_J` and density `≥ c`. With `L = 3T`
the torus set of `A ∩ [-T,T]²` has measure `≥ a`; if `A` avoided all `r_j` then
`torus_bound` would give `J a ≤ 2`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set
open OAI.EuclideanFiveColor OAI.HNN

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **FKW, weak form.** -/
theorem fkw {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) {c : ℝ} (hc : 0 < c)
    (hfreq : ∃ᶠ T in atTop, ENNReal.ofReal c * volume (cube 2 T) ≤ volume (A ∩ cube 2 T))
    {S : Set ℝ} (hS : ∀ s ∈ S, 0 < s) (hunb : ¬ BddAbove S) :
    ∃ s ∈ S, ∃ x ∈ A, ∃ y ∈ A, dist x y = s := by
  by_contra hno
  push Not at hno
  set a : ℝ := 4 * c / 9 with ha_def
  have ha : 0 < a := by positivity
  set K : ℝ := 1600 / a ^ 2 + 1 with hK_def
  have hK1 : 1 ≤ K := by have : 0 ≤ 1600 / a ^ 2 := by positivity
                         linarith
  have hK : 0 < K := by linarith
  have hKa : 400 / (1 + K) ≤ (a / 2) ^ 2 := by
    have h1 : 400 / (1 + K) ≤ 400 / (1600 / a ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have h2 : 400 / (1600 / a ^ 2) = (a / 2) ^ 2 := by field_simp; ring
    linarith
  set J : ℕ := ⌊2 / a⌋₊ + 1 with hJ_def
  have hJa : 2 < (J : ℝ) * a := by
    have h := Nat.lt_floor_add_one (2 / a)
    rw [hJ_def]
    push_cast
    have := (div_lt_iff₀ ha).mp h
    linarith
  -- radii
  rw [not_bddAbove_iff] at hunb
  choose f hfS hfM using hunb
  let r : ℕ → ℝ := fun n => Nat.rec (f 0) (fun _ x => f (4 * K * x)) n
  have hrS : ∀ n, r n ∈ S := by
    intro n; cases n with
    | zero => exact hfS 0
    | succ n => exact hfS _
  have hrpos : ∀ n, 0 < r n := fun n => hS _ (hrS n)
  have hrstep : ∀ n, 4 * K * r n < r (n + 1) := fun n => hfM _
  have hsep : ∀ i j, i < j → 4 * K * r i ≤ r j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact (hrstep i).le
    | succ j _ ih =>
      have h1 := hrstep j
      have h2 : r j ≤ 4 * K * r j := by nlinarith [hrpos j]
      linarith
  have hrJ : ∀ j < J, r j ≤ r J := by
    intro j hj
    have := hsep j J hj
    nlinarith [hrpos j]
  -- the square
  obtain ⟨T, hTdens, hTge⟩ := (hfreq.and_eventually (eventually_ge_atTop (r J + 1))).exists
  have hT : 0 < T := by linarith [hrpos J]
  set L : ℝ := 3 * T with hL_def
  have hL : 0 < L := by positivity
  set B := A ∩ cube 2 T with hB_def
  have hBm : MeasurableSet B := hA.inter (cube_measurable T)
  have hBT : B ⊆ cube 2 T := inter_subset_right
  set E := torusSet L B with hE_def
  have hEm : MeasurableSet E := torusSet_measurable L hBm
  have haE : a ≤ (volume E).toReal := by
    have hvol := volume_torusSet hL (by linarith) hBm hBT
    have hlow : ENNReal.ofReal a ≤ volume E := by
      rw [hE_def, hvol]
      calc ENNReal.ofReal a = ENNReal.ofReal (L ^ 2)⁻¹ * (ENNReal.ofReal c *
            ENNReal.ofReal ((2 * T) ^ 2)) := by
            rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [ha_def, hL_def]
            field_simp
            ring
        _ ≤ ENNReal.ofReal (L ^ 2)⁻¹ * volume B := by
            rw [← volume_cube2 hT.le]
            exact mul_le_mul_right hTdens _
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hlow
  have hb := torus_bound E hEm (fun j => r j / L) J ha haE hK hKa
    (fun j => div_pos (hrpos j) hL)
    (fun i j hij => by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (hsep i j hij) hL.le)
    (fun j hj t => by
      have := hrJ j hj
      exact torusSet_avoid hL (hrpos j) (by linarith) hBT
        (fun x hx y hy => hno _ (hrS j) x hx.1 y hy.1) t)
  linarith

end
end OAI.Soifer
