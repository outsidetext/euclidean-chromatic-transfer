import OAI.Soifer.Lacunary
import OAI.Soifer.Main

/-!
# Erdős Problem #706: `L(r)` is not polynomially bounded

For `D_K = {q^j : j < K}`, `q = 10⁶` (a `K`-element set of positive integers), every colouring
of the plane in which no two points at a distance from `D_K` share a colour uses at least
`(4/9)·(3/2)^K` colours. Hence no bound `L(K) ≤ C·K^e` holds.

Proof: the colouring gives, via `euclidean_transfer_set`, a measurable `D_K`-avoiding class of
density `≥ 1/k` in arbitrarily large squares; embedded in the torus of side `3T` it has
measure `α ≥ 4/(9k)`; the torus Delsarte bound with the lacunary certificate gives
`α (3/2)^K ≤ 1`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set
open OAI.EuclideanFiveColor OAI.HNN

local instance erdos706MS : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance erdos706Prob : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The lacunary distance set `{(10⁶)^j : j < K}`. -/
def lacD (K : ℕ) : Finset ℝ := (Finset.range K).image (fun j => qL ^ j)

lemma lacD_card (K : ℕ) : (lacD K).card = K := by
  rw [lacD, Finset.card_image_of_injective _
    (pow_right_injective₀ qL_pos (by rw [qL_eq]; norm_num)), Finset.card_range]

lemma lacD_pos_alg (K : ℕ) : ∀ d ∈ lacD K, 0 < d ∧ IsAlgebraic ℚ d := by
  intro d hd
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
  refine ⟨pow_pos qL_pos j, ?_⟩
  have h := isAlgebraic_natCast (R := ℚ) (A := ℝ) ((10 ^ 6) ^ j)
  rw [qL]
  exact_mod_cast h

/-- Plane Delsarte bound for the lacunary set. -/
theorem plane_delsarte {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) {c : ℝ}
    (hc : 0 < c)
    (hfreq : ∃ᶠ T in atTop, ENNReal.ofReal c * volume (cube 2 T) ≤ volume (A ∩ cube 2 T))
    (K : ℕ) (hAv : ∀ x ∈ A, ∀ y ∈ A, dist x y ∉ lacD K) :
    4 * c / 9 * (3 / 2 : ℝ) ^ K ≤ 1 := by
  have hq1 : 1 ≤ qL := by rw [qL_eq]; norm_num
  obtain ⟨T, hTdens, hTge⟩ := (hfreq.and_eventually (eventually_ge_atTop (qL ^ K + 1))).exists
  have hT : 0 < T := by linarith [pow_pos qL_pos K]
  set L : ℝ := 3 * T with hL_def
  have hL : 0 < L := by positivity
  set B := A ∩ cube 2 T with hB_def
  have hBm : MeasurableSet B := hA.inter (cube_measurable T)
  have hBT : B ⊆ cube 2 T := inter_subset_right
  set E := torusSet L B with hE_def
  have hEm : MeasurableSet E := torusSet_measurable L hBm
  have haE : 4 * c / 9 ≤ (volume E).toReal := by
    have hvol := volume_torusSet hL (by linarith) hBm hBT
    have hlow : ENNReal.ofReal (4 * c / 9) ≤ volume E := by
      rw [hE_def, hvol]
      calc ENNReal.ofReal (4 * c / 9) = ENNReal.ofReal (L ^ 2)⁻¹ * (ENNReal.ofReal c *
            ENNReal.ofReal ((2 * T) ^ 2)) := by
            rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hL_def]
            field_simp
            ring
        _ ≤ ENNReal.ofReal (L ^ 2)⁻¹ * volume B := by
            rw [← volume_cube2 hT.le]
            exact mul_le_mul_right hTdens _
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hlow
  have hd := torus_delsarte E hEm (fun j => qL ^ j / L) (fun j => (1 / 2) * (3 / 2 : ℝ) ^ j) K
    (fun j hj t => by
      have hjK : qL ^ j ≤ qL ^ K := pow_le_pow_right₀ hq1 hj.le
      exact torusSet_avoid hL (pow_pos qL_pos j) (by linarith) hBT
        (fun x hx y hy hxy => hAv x hx.1 y hy.1
          (hxy ▸ Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)) t)
    (fun n => by
      have hs : ∀ j, (qL ^ j / L) • xi n = qL ^ j • ((1 / L) • xi n) := fun j => by
        rw [smul_smul, div_eq_mul_one_div]
      simp only [hs]
      have := lacH_ge K ((1 / L) • xi n)
      rw [lacH] at this
      linarith)
  rw [weights_sum, add_sub_cancel] at hd
  have hpow : (0 : ℝ) ≤ (3 / 2) ^ K := by positivity
  nlinarith

/-- **Exponential lower bound.** Every colouring of the plane avoiding the `K` distances
`(10⁶)^j`, `j < K`, uses at least `(4/9)·(3/2)^K` colours. -/
theorem lacunary_chromatic (K k : ℕ) [NeZero k] (c : EuclideanSpace ℝ (Fin 2) → Fin k)
    (hc : ∀ x y, dist x y ∈ lacD K → c x ≠ c y) :
    4 / 9 * (3 / 2 : ℝ) ^ K ≤ k := by
  obtain ⟨A, hAm, hAd, hAn, hAu⟩ :=
    euclidean_transfer_set le_rfl (lacD K).countable_toSet (lacD_pos_alg K) c
      (fun x y hxy => hc x y hxy)
  obtain ⟨i, hi⟩ := exists_dense_class hAm hAd hAn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have h := plane_delsarte (hAm i) (one_div_pos.mpr hk0) hi K (fun x hx y hy => hAu i x hx y hy)
  have h2 : 4 * (1 / (k : ℝ)) / 9 * (3 / 2) ^ K * k = 4 / 9 * (3 / 2) ^ K := by
    field_simp
  nlinarith

/-- No colouring with fewer than `(4/9)·(3/2)^K` colours avoids `D_K`. -/
theorem lacunary_no_coloring (K k : ℕ) (hk : (k : ℝ) < 4 / 9 * (3 / 2 : ℝ) ^ K) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, ∀ x y, dist x y ∈ lacD K → c x ≠ c y := by
  rintro ⟨c, hc⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact (c 0).elim0
  · have : NeZero k := ⟨hk0.ne'⟩
    linarith [lacunary_chromatic K k c hc]

/-- **Erdős #706, negative answer.** For every `C` and `e` there is a `K`-element set `D` of
positive algebraic (indeed integer) distances such that no colouring of the plane with at most
`C·K^e` colours avoids `D`. So `L(K)` is not bounded by any polynomial in `K`. -/
theorem erdos706_not_polynomial (C : ℝ) (e : ℕ) :
    ∃ K : ℕ, ∃ D : Finset ℝ, D.card = K ∧ (∀ d ∈ D, 0 < d ∧ IsAlgebraic ℚ d) ∧
      ∀ k : ℕ, (k : ℝ) ≤ C * (K : ℝ) ^ e →
        ¬ ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, ∀ x y, dist x y ∈ D → c x ≠ c y := by
  have hC : 0 < |C| + 1 := by positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 3 / 2)
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < 4 / (9 * (|C| + 1))))).exists
  refine ⟨K, lacD K, lacD_card K, lacD_pos_alg K, fun k hk => lacunary_no_coloring K k ?_⟩
  have hpow : (0 : ℝ) < (3 / 2) ^ K := by positivity
  have hKe : (0 : ℝ) ≤ (K : ℝ) ^ e := by positivity
  rw [div_lt_div_iff₀ hpow (by positivity)] at hK
  have h1 : C * (K : ℝ) ^ e ≤ (|C| + 1) * (K : ℝ) ^ e :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hKe
  nlinarith

end
end OAI.Soifer
