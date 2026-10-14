import OAI.Soifer.Erdos706

/-!
# Quantitative Soifer theorem

The lacunary certificate of `Lacunary.lean` works for every ratio `q ≥ 10⁶` (the only use of
`q` is `μ² q ≥ 1` with `μ = 3/2000`). With `q = 2²⁰` this gives: every `k`-colouring of the
plane has a monochromatic distance `2^i` with `i ≤ 20 (2 ⌊log₂ 9k⌋ + 2)`, i.e. a monochromatic
power of two at most `(9k)^40 · 2^40`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set
open OAI.EuclideanFiveColor OAI.HNN

local instance quantMS : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance quantProb : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ### The certificate for a general ratio -/

/-- The lacunary Delsarte sum with ratio `q`. -/
def lacHq (q : ℝ) (K : ℕ) (ξ : ℂ) : ℝ :=
  ∑ j ∈ Finset.range K, (1 / 2) * (3 / 2 : ℝ) ^ j * (circleSymbol (q ^ j • ξ)).re

lemma lacHq_zero (q : ℝ) (ξ : ℂ) : lacHq q 0 ξ = 0 := by simp [lacHq]

lemma lacHq_succ (q : ℝ) (K : ℕ) (ξ : ℂ) :
    lacHq q (K + 1) ξ = (1 / 2) * (circleSymbol ξ).re + (3 / 2) * lacHq q K (q • ξ) := by
  rw [lacHq, Finset.sum_range_succ', lacHq, Finset.mul_sum]
  simp only [pow_zero, mul_one, one_smul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show q ^ (j + 1) • ξ = q ^ j • q • ξ by rw [pow_succ, mul_smul]]
  ring

/-- The induction invariant for ratio `q`. -/
structure LacInvQ (q : ℝ) (K : ℕ) : Prop where
  low : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 / 10 → -(1 / 2) ≤ lacHq q K ξ
  mid : ∀ ξ : ℂ, 1 / 10 < ‖ξ‖ → -(1 / 2) * (1 + 3 / 2 * 70 * (3 / 2000)) ≤ lacHq q K ξ
  high : ∀ i : ℕ, 1 ≤ i → ∀ ξ : ℂ, q ^ i / 10 < ‖ξ‖ →
    -(1 / 2) * (70 * (3 / 2000 : ℝ) ^ i) ≤ lacHq q K ξ

lemma lacInvQ_all {q : ℝ} (hq : 1000000 ≤ q) (K : ℕ) : LacInvQ q K := by
  have hq0 : 0 < q := by linarith
  have hnq : ∀ ξ : ℂ, ‖q • ξ‖ = q * ‖ξ‖ := fun ξ => by
    rw [norm_smul, Real.norm_of_nonneg hq0.le]
  induction K with
  | zero =>
    refine ⟨fun ξ _ => ?_, fun ξ _ => ?_, fun i _ ξ _ => ?_⟩ <;> rw [lacHq_zero]
    · norm_num
    · norm_num
    · have : (0 : ℝ) ≤ 70 * (3 / 2000 : ℝ) ^ i := by positivity
      linarith
  | succ K ih =>
    refine ⟨fun ξ hξ => ?_, fun ξ hξ => ?_, fun i hi ξ hξ => ?_⟩
    · rw [lacHq_succ]
      have h1 := re_circleSymbol_ge ξ
      have hpi := Real.pi_lt_d2
      have hpi0 := Real.pi_pos
      have hn2 : ‖ξ‖ ^ 2 ≤ 1 / 100 := by nlinarith [norm_nonneg ξ]
      have hp2 : Real.pi ^ 2 ≤ 3.15 ^ 2 := by nlinarith
      have hre : (0.8 : ℝ) ≤ (circleSymbol ξ).re := by nlinarith
      by_cases h2 : ‖q • ξ‖ ≤ 1 / 10
      · have := ih.low _ h2
        linarith
      · have := ih.mid _ (lt_of_not_ge h2)
        norm_num at this ⊢
        linarith
    · rw [lacHq_succ]
      have h1 : -1 ≤ (circleSymbol ξ).re := by
        have := re_ge_neg_norm (circleSymbol ξ)
        have := circleSymbol_norm_le_one ξ
        linarith
      have h2 := ih.high 1 le_rfl (q • ξ) (by
        rw [hnq, pow_one]
        nlinarith)
      rw [pow_one] at h2
      linarith
    · rw [lacHq_succ]
      have hqi : 0 < q ^ i := pow_pos hq0 i
      have h2 := ih.high (i + 1) (by omega) (q • ξ) (by
        rw [hnq, pow_succ]
        nlinarith [mul_lt_mul_of_pos_left hξ hq0])
      set p : ℝ := (3 / 2000 : ℝ) ^ i with hp
      have hp0 : 0 < p := by positivity
      have hpq : p ^ 2 * q ^ i = ((3 / 2000) ^ 2 * q) ^ i := by
        rw [hp, ← pow_mul, mul_comm i 2, pow_mul, ← mul_pow]
      have hpq1 : 1 ≤ p ^ 2 * q ^ i := by
        rw [hpq]
        exact one_le_pow₀ (by nlinarith)
      have hs := circleSymbol_sq_bound ξ
      have hs1 : 400 / (1 + ‖ξ‖) ≤ 4000 / q ^ i := by
        rw [div_le_div_iff₀ (by positivity) hqi]
        nlinarith [norm_nonneg ξ]
      have hs2 : 4000 / q ^ i ≤ 4000 * p ^ 2 := by
        rw [div_le_iff₀ hqi]
        nlinarith
      set B : ℝ := 70 * p * (1 - 3 / 2 * (3 / 2000)) with hB
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      have hB2 : 4000 * p ^ 2 ≤ B ^ 2 := by rw [hB]; nlinarith
      have hnorm : ‖circleSymbol ξ‖ ≤ B := by nlinarith [norm_nonneg (circleSymbol ξ)]
      have hre := re_ge_neg_norm (circleSymbol ξ)
      rw [pow_succ, ← hp] at h2
      rw [hB] at hnorm
      linarith

theorem lacHq_ge {q : ℝ} (hq : 1000000 ≤ q) (K : ℕ) (ξ : ℂ) : -1 ≤ lacHq q K ξ := by
  by_cases h : ‖ξ‖ ≤ 1 / 10
  · have := (lacInvQ_all hq K).low ξ h
    linarith
  · have := (lacInvQ_all hq K).mid ξ (lt_of_not_ge h)
    norm_num at this
    linarith

/-! ### Plane bound for a general ratio -/

/-- The distance set `{q^j : j < K}`. -/
def lacDq (q : ℕ) (K : ℕ) : Finset ℝ := (Finset.range K).image (fun j => (q : ℝ) ^ j)

lemma lacDq_pos_alg {q : ℕ} (hq : 0 < q) (K : ℕ) : ∀ d ∈ lacDq q K, 0 < d ∧ IsAlgebraic ℚ d := by
  intro d hd
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
  refine ⟨pow_pos (by exact_mod_cast hq) j, ?_⟩
  have h := isAlgebraic_natCast (R := ℚ) (A := ℝ) (q ^ j)
  exact_mod_cast h

theorem plane_delsarte_q {q : ℕ} (hq : 1000000 ≤ q) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : MeasurableSet A) {c : ℝ} (hc : 0 < c)
    (hfreq : ∃ᶠ T in atTop, ENNReal.ofReal c * volume (cube 2 T) ≤ volume (A ∩ cube 2 T))
    (K : ℕ) (hAv : ∀ x ∈ A, ∀ y ∈ A, dist x y ∉ lacDq q K) :
    4 * c / 9 * (3 / 2 : ℝ) ^ K ≤ 1 := by
  have hqR : (1000000 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨T, hTdens, hTge⟩ :=
    (hfreq.and_eventually (eventually_ge_atTop ((q : ℝ) ^ K + 1))).exists
  have hT : 0 < T := by linarith [pow_pos hq0 K]
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
  have hd := torus_delsarte E hEm (fun j => (q : ℝ) ^ j / L) (fun j => (1 / 2) * (3 / 2 : ℝ) ^ j) K
    (fun j hj t => by
      have hjK : (q : ℝ) ^ j ≤ (q : ℝ) ^ K := pow_le_pow_right₀ hq1 hj.le
      exact torusSet_avoid hL (pow_pos hq0 j) (by linarith) hBT
        (fun x hx y hy hxy => hAv x hx.1 y hy.1
          (hxy ▸ Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)) t)
    (fun n => by
      have hs : ∀ j, ((q : ℝ) ^ j / L) • xi n = (q : ℝ) ^ j • ((1 / L) • xi n) := fun j => by
        rw [smul_smul, div_eq_mul_one_div]
      simp only [hs]
      have := lacHq_ge hqR K ((1 / L) • xi n)
      rw [lacHq] at this
      linarith)
  rw [weights_sum, add_sub_cancel] at hd
  have hpow : (0 : ℝ) ≤ (3 / 2) ^ K := by positivity
  nlinarith

/-- `lacunary_chromatic` for any ratio `q ≥ 10⁶`. -/
theorem lacunary_chromatic_q {q : ℕ} (hq : 1000000 ≤ q) (K k : ℕ) [NeZero k]
    (c : EuclideanSpace ℝ (Fin 2) → Fin k) (hc : ∀ x y, dist x y ∈ lacDq q K → c x ≠ c y) :
    4 / 9 * (3 / 2 : ℝ) ^ K ≤ k := by
  obtain ⟨A, hAm, hAd, hAn, hAu⟩ :=
    euclidean_transfer_set le_rfl (lacDq q K).countable_toSet
      (lacDq_pos_alg (by omega) K) c (fun x y hxy => hc x y hxy)
  obtain ⟨i, hi⟩ := exists_dense_class hAm hAd hAn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have h := plane_delsarte_q hq (hAm i) (one_div_pos.mpr hk0) hi K
    (fun x hx y hy => hAu i x hx y hy)
  have h2 : 4 * (1 / (k : ℝ)) / 9 * (3 / 2) ^ K * k = 4 / 9 * (3 / 2) ^ K := by
    field_simp
  nlinarith

/-! ### Quantitative Soifer -/

/-- **Quantitative Soifer theorem.** Every `k`-colouring of the plane has two points of the
same colour at distance `2^i` for some `i ≤ 20 (2 ⌊log₂ 9k⌋ + 2)`. -/
theorem soifer_quantitative {k : ℕ} [NeZero k] (c : EuclideanSpace ℝ (Fin 2) → Fin k) :
    ∃ i : ℕ, i ≤ 20 * (Nat.log 2 (9 * k) * 2 + 2) ∧
      ∃ x y, dist x y = (2 : ℝ) ^ i ∧ c x = c y := by
  by_contra h
  push Not at h
  set m := Nat.log 2 (9 * k) + 1 with hm
  set K := Nat.log 2 (9 * k) * 2 + 2 with hK
  have hKm : K = 2 * m := by omega
  have hc : ∀ x y, dist x y ∈ lacDq (2 ^ 20) K → c x ≠ c y := by
    intro x y hxy
    obtain ⟨j, hj, hjd⟩ := Finset.mem_image.mp hxy
    have hjK := Finset.mem_range.mp hj
    have hd : dist x y = (2 : ℝ) ^ (20 * j) := by
      rw [← hjd, pow_mul]
      push_cast
      ring
    exact h (20 * j) (by omega) x y hd
  have hbound := lacunary_chromatic_q (by norm_num) K k c hc
  have hlog : 9 * k < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) (9 * k)
  have hlogR : (9 * k : ℝ) < 2 ^ m := by exact_mod_cast hlog
  have hpow : (2 : ℝ) ^ m ≤ (3 / 2 : ℝ) ^ K := by
    rw [hKm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  nlinarith

end
end OAI.Soifer
