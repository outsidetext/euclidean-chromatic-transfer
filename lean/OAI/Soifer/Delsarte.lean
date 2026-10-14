import OAI.Soifer.Torus

/-!
# Delsarte bound on the torus

If `E ⊆ (ℝ/ℤ)²` has measure `α` and avoids the torus radii `ρ_j` (`j < J`) in every direction,
and `h(ξ) = 1 + Σ_j v_j Re σ̂(ρ_j ξ) ≥ 0` at all integer frequencies, then
`α = Σ_n |ĝ_n|² h(ξ_n) ≥ |ĝ_0|² h(0) = α² (1 + Σ_j v_j)`, so `α (1 + Σ_j v_j) ≤ 1`.
Also: the Taylor lower bound `Re σ̂(ξ) ≥ 1 - 2π²‖ξ‖²`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set UnitAddTorus ComplexConjugate
open OAI.EuclideanFiveColor

local instance delsarteMS : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance delsarteProb : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance delsarteHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- Taylor lower bound for the circle symbol. -/
lemma re_circleSymbol_ge (ξ : ℂ) : 1 - 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤ (circleSymbol ξ).re := by
  have h := integral_re (phase_integrable ξ)
  simp only [RCLike.re_to_complex] at h
  rw [circleSymbol, ← h]
  have hc : ∫ _t, (1 - 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) ∂angularMeasure =
      1 - 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
    simp only [integral_const, probReal_univ, one_smul]
  rw [← hc]
  have hi : Integrable (fun t => (planePhase (direction t) ξ).re) angularMeasure := by
    simpa only [RCLike.re_to_complex] using (phase_integrable ξ).re
  refine integral_mono (integrable_const _) hi (fun t => ?_)
  simp only [planePhase, Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
  have hin := abs_real_inner_le_norm (direction t) ξ
  rw [direction_norm, one_mul] at hin
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * inner ℝ (direction t) ξ)
  have h2 : (inner ℝ (direction t) ξ) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hin 2
  have h3 : (2 * Real.pi * inner ℝ (direction t) ξ) ^ 2 / 2 =
      2 * Real.pi ^ 2 * (inner ℝ (direction t) ξ) ^ 2 := by ring
  rw [h3] at h1
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

/-- **Torus Delsarte bound.** -/
theorem torus_delsarte (E : Set Tor) (hE : MeasurableSet E) (ρ v : ℕ → ℝ) (J : ℕ)
    (havoid : ∀ j < J, ∀ t : Angles, ∀ θ ∈ E, θ + tp (ρ j • direction t) ∉ E)
    (hh : ∀ n : Fin 2 → ℤ,
      0 ≤ 1 + ∑ j ∈ Finset.range J, v j * (circleSymbol (ρ j • xi n)).re) :
    (volume E).toReal * (1 + ∑ j ∈ Finset.range J, v j) ≤ 1 := by
  classical
  set g : Tor → ℂ := E.indicator (fun _ => 1) with hgdef
  have hg := indicator_memLp E hE
  set α := (volume E).toReal with hαdef
  set w := fun n => ‖mFourierCoeff g n‖ ^ 2 with hwdef
  have hw : HasSum w α := by
    have h := hasSum_wt hg
    have he : (fun θ => ‖g θ‖ ^ 2) = E.indicator (fun _ => (1 : ℝ)) := by
      funext θ
      by_cases h : θ ∈ E <;> simp [g, h]
    rw [he, integral_indicator_const _ hE, smul_eq_mul, mul_one] at h
    exact h
  have hw0 : w 0 = α ^ 2 := by
    have : mFourierCoeff g 0 = (α : ℂ) := by
      simp only [mFourierCoeff, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul, g]
      rw [integral_indicator_const _ hE, Measure.real, Complex.real_smul, mul_one]
    simp only [w, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hj : ∀ j ∈ Finset.range J,
      HasSum (fun n => v j * (w n * (circleSymbol (ρ j • xi n)).re)) (v j * 0) := by
    intro j hj
    refine HasSum.mul_left _ (circle_sum_zero hg _ ?_)
    intro t θ
    by_cases h1 : θ ∈ E
    · have := havoid j (Finset.mem_range.mp hj) t θ h1
      rw [Set.indicator_of_notMem this, mul_zero]
    · rw [Set.indicator_of_notMem h1, map_zero, zero_mul]
  have htot := hw.add (hasSum_sum hj)
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at htot
  have hfun : (fun n => w n + ∑ j ∈ Finset.range J, v j * (w n * (circleSymbol (ρ j • xi n)).re)) =
      fun n => w n * (1 + ∑ j ∈ Finset.range J, v j * (circleSymbol (ρ j • xi n)).re) := by
    funext n
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun] at htot
  have hle := le_hasSum htot 0 (fun n _ => mul_nonneg (sq_nonneg _) (hh n))
  have hx : xi 0 = 0 := by simp [xi]
  simp only [hx, smul_zero, circleSymbol_zero, Complex.one_re, mul_one, hw0] at hle
  have hα0 : 0 ≤ α := ENNReal.toReal_nonneg
  rcases hα0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; norm_num
  · nlinarith

end
end OAI.Soifer
