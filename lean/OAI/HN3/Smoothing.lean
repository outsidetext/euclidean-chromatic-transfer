import OAI.HN3.Rigidity

/-!
# Vector-window smoothing over the real algebraic line

A version of OpenAI's `smoothed_tendsto` in which the scalar window `φ t • U t v` is replaced
by `U t (Φ t)` for a uniformly continuous, boundedly supported vector window `Φ`.
-/

namespace OAI

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace HN3
open PlaneFiveColor.InvariantMean

section VectorSmoothing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : PlaneFiveColor.InvariantMean.AF → H ≃ₗᵢ[ℝ] H)

lemma vwindow_support (Φ : ℝ → H) {N : ℕ} (hs : ∀ t : ℝ, (N : ℝ) < |t| → Φ t = 0) :
    ∀ t : PlaneFiveColor.InvariantMean.AF, (N : ℝ) < |(t : ℝ)| → S t (Φ t) = 0 := by
  intro t ht
  rw [hs t ht, map_zero]

lemma vwindow_bound (Φ : ℝ → H) {B : ℝ} (hb : ∀ t, ‖Φ t‖ ≤ B) :
    ∀ t : PlaneFiveColor.InvariantMean.AF, ‖S t (Φ t)‖ ≤ B := by
  intro t
  rw [(S t).norm_map]
  exact hb t

/-- The invariant-mean integral of `t ↦ S t (Φ t)` over the real algebraic numbers. -/
def vsmoothed (Φ : ℝ → H) {N : ℕ} {B : ℝ} (hs : ∀ t : ℝ, (N : ℝ) < |t| → Φ t = 0)
    (hb : ∀ t, ‖Φ t‖ ≤ B) : H :=
  weakIntegral (fun t => S t (Φ t)) (vwindow_support S Φ hs) (vwindow_bound S Φ hb)

theorem vsmoothed_translation_bound
    (hu : ∀ s t v, S s (S t v) = S (s + t) v)
    (Φ : ℝ → H) {N : ℕ} {B C : ℝ} (hs : ∀ t : ℝ, (N : ℝ) < |t| → Φ t = 0)
    (hb : ∀ t, ‖Φ t‖ ≤ B) (s : PlaneFiveColor.InvariantMean.AF) (hs1 : |(s : ℝ)| ≤ 1)
    (hC : 0 ≤ C) (hd : ∀ t : PlaneFiveColor.InvariantMean.AF, ‖Φ ((t - s : PlaneFiveColor.InvariantMean.AF) : ℝ) - Φ t‖ ≤ C) :
    ‖S s (vsmoothed S Φ hs hb) - vsmoothed S Φ hs hb‖ ≤
      (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * C := by
  let h : PlaneFiveColor.InvariantMean.AF → H := fun t => S t (Φ t)
  let j : PlaneFiveColor.InvariantMean.AF → H := fun t => S t (Φ ((t - s : PlaneFiveColor.InvariantMean.AF) : ℝ))
  have hh := vwindow_support S Φ hs
  have bh := vwindow_bound S Φ hb
  have hj : ∀ t : PlaneFiveColor.InvariantMean.AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → j t = 0 := by
    intro t ht
    change S t (Φ ((t - s : PlaneFiveColor.InvariantMean.AF) : ℝ)) = 0
    rw [hs _ (by
      push_cast at ht ⊢
      have := abs_sub_abs_le_abs_sub (t : ℝ) (s : ℝ)
      linarith), map_zero]
  have bj : ∀ t, ‖j t‖ ≤ B := by
    intro t
    change ‖S t _‖ ≤ B
    rw [(S t).norm_map]; exact hb _
  have dh : ∀ t : PlaneFiveColor.InvariantMean.AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → j t - h t = 0 := by
    intro t ht
    rw [hj t ht]
    change 0 - S t (Φ t) = 0
    rw [hh t (by push_cast at ht; linarith), sub_self]
  have db : ∀ t, ‖j t - h t‖ ≤ C := by
    intro t
    change ‖S t (Φ _) - S t (Φ t)‖ ≤ C
    rw [← map_sub, (S t).norm_map]
    exact hd t
  have kh : ∀ t : PlaneFiveColor.InvariantMean.AF, (N : ℝ) < |(t : ℝ)| → S s (h t) = 0 := by
    intro t ht
    change S s (S t (Φ t)) = 0
    rw [hs t ht, map_zero, map_zero]
  have kb : ∀ t, ‖S s (h t)‖ ≤ B := by
    intro t
    rw [(S s).norm_map]
    exact bh t
  have je : ∀ t, j t = S s (h (t + (-s))) := by
    intro t
    simp only [j, h, hu, sub_eq_add_neg]
    congr 1
    abel
  have kjs : ∀ t : PlaneFiveColor.InvariantMean.AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → S s (h (t + (-s))) = 0 := by
    intro t ht
    rw [← je]
    exact hj t ht
  have kjb : ∀ t, ‖S s (h (t + (-s)))‖ ≤ B := by
    intro t
    rw [← je]
    exact bj t
  have ji : weakIntegral j hj bj = S s (weakIntegral h hh bh) := by
    calc
      _ = weakIntegral (fun t => S s (h (t + (-s)))) kjs kjb :=
        weakIntegral_congr _ _ _ _ _ _ je
      _ = weakIntegral (fun t => S s (h t)) kh kb :=
        weakIntegral_shift (fun t => S s (h t)) (-s) kh kb kjs kjb
      _ = S s (weakIntegral h hh bh) :=
        weakIntegral_map (S s).toContinuousLinearEquiv.toContinuousLinearMap h hh bh kh kb
  have di := weakIntegral_sub j h hj bj hh bh dh db
  change ‖S s (weakIntegral h hh bh) - weakIntegral h hh bh‖ ≤ _
  rw [← ji, ← di]
  exact weakIntegral_norm_bound _ dh db hC

/-- A uniformly continuous compactly supported vector window gives a vector that is strongly
continuous for the discrete line representation. -/
theorem vsmoothed_tendsto
    (hu : ∀ s t v, S s (S t v) = S (s + t) v)
    (Φ : ℝ → H) (hc : UniformContinuous Φ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → Φ t = 0) (hb : ∀ t, ‖Φ t‖ ≤ B) :
    Tendsto (fun s : PlaneFiveColor.InvariantMean.AF => S s (vsmoothed S Φ hs hb)) (𝓝 0)
      (𝓝 (vsmoothed S Φ hs hb)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let Q : ℝ := (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hp : 0 < ε / (Q + 1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hc _ hp
  have hnorm : ∀ᶠ s : PlaneFiveColor.InvariantMean.AF in 𝓝 0, ‖s‖ < min δ 1 :=
    (show Tendsto (fun s : PlaneFiveColor.InvariantMean.AF => ‖s‖) (𝓝 0) (𝓝 (0 : ℝ)) by
      simpa using continuous_norm.tendsto (0 : PlaneFiveColor.InvariantMean.AF)).eventually
        (eventually_lt_nhds (lt_min hδ zero_lt_one))
  filter_upwards [hnorm] with s hsn
  have hsδ : |(s : ℝ)| < δ := (lt_min_iff.mp hsn).1
  have hs1 : |(s : ℝ)| ≤ 1 := le_of_lt (lt_min_iff.mp hsn).2
  have hdiff : ∀ t : PlaneFiveColor.InvariantMean.AF,
      ‖Φ ((t - s : PlaneFiveColor.InvariantMean.AF) : ℝ) - Φ t‖ ≤ ε / (Q + 1) := by
    intro t
    apply le_of_lt
    rw [← dist_eq_norm]
    apply hd
    rw [Real.dist_eq]
    push_cast
    rw [show (t : ℝ) - (s : ℝ) - (t : ℝ) = -(s : ℝ) by ring, abs_neg]
    exact hsδ
  have hbound := vsmoothed_translation_bound S hu Φ hs hb s hs1 hp.le hdiff
  rw [dist_zero_right]
  apply hbound.trans_lt
  have hr : Q * (ε / (Q + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < Q + 1)]
    nlinarith
  exact hr

end VectorSmoothing

end HN3
end
end OAI
