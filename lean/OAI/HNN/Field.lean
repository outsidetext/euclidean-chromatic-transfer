import OAI.HNN.Odd

/-!
# Measurable label fields on the real model

The extended orbits `x ↦ Ext (pv i) x` are continuous fields with values in `[0,1]`, summing to
one, and orthogonal at every displacement of forbidden length. Measurable versions give label
fields `H i : X m r × Ω → ℝ`.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HNN
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable {m r : ℕ} {D : Set ℝ} {k : ℕ} (ω : Space m r D k)

/-- Zero correlation of all label vectors at all real vectors of forbidden length. -/
def CorrZero : Prop :=
  ∀ i : Fin k, ∀ y : X m r, ∀ d ∈ D, usq y = d ^ 2 → ⟪pv ω i, Ext ω (pv ω i) y⟫_ℂ = 0

/-- The correlation statement holds in every dimension `2m + r ≥ 2`, for algebraic positive
forbidden lengths. -/
theorem corrZero (hm : 0 < m) (hr : r ≤ 1) (hD : ∀ d ∈ D, 0 < d ∧ IsAlgebraic ℚ d)
    (ω : Space m r D k) : CorrZero ω := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hr with rfl | rfl
  · exact fun i y d hd hy => pv_corr_even ω i hd (hD d hd).2 (hD d hd).1 y hy
  · exact fun i y d hd hy => pv_corr_odd ω hm i hd (hD d hd).2 (hD d hd).1 y hy

def fieldV (i : Fin k) (x : X m r) : Hilbert ω := Ext ω (pv ω i) x

variable (hr : r ≤ 1)
include hr

lemma fieldV_continuous (i : Fin k) : Continuous (fieldV ω i) :=
  Ext_continuous ω hr (pv_plane ω i) (pv_line ω i)

lemma fieldV_alg (i : Fin k) (a : V m r) : fieldV ω i (emb a) = T ω a (pv ω i) :=
  Ext_eq ω hr (pv_plane ω i) (pv_line ω i) a

lemma fieldV_sum (x : X m r) : ∑ i : Fin k, fieldV ω i x = oneV ω := by
  refine emb_dense.induction_on x (isClosed_eq (continuous_finsetSum _
    (fun i _ => fieldV_continuous ω hr i)) continuous_const) ?_
  intro a
  simp only [fieldV_alg ω hr, ← map_sum, pv_sum, T_oneV]

lemma fieldV_range (i : Fin k) (x : X m r) : ∀ᵐ η ∂measure ω,
    (fieldV ω i x η).im = 0 ∧ 0 ≤ (fieldV ω i x η).re ∧ (fieldV ω i x η).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero (fieldV ω i x) = fieldV ω i x := by
    refine emb_dense.induction_on x (isClosed_eq
      ((clamp_lipschitz.continuous_compLp clamp_zero).comp (fieldV_continuous ω hr i))
      (fieldV_continuous ω hr i)) ?_
    intro a
    rw [fieldV_alg ω hr, translation_apply]
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero
        (Lp.compMeasurePreserving (trans a) (trans_preserving ω a) (pv ω i)),
      Lp.coeFn_compMeasurePreserving (pv ω i) (trans_preserving ω a),
      (trans_preserving ω a).quasiMeasurePreserving.ae (pv_range ω i)] with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
    exact clamp_eq h3
  have ha := clamp_lipschitz.coeFn_compLp clamp_zero (fieldV ω i x)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clamp_range _

lemma fieldV_corr (hC : CorrZero ω) (i : Fin k) (x y : X m r) {d : ℝ} (hd : d ∈ D)
    (hy : usq y = d ^ 2) : ⟪fieldV ω i x, fieldV ω i (x + y)⟫_ℂ = 0 := by
  rw [fieldV, fieldV, Ext_inner ω hr (pv_plane ω i) (pv_line ω i) (pv_plane ω i) (pv_line ω i)]
  exact hC i y d hd hy

theorem exists_label_field (hC : CorrZero ω) : ∃ H : Fin k → X m r × Space m r D k → ℝ,
    (∀ i, Measurable (H i)) ∧
    (∀ x : X m r, ∀ᵐ η ∂measure ω, ∑ i, H i (x, η) = 1) ∧
    (∀ x y : X m r, ∀ d ∈ D, usq y = d ^ 2 →
      ∀ᵐ η ∂measure ω, ∀ i, H i (x, η) * H i (x + y, η) = 0) := by
  have hex (i : Fin k) := exists_measurable_field (measure ω) (fieldV ω i)
    (fieldV_continuous ω hr i)
  choose F hm hae using hex
  refine ⟨fun i p => (F i p).re, fun i => Complex.continuous_re.measurable.comp (hm i), ?_, ?_⟩
  · intro x
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin k => fieldV ω i x)
    rw [fieldV_sum ω hr] at hs
    filter_upwards [ae_all_iff.mpr (fun i => hae i x), hs, oneV_ae ω] with η he hs h1
    have hc : ∑ i : Fin k, F i (x, η) = 1 := by
      simp_rw [he]
      exact hs.symm.trans h1
    have hr' := congrArg Complex.re hc
    simpa only [map_sum, Complex.re_sum, Complex.one_re] using hr'
  · intro x y d hd hy
    apply ae_all_iff.mpr
    intro i
    have hz := positive_orthogonal (measure ω) (fieldV ω i x) (fieldV ω i (x + y))
      ((fieldV_range ω hr i x).mono fun _ h => ⟨h.1, h.2.1⟩)
      ((fieldV_range ω hr i (x + y)).mono fun _ h => ⟨h.1, h.2.1⟩)
      (fieldV_corr ω hr hC i x y hd hy)
    filter_upwards [hae i x, hae i (x + y), hz] with η h1 h2 h3
    simpa only [h1, h2] using h3

end HNN
end
end OAI
