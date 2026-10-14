import OAI.HN3.IndepLineMain
import OAI.HN3.Sampling

/-!
# The measurable field of the independent-set model

`fieldV L x = Ext3 (pv L) x` takes values in `[0,1]`, is orthogonal to its unit translates, and
has the same mean as the indicator `1[0 ∈ I]`. A jointly measurable clamped version gives a
field `H : (ℂ × ℝ) × ISpace → [0,1]`.
-/

set_option linter.unusedSectionVars false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HN3
namespace Indep
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable (L : State ISpace)

def oneV : Hilbert L := (memLp_const (1 : ℂ)).toLp (fun _ : ISpace => (1 : ℂ))

lemma oneV_ae : oneV L =ᵐ[measure L] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _

lemma T_oneV (a : V) : T L a (oneV L) = oneV L := by
  rw [translation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (oneV L) (trans_preserving L a),
    (trans_preserving L a).quasiMeasurePreserving.ae (oneV_ae L), oneV_ae L] with η h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

lemma oneV_plane : oneV L ∈ space (A := E) (planeRep L) := by
  change Tendsto (fun a : E => op (planeRep L) a (oneV L)) (𝓝 0) (𝓝 (oneV L))
  simp only [planeRep_op, T_oneV]
  exact tendsto_const_nhds

lemma oneV_line : oneV L ∈ space (A := AF) (lineRep L) := by
  change Tendsto (fun a : AF => op (lineRep L) a (oneV L)) (𝓝 0) (𝓝 (oneV L))
  simp only [lineRep_op, T_oneV]
  exact tendsto_const_nhds

lemma gv_range : ∀ᵐ η ∂measure L,
    ((gv L) η).im = 0 ∧ 0 ≤ ((gv L) η).re ∧ ((gv L) η).re ≤ 1 := by
  apply projection_range (measure L) (planeRep L) (fun z : E => trans (z, 0))
    (fun z => trans_preserving L (z, 0)) (fun z v => rfl)
  filter_upwards [color_ae L] with η h
  rw [h]
  dsimp [colorValue]
  split_ifs <;> norm_num

lemma pv_range : ∀ᵐ η ∂measure L,
    ((pv L) η).im = 0 ∧ 0 ≤ ((pv L) η).re ∧ ((pv L) η).re ≤ 1 :=
  projection_range (measure L) (lineRep L) (fun t : AF => trans (0, t))
    (fun t => trans_preserving L (0, t)) (fun t v => rfl) _ (gv_range L)

/-- The label fields on all of `ℂ × ℝ`. -/
def fieldV (x : ℂ × ℝ) : Hilbert L := Ext3 L (pv L) x

lemma fieldV_continuous : Continuous (fieldV L) :=
  Ext3_continuous L (pv_plane L) (pv_line L)

lemma fieldV_alg (a : V) : fieldV L (emb a) = T L a (pv L) :=
  Ext3_eq L (pv_plane L) (pv_line L) a

lemma fieldV_range (x : ℂ × ℝ) : ∀ᵐ η ∂measure L,
    (fieldV L x η).im = 0 ∧ 0 ≤ (fieldV L x η).re ∧ (fieldV L x η).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero (fieldV L x) = fieldV L x := by
    refine emb_dense.induction_on x (isClosed_eq
      ((clamp_lipschitz.continuous_compLp clamp_zero).comp (fieldV_continuous L))
      (fieldV_continuous L)) ?_
    intro a
    rw [fieldV_alg, translation_apply]
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero
        (Lp.compMeasurePreserving (trans a) (trans_preserving L a) (pv L)),
      Lp.coeFn_compMeasurePreserving (pv L) (trans_preserving L a),
      (trans_preserving L a).quasiMeasurePreserving.ae (pv_range L)] with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
    exact clamp_eq h3
  have ha := clamp_lipschitz.coeFn_compLp clamp_zero (fieldV L x)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clamp_range _

lemma fieldV_unit_correlation (x y : ℂ × ℝ) (hy : ‖y.1‖ ^ 2 + y.2 ^ 2 = 1) :
    ⟪fieldV L x, fieldV L (x + y)⟫_ℂ = 0 := by
  rw [fieldV, fieldV, Ext3_inner L (pv_plane L) (pv_line L) (pv_plane L)
    (pv_line L)]
  exact pv_unit_correlation L y hy

/-! ### Means -/

/-- Pairing with the constant one is the integral. -/
lemma inner_oneV (v : Hilbert L) : ⟪oneV L, v⟫_ℂ = ∫ η, v η ∂measure L := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneV_ae L] with η h
  simp [h]

lemma inner_oneV_pv : ⟪oneV L, pv L⟫_ℂ = ⟪oneV L, colorVector L⟫_ℂ := by
  simp only [pv, gv]
  rw [← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (oneV_line L),
    ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (oneV_plane L)]

lemma fieldV_mean (x : ℂ × ℝ) : ⟪oneV L, fieldV L x⟫_ℂ = ⟪oneV L, colorVector L⟫_ℂ := by
  refine emb_dense.induction_on x (isClosed_eq (continuous_const.inner (fieldV_continuous L))
    continuous_const) ?_
  intro a
  rw [fieldV_alg, ← inner_oneV_pv]
  conv_lhs => rw [← T_oneV L a]
  exact Unitary.inner_map_map (translation L a) _ _

lemma integrable_L2 (v : Hilbert L) : Integrable (fun η => v η) (measure L) :=
  (Lp.memLp v).integrable (by norm_num)

/-- The jointly measurable `[0,1]`-valued field. -/
lemma exists_label_field : ∃ H : (ℂ × ℝ) × ISpace → ℝ, Measurable H ∧
    (∀ p, 0 ≤ H p ∧ H p ≤ 1) ∧
    (∀ x : ℂ × ℝ, ∫ η, H (x, η) ∂measure L = ∫ η, (colorValue η).re ∂measure L) ∧
    (∀ x y : ℂ × ℝ, ‖y.1‖ ^ 2 + y.2 ^ 2 = 1 →
      ∀ᵐ η ∂measure L, H (x, η) * H (x + y, η) = 0) := by
  obtain ⟨F, hm, hae⟩ := exists_measurable_field (measure L) (fieldV L) (fieldV_continuous L)
  have hH : ∀ x : ℂ × ℝ, ∀ᵐ η ∂measure L, (clamp (F (x, η))).re = (fieldV L x η).re := by
    intro x
    filter_upwards [hae x, fieldV_range L x] with η h1 h2
    change F (x, η) = _ at h1
    rw [h1, clamp_eq h2]
  refine ⟨fun p => (clamp (F p)).re, ?_, fun p => ⟨(clamp_range _).2.1, (clamp_range _).2.2⟩, ?_, ?_⟩
  · exact Complex.continuous_re.measurable.comp (clamp_lipschitz.continuous.measurable.comp hm)
  · intro x
    have h1 : ∫ η, (clamp (F (x, η))).re ∂measure L = ∫ η, (fieldV L x η).re ∂measure L :=
      integral_congr_ae (hH x)
    have h2 : ∫ η, (colorValue η).re ∂measure L = ∫ η, (colorVector L η).re ∂measure L := by
      apply integral_congr_ae
      filter_upwards [color_ae L] with η h
      rw [h]
    rw [h1, h2]
    have e1 : ∫ η, (fieldV L x η).re ∂measure L = (∫ η, fieldV L x η ∂measure L).re :=
      integral_re (integrable_L2 L (fieldV L x))
    have e2 : ∫ η, (colorVector L η).re ∂measure L = (∫ η, colorVector L η ∂measure L).re :=
      integral_re (integrable_L2 L (colorVector L))
    rw [e1, e2, ← inner_oneV, ← inner_oneV, fieldV_mean]
  · intro x y hy
    have hz := positive_orthogonal (measure L) (fieldV L x) (fieldV L (x + y))
      ((fieldV_range L x).mono fun _ h => ⟨h.1, h.2.1⟩)
      ((fieldV_range L (x + y)).mono fun _ h => ⟨h.1, h.2.1⟩)
      (fieldV_unit_correlation L x y hy)
    filter_upwards [hH x, hH (x + y), hz] with η h1 h2 h3
    rw [h1, h2]
    exact h3

end Indep
end HN3
end
end OAI
