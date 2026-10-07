import OAI.HN3.LineMain

/-!
# Measurable label fields on `ℂ × ℝ` and a sampled coloring

The fully continuous projections `pv i` give continuous fields `x ↦ Ext3 (pv i) x` with values
in `[0,1]`, summing to one, and orthogonal at every unit displacement. Measurable versions and
one good sample give a measurable coloring whose monochromatic unit pairs are null for any
direction measure.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HN3
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable (k : ℕ) (ω : Space k)

def oneV : Hilbert k ω := (memLp_const (1 : ℂ)).toLp (fun _ : Space k => (1 : ℂ))

lemma oneV_ae : oneV k ω =ᵐ[measure k ω] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _

lemma T_oneV (a : V) : T k ω a (oneV k ω) = oneV k ω := by
  rw [translation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (oneV k ω) (trans_preserving k ω a),
    (trans_preserving k ω a).quasiMeasurePreserving.ae (oneV_ae k ω), oneV_ae k ω] with η h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

lemma oneV_plane : oneV k ω ∈ space (A := E) (planeRep k ω) := by
  change Tendsto (fun a : E => op (planeRep k ω) a (oneV k ω)) (𝓝 0) (𝓝 (oneV k ω))
  simp only [planeRep_op, T_oneV]
  exact tendsto_const_nhds

lemma oneV_line : oneV k ω ∈ space (A := AF) (lineRep k ω) := by
  change Tendsto (fun a : AF => op (lineRep k ω) a (oneV k ω)) (𝓝 0) (𝓝 (oneV k ω))
  simp only [lineRep_op, T_oneV]
  exact tendsto_const_nhds

lemma color_sum : ∑ i : Fin k, colorVector k ω i = oneV k ω := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ) (colorVector k ω),
    ae_all_iff.mpr (color_ae k ω), oneV_ae k ω] with η h1 h2 h3
  rw [h1, h3]
  simp_rw [h2, colorValue]
  simp

lemma pv_sum : ∑ i : Fin k, pv k ω i = oneV k ω := by
  simp only [pv, gv]
  rw [← map_sum, ← map_sum, color_sum,
    Submodule.starProjection_eq_self_iff.mpr (oneV_plane k ω),
    Submodule.starProjection_eq_self_iff.mpr (oneV_line k ω)]

lemma gv_range (i : Fin k) : ∀ᵐ η ∂measure k ω,
    ((gv k ω i) η).im = 0 ∧ 0 ≤ ((gv k ω i) η).re ∧ ((gv k ω i) η).re ≤ 1 := by
  apply projection_range (measure k ω) (planeRep k ω) (fun z : E => trans k (z, 0))
    (fun z => trans_preserving k ω (z, 0)) (fun z v => rfl)
  filter_upwards [color_ae k ω i] with η h
  rw [h]
  dsimp [colorValue]
  split_ifs <;> norm_num

lemma pv_range (i : Fin k) : ∀ᵐ η ∂measure k ω,
    ((pv k ω i) η).im = 0 ∧ 0 ≤ ((pv k ω i) η).re ∧ ((pv k ω i) η).re ≤ 1 :=
  projection_range (measure k ω) (lineRep k ω) (fun t : AF => trans k (0, t))
    (fun t => trans_preserving k ω (0, t)) (fun t v => rfl) _ (gv_range k ω i)

/-- The label fields on all of `ℂ × ℝ`. -/
def fieldV (i : Fin k) (x : ℂ × ℝ) : Hilbert k ω := Ext3 k ω (pv k ω i) x

lemma fieldV_continuous (i : Fin k) : Continuous (fieldV k ω i) :=
  Ext3_continuous k ω (pv_plane k ω i) (pv_line k ω i)

lemma fieldV_alg (i : Fin k) (a : V) : fieldV k ω i (emb a) = T k ω a (pv k ω i) :=
  Ext3_eq k ω (pv_plane k ω i) (pv_line k ω i) a

lemma fieldV_sum (x : ℂ × ℝ) : ∑ i : Fin k, fieldV k ω i x = oneV k ω := by
  refine emb_dense.induction_on x (isClosed_eq (continuous_finsetSum _
    (fun i _ => fieldV_continuous k ω i)) continuous_const) ?_
  intro a
  simp only [fieldV_alg, ← map_sum, pv_sum, T_oneV]

lemma fieldV_range (i : Fin k) (x : ℂ × ℝ) : ∀ᵐ η ∂measure k ω,
    (fieldV k ω i x η).im = 0 ∧ 0 ≤ (fieldV k ω i x η).re ∧ (fieldV k ω i x η).re ≤ 1 := by
  have he : clamp_lipschitz.compLp clamp_zero (fieldV k ω i x) = fieldV k ω i x := by
    refine emb_dense.induction_on x (isClosed_eq
      ((clamp_lipschitz.continuous_compLp clamp_zero).comp (fieldV_continuous k ω i))
      (fieldV_continuous k ω i)) ?_
    intro a
    rw [fieldV_alg, translation_apply]
    apply Lp.ext
    filter_upwards [clamp_lipschitz.coeFn_compLp clamp_zero
        (Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) (pv k ω i)),
      Lp.coeFn_compMeasurePreserving (pv k ω i) (trans_preserving k ω a),
      (trans_preserving k ω a).quasiMeasurePreserving.ae (pv_range k ω i)] with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
    exact clamp_eq h3
  have ha := clamp_lipschitz.coeFn_compLp clamp_zero (fieldV k ω i x)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clamp_range _

lemma fieldV_unit_correlation (i : Fin k) (x y : ℂ × ℝ) (hy : ‖y.1‖ ^ 2 + y.2 ^ 2 = 1) :
    ⟪fieldV k ω i x, fieldV k ω i (x + y)⟫_ℂ = 0 := by
  rw [fieldV, fieldV, Ext3_inner k ω (pv_plane k ω i) (pv_line k ω i) (pv_plane k ω i)
    (pv_line k ω i)]
  exact pv_unit_correlation k ω i y hy

lemma exists_label_field : ∃ H : Fin k → (ℂ × ℝ) × Space k → ℝ,
    (∀ i, Measurable (H i)) ∧
    (∀ x : ℂ × ℝ, ∀ᵐ η ∂measure k ω, ∑ i, H i (x, η) = 1) ∧
    (∀ x y : ℂ × ℝ, ‖y.1‖ ^ 2 + y.2 ^ 2 = 1 →
      ∀ᵐ η ∂measure k ω, ∀ i, H i (x, η) * H i (x + y, η) = 0) := by
  have hex (i : Fin k) := exists_measurable_field (measure k ω) (fieldV k ω i)
    (fieldV_continuous k ω i)
  choose F hm hae using hex
  refine ⟨fun i p => (F i p).re, fun i => Complex.continuous_re.measurable.comp (hm i), ?_, ?_⟩
  · intro x
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin k => fieldV k ω i x)
    rw [fieldV_sum] at hs
    filter_upwards [ae_all_iff.mpr (fun i => hae i x), hs, oneV_ae k ω] with η he hs h1
    have hc : ∑ i : Fin k, F i (x, η) = 1 := by
      simp_rw [he]
      exact hs.symm.trans h1
    have hr := congrArg Complex.re hc
    simpa only [map_sum, Complex.re_sum, Complex.one_re] using hr
  · intro x y hy
    apply ae_all_iff.mpr
    intro i
    have hz := positive_orthogonal (measure k ω) (fieldV k ω i x) (fieldV k ω i (x + y))
      ((fieldV_range k ω i x).mono fun _ h => ⟨h.1, h.2.1⟩)
      ((fieldV_range k ω i (x + y)).mono fun _ h => ⟨h.1, h.2.1⟩)
      (fieldV_unit_correlation k ω i x y hy)
    filter_upwards [hae i x, hae i (x + y), hz] with η h1 h2 h3
    simpa only [h1, h2] using h3

section Sample
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure S) [SFinite ν]
  (d : S → ℂ × ℝ) (hd : Measurable d) {k' : ℕ} [NeZero k']
include hd

lemma sample_field (H : Fin k' → (ℂ × ℝ) × Ω → ℝ) (hm : ∀ i, Measurable (H i))
    (hp : ∀ x : ℂ × ℝ, ∀ᵐ ω ∂μ, ∑ i, H i (x, ω) = 1)
    (ho : ∀ x : ℂ × ℝ, ∀ s : S, ∀ᵐ ω ∂μ, ∀ i, H i (x, ω) * H i (x + d s, ω) = 0) :
    ∃ c : ℂ × ℝ → Fin k', Measurable c ∧
      ∀ᵐ p ∂(volume : Measure (ℂ × ℝ)).prod ν, c p.1 ≠ c (p.1 + d p.2) := by
  let c : (ℂ × ℝ) × Ω → Fin k' := positiveSelect H
  have hc : Measurable c := positiveSelect_measurable H hm
  have ha (p : (ℂ × ℝ) × S) : ∀ᵐ ω ∂μ, c (p.1, ω) ≠ c (p.1 + d p.2, ω) := by
    filter_upwards [hp p.1, hp (p.1 + d p.2), ho p.1 p.2] with ω h1 h2 h3
    intro he
    have hpos1 := positiveSelect_pos H (p.1, ω) h1
    have hpos2 := positiveSelect_pos H (p.1 + d p.2, ω) h2
    change 0 < H (c (p.1, ω)) (p.1, ω) at hpos1
    change 0 < H (c (p.1 + d p.2, ω)) (p.1 + d p.2, ω) at hpos2
    rw [← he] at hpos2
    exact (mul_pos hpos1 hpos2).ne' (h3 _)
  have hm1 : Measurable (fun q : ((ℂ × ℝ) × S) × Ω => c (q.1.1, q.2)) :=
    hc.comp ((measurable_fst.fst).prodMk measurable_snd)
  have hm2 : Measurable (fun q : ((ℂ × ℝ) × S) × Ω => c (q.1.1 + d q.1.2, q.2)) :=
    hc.comp (((measurable_fst.fst).add (hd.comp measurable_fst.snd)).prodMk measurable_snd)
  have hh : ∀ᵐ ω ∂μ, ∀ᵐ p ∂(volume : Measure (ℂ × ℝ)).prod ν, c (p.1, ω) ≠ c (p.1 + d p.2, ω) :=
    (Measure.ae_ae_comm (measurableSet_eq_fun hm1 hm2).compl).mp (.of_forall ha)
  obtain ⟨ω, hω⟩ := hh.exists
  exact ⟨fun x => c (x, ω), hc.comp (measurable_id.prodMk measurable_const), hω⟩

end Sample

end HN3
end
end OAI
