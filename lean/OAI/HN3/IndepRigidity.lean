import OAI.HN3.IndepModel
import OAI.HN3.Line

/-!
# The plane step and the line split for the independent-set model

Copy of the model-specific parts of `HN3.Rigidity` and `HN3.Line` for the single indicator
`f = 1[0 ∈ I]` on the independent-set model `(ISpace, measure L)`. Generic lemmas
(`twisted_residual`, `comm_mem_space`, `comm_projection`, `emb`, ...) are reused from `HN3`.
-/

set_option linter.unusedSectionVars false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HN3
namespace Indep
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

/-! ## The plane step in the three-dimensional model -/

variable (L : State ISpace)

def colorValue (η : ISpace) : ℂ := if η.val 0 = 1 then 1 else 0

lemma color_memLp : MemLp (colorValue) 2 (measure L) := by
  refine MemLp.of_bound ?_ 1 ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton (1 : Fin 2)).preimage (show Measurable (fun η : ISpace => η.val 0) from
      ((continuous_apply (0 : V)).comp continuous_subtype_val).measurable)
  · exact .of_forall fun η => by dsimp [colorValue]; split_ifs <;> simp

abbrev colorVector : Hilbert L := (color_memLp L).toLp (colorValue)

lemma color_ae : colorVector L =ᵐ[measure L] colorValue :=
  (color_memLp L).coeFn_toLp

lemma color_rotation_fixed (b : K) : R L b (colorVector L) = colorVector L := by
  change Lp.compMeasurePreserving (rotate b) (rotate_preserving L b) _ = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (colorVector L) (rotate_preserving L b),
    (rotate_preserving L b).quasiMeasurePreserving.ae (color_ae L), color_ae L]
    with η h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, colorValue, rotate_apply, rmap_zero]

/-- Independence: zero correlation of the indicator at every algebraic unit vector. -/
lemma color_unit_correlation (x : V) (hx : sq x = 1) :
    ⟪colorVector L, T L x (colorVector L)⟫_ℂ = 0 := by
  rw [translation_apply, L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [color_ae L,
    Lp.coeFn_compMeasurePreserving (colorVector L) (trans_preserving L x),
    (trans_preserving L x).quasiMeasurePreserving.ae (color_ae L)] with η h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, colorValue, trans_apply, zero_add]
  have hp : ¬ (η.val 0 = 1 ∧ η.val x = 1) := η.property 0 x (by rw [zero_sub, sq_neg, hx])
  by_cases hi : η.val 0 = 1
  · have hj : η.val x ≠ 1 := fun h => hp ⟨hi, h⟩
    simp [hi, hj]
  · simp [hi]

instance plane_complete : CompleteSpace (space (A := E) (planeRep L)) :=
  (isClosed_space (A := E) (planeRep L)).completeSpace_coe

/-- Projection onto vectors continuous under horizontal translations. -/
abbrev PE : Hilbert L →L[ℂ] Hilbert L := (space (A := E) (planeRep L)).starProjection

lemma T_comm_plane (x : V) (z : E) (w : Hilbert L) :
    T L x (op (planeRep L) z w) = op (planeRep L) z (T L x w) := by
  rw [planeRep_op, planeRep_op, T_comm]

lemma PE_rotation_fixed (v : Hilbert L) (b : K) (hv : R L b v = v) :
    R L b (PE L v) = PE L v :=
  projection_covariance_fixed (planeRep L) (rotation L b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (plane_covariance L b) v hv

/-- Plane step: the horizontally continuous projection of a color indicator keeps zero
correlation at every algebraic unit vector with nonzero horizontal component. -/
theorem plane_projection_unit_correlation (x : V) (hx : sq x = 1) (hz : x.1 ≠ 0) :
    ⟪PE L (colorVector L), T L x (PE L (colorVector L))⟫_ℂ = 0 := by
  set f := colorVector L
  set g := PE L f
  set b := f - g
  have hg : g ∈ space (A := E) (planeRep L) := (space (A := E) (planeRep L)).starProjection_apply_mem f
  have hb : b ∈ (space (A := E) (planeRep L))ᗮ :=
    (space (A := E) (planeRep L)).sub_starProjection_mem_orthogonal f
  have hbfix : ∀ c, R L c b = b := fun c => by
    simp only [b, map_sub, color_rotation_fixed, g, PE_rotation_fixed L f c (color_rotation_fixed L c), f]
  -- the vertical translation commutes with plane translations and rotations
  let Y := translation L (0, x.2)
  have hYU : ∀ z w, (Y : Hilbert L →L[ℂ] Hilbert L) (op (planeRep L) z w) =
      op (planeRep L) z ((Y : Hilbert L →L[ℂ] Hilbert L) w) := fun z w => T_comm_plane L _ z w
  have hYW : ∀ c w, (Y : Hilbert L →L[ℂ] Hilbert L) (R L c w) =
      R L c ((Y : Hilbert L →L[ℂ] Hilbert L) w) := fun c w => (R_line L c x.2 w).symm
  have hsplit : ∀ w, T L x w = op (planeRep L) x.1 ((Y : Hilbert L →L[ℂ] Hilbert L) w) := by
    intro w
    rw [planeRep_op]
    change T L x w = T L (x.1, 0) (T L (0, x.2) w)
    rw [← T_add]
    simp
  have hbb : ⟪b, T L x b⟫_ℂ = 0 := by
    rw [hsplit]
    exact twisted_residual (planeRep L) (rotation L) (plane_covariance L) Y hYU hYW b hb
      hbfix x.1 hz
  have hTx : ∀ a w, T L x (op (planeRep L) a w) = op (planeRep L) a (T L x w) :=
    fun a w => T_comm_plane L x a w
  have h1 : ⟪g, T L x b⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp (comm_mem_orthogonal (planeRep L) (translation L x) hTx hb) g hg
  have h2 : ⟪b, T L x g⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp hb _ (comm_mem_space (planeRep L) _ hTx hg)
  have hf : f = g + b := by simp [b]
  have h0 : ⟪f, T L x f⟫_ℂ = 0 := color_unit_correlation L x hx
  rw [hf, map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, hbb] at h0
  simpa using h0


/-! ### Orbits of fully continuous vectors and their extension to `ℂ × ℝ` -/

lemma orbit3_uc {v : Hilbert L} (h1 : v ∈ space (A := E) (planeRep L))
    (h2 : v ∈ space (A := AF) (lineRep L)) : UniformContinuous (fun a : V => T L a v) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ1, hδ1, hc1⟩ := Metric.continuousAt_iff.mp
    (orbit_continuous (planeRep L) h1).continuousAt (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, hc2⟩ := Metric.continuousAt_iff.mp
    (orbit_continuous (lineRep L) h2).continuousAt (ε / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun {a b} hab => ?_⟩
  have hd : dist a b = max (dist a.1 b.1) (dist a.2 b.2) := Prod.dist_eq
  have ha1 : dist (a.1 - b.1) 0 < δ1 := by
    rw [dist_zero_right, ← dist_eq_norm]
    exact lt_of_le_of_lt (le_max_left _ _) (hd ▸ lt_of_lt_of_le hab (min_le_left _ _))
  have ha2 : dist (a.2 - b.2) 0 < δ2 := by
    rw [dist_zero_right, ← dist_eq_norm]
    exact lt_of_le_of_lt (le_max_right _ _) (hd ▸ lt_of_lt_of_le hab (min_le_right _ _))
  have e1 : dist (op (planeRep L) (a.1 - b.1) v) v < ε / 2 := by
    have := hc1 ha1
    rwa [planeRep_op (z := 0), show ((0 : E), (0 : AF)) = (0 : V) from rfl, T_zero] at this
  have e2 : dist (op (lineRep L) (a.2 - b.2) v) v < ε / 2 := by
    have := hc2 ha2
    rwa [lineRep_op (t := 0), show ((0 : E), (0 : AF)) = (0 : V) from rfl, T_zero] at this
  have hsplit : T L a v = T L b (op (planeRep L) (a.1 - b.1) (op (lineRep L) (a.2 - b.2) v)) := by
    have he : b + ((a.1 - b.1, 0) : V) + ((0, a.2 - b.2) : V) = a := by
      refine Prod.ext ?_ ?_
      · change b.1 + (a.1 - b.1) + 0 = a.1
        abel
      · change b.2 + 0 + (a.2 - b.2) = a.2
        abel
    rw [planeRep_op, lineRep_op, ← T_add, ← T_add, he]
  rw [hsplit]
  calc dist (T L b (op (planeRep L) (a.1 - b.1) (op (lineRep L) (a.2 - b.2) v))) (T L b v)
      = dist (op (planeRep L) (a.1 - b.1) (op (lineRep L) (a.2 - b.2) v)) v := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact Unitary.norm_map (translation L b) _
    _ ≤ dist (op (planeRep L) (a.1 - b.1) (op (lineRep L) (a.2 - b.2) v))
          (op (planeRep L) (a.1 - b.1) v) + dist (op (planeRep L) (a.1 - b.1) v) v :=
        dist_triangle _ _ _
    _ = dist (op (lineRep L) (a.2 - b.2) v) v + dist (op (planeRep L) (a.1 - b.1) v) v := by
        rw [dist_op (A := E) (planeRep L)]
    _ < ε / 2 + ε / 2 := add_lt_add e2 e1
    _ = ε := by ring

/-- Continuous extension of the orbit of `v` to all of `ℂ × ℝ`. -/
def Ext3 (v : Hilbert L) : ℂ × ℝ → Hilbert L :=
  (emb_ui.isDenseInducing emb_dense).extend (fun a : V => T L a v)

lemma Ext3_eq {v : Hilbert L} (h1 : v ∈ space (A := E) (planeRep L))
    (h2 : v ∈ space (A := AF) (lineRep L)) (a : V) : Ext3 L v (emb a) = T L a v :=
  uniformly_extend_of_ind emb_ui emb_dense (orbit3_uc L h1 h2) a

lemma Ext3_continuous {v : Hilbert L} (h1 : v ∈ space (A := E) (planeRep L))
    (h2 : v ∈ space (A := AF) (lineRep L)) : Continuous (Ext3 L v) :=
  (uniformContinuous_uniformly_extend emb_ui emb_dense (orbit3_uc L h1 h2)).continuous

lemma Ext3_inner {v w : Hilbert L} (hv1 : v ∈ space (A := E) (planeRep L))
    (hv2 : v ∈ space (A := AF) (lineRep L)) (hw1 : w ∈ space (A := E) (planeRep L))
    (hw2 : w ∈ space (A := AF) (lineRep L)) (x y : ℂ × ℝ) :
    ⟪Ext3 L v x, Ext3 L w (x + y)⟫_ℂ = ⟪v, Ext3 L w y⟫_ℂ := by
  have hc := Ext3_continuous L hv1 hv2
  have hd := Ext3_continuous L hw1 hw2
  refine emb_dense.induction_on₂
    (p := fun x y => ⟪Ext3 L v x, Ext3 L w (x + y)⟫_ℂ = ⟪v, Ext3 L w y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq ((hc.comp continuous_fst).inner (hd.comp (continuous_fst.add continuous_snd)))
      (continuous_const.inner (hd.comp continuous_snd))
  · intro a b
    change ⟪Ext3 L v (emb a), Ext3 L w (emb a + emb b)⟫_ℂ = ⟪v, Ext3 L w (emb b)⟫_ℂ
    rw [← emb_add, Ext3_eq L hv1 hv2, Ext3_eq L hw1 hw2, Ext3_eq L hw1 hw2, T_add]
    exact Unitary.inner_map_map (translation L a) v (T L b w)

/-! ### The projections and the correlation split -/

instance line_complete : CompleteSpace (space (A := AF) (lineRep L)) :=
  (isClosed_space (A := AF) (lineRep L)).completeSpace_coe

abbrev P0 : Hilbert L →L[ℂ] Hilbert L := (space (A := AF) (lineRep L)).starProjection

def gv : Hilbert L := PE L (colorVector L)
def pv : Hilbert L := P0 L (gv L)
def wv : Hilbert L := gv L - pv L

lemma line_comm (x : V) (t : AF) (w : Hilbert L) :
    T L x (op (lineRep L) t w) = op (lineRep L) t (T L x w) := by
  rw [lineRep_op, lineRep_op, T_comm]

lemma gv_plane : gv L ∈ space (A := E) (planeRep L) :=
  (space (A := E) (planeRep L)).starProjection_apply_mem _

lemma pv_line : pv L ∈ space (A := AF) (lineRep L) :=
  (space (A := AF) (lineRep L)).starProjection_apply_mem _

lemma P0_comm_T (x : V) (v : Hilbert L) : P0 L (T L x v) = T L x (P0 L v) :=
  comm_projection (lineRep L) (translation L x) (fun a w => line_comm L x a w) v

lemma pv_plane : pv L ∈ space (A := E) (planeRep L) :=
  comm_mem_space (planeRep L) (P0 L)
    (fun z w => by rw [planeRep_op, planeRep_op]; exact P0_comm_T L (z, 0) w) (gv_plane L)

lemma wv_plane : wv L ∈ space (A := E) (planeRep L) :=
  Submodule.sub_mem _ (gv_plane L) (pv_plane L)

lemma wv_orth : wv L ∈ (space (A := AF) (lineRep L))ᗮ :=
  (space (A := AF) (lineRep L)).sub_starProjection_mem_orthogonal _

lemma corr_split (x : V) (hx : sq x = 1) (hz : x.1 ≠ 0) :
    ⟪pv L, T L x (pv L)⟫_ℂ = -⟪wv L, T L x (wv L)⟫_ℂ := by
  have h0 : ⟪gv L, T L x (gv L)⟫_ℂ = 0 :=
    plane_projection_unit_correlation L x hx hz
  have hTx : ∀ a w, T L x (op (lineRep L) a w) = op (lineRep L) a (T L x w) :=
    line_comm L x
  have h1 : ⟪pv L, T L x (wv L)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp
      (comm_mem_orthogonal (lineRep L) (translation L x) hTx (wv_orth L)) _ (pv_line L)
  have h2 : ⟪wv L, T L x (pv L)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (wv_orth L) _
      (comm_mem_space (lineRep L) _ hTx (pv_line L))
  have hg : gv L = pv L + wv L := by simp [wv]
  rw [hg, map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2] at h0
  linear_combination h0

end Indep
end HN3
end
end OAI
