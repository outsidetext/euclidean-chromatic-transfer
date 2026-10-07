import OAI.HN3.Smoothing

/-!
# The vertical axis in three dimensions

After projecting onto horizontally continuous vectors (`plane_projection_unit_correlation`),
the remaining obstruction is a part that is continuous horizontally but arbitrary vertically.
Along each algebraic direction `u ∈ K` the points `(√(1-t²)·u, t)` are algebraic unit vectors,
and an invariant-mean line average kills that part. The fully continuous projection `pv` then
has zero correlation at every real unit vector.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HN3
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

section Abstract
variable {A H : Type*} [AddCommGroup A] [TopologicalSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))

lemma comm_projection (Y : unitary (H →L[ℂ] H))
    (hY : ∀ a w, (Y : H →L[ℂ] H) (op U a w) = op U a ((Y : H →L[ℂ] H) w)) (v : H) :
    (space U).starProjection ((Y : H →L[ℂ] H) v) =
      (Y : H →L[ℂ] H) ((space U).starProjection v) := by
  have h1 : (Y : H →L[ℂ] H) ((space U).starProjection v) ∈ space U :=
    comm_mem_space U _ hY ((space U).starProjection_apply_mem v)
  have h2 : (Y : H →L[ℂ] H) (v - (space U).starProjection v) ∈ (space U)ᗮ :=
    comm_mem_orthogonal U Y hY ((space U).sub_starProjection_mem_orthogonal v)
  have hv : (Y : H →L[ℂ] H) v = (Y : H →L[ℂ] H) ((space U).starProjection v) +
      (Y : H →L[ℂ] H) (v - (space U).starProjection v) := by
    rw [← map_add]; congr 1; abel
  rw [hv, map_add, Submodule.starProjection_eq_self_iff.mpr h1,
    (space U).starProjection_apply_eq_zero_iff.mpr h2, add_zero]

end Abstract

lemma dense_AF : Dense (AF : Set ℝ) := by
  refine Rat.denseRange_cast.mono ?_
  rintro _ ⟨q, rfl⟩
  exact mem_algebraicClosure_iff.mpr (by simpa using isAlgebraic_ratCast ℚ (A := ℝ) q)

/-- Embedding of the algebraic points into `ℂ × ℝ`. -/
def emb (a : V) : ℂ × ℝ := ((a.1 : ℂ), (a.2 : ℝ))

lemma emb_ui : IsUniformInducing emb :=
  (isUniformEmbedding_subtype_val.isUniformInducing).prod
    (isUniformEmbedding_subtype_val.isUniformInducing)

lemma emb_dense : DenseRange emb :=
  (dense_E.denseRange_val).prodMap dense_AF.denseRange_val

lemma emb_add (a b : V) : emb (a + b) = emb a + emb b := by
  simp [emb]

variable (k : ℕ) (ω : Space k)

/-! ### Orbits of fully continuous vectors and their extension to `ℂ × ℝ` -/

lemma orbit3_uc {v : Hilbert k ω} (h1 : v ∈ space (A := E) (planeRep k ω))
    (h2 : v ∈ space (A := AF) (lineRep k ω)) : UniformContinuous (fun a : V => T k ω a v) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ1, hδ1, hc1⟩ := Metric.continuousAt_iff.mp
    (orbit_continuous (planeRep k ω) h1).continuousAt (ε / 2) (by positivity)
  obtain ⟨δ2, hδ2, hc2⟩ := Metric.continuousAt_iff.mp
    (orbit_continuous (lineRep k ω) h2).continuousAt (ε / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun {a b} hab => ?_⟩
  have hd : dist a b = max (dist a.1 b.1) (dist a.2 b.2) := Prod.dist_eq
  have ha1 : dist (a.1 - b.1) 0 < δ1 := by
    rw [dist_zero_right, ← dist_eq_norm]
    exact lt_of_le_of_lt (le_max_left _ _) (hd ▸ lt_of_lt_of_le hab (min_le_left _ _))
  have ha2 : dist (a.2 - b.2) 0 < δ2 := by
    rw [dist_zero_right, ← dist_eq_norm]
    exact lt_of_le_of_lt (le_max_right _ _) (hd ▸ lt_of_lt_of_le hab (min_le_right _ _))
  have e1 : dist (op (planeRep k ω) (a.1 - b.1) v) v < ε / 2 := by
    have := hc1 ha1
    rwa [planeRep_op (z := 0), show ((0 : E), (0 : AF)) = (0 : V) from rfl, T_zero] at this
  have e2 : dist (op (lineRep k ω) (a.2 - b.2) v) v < ε / 2 := by
    have := hc2 ha2
    rwa [lineRep_op (t := 0), show ((0 : E), (0 : AF)) = (0 : V) from rfl, T_zero] at this
  have hsplit : T k ω a v = T k ω b (op (planeRep k ω) (a.1 - b.1) (op (lineRep k ω) (a.2 - b.2) v)) := by
    have he : b + ((a.1 - b.1, 0) : V) + ((0, a.2 - b.2) : V) = a := by
      refine Prod.ext ?_ ?_
      · change b.1 + (a.1 - b.1) + 0 = a.1
        abel
      · change b.2 + 0 + (a.2 - b.2) = a.2
        abel
    rw [planeRep_op, lineRep_op, ← T_add, ← T_add, he]
  rw [hsplit]
  calc dist (T k ω b (op (planeRep k ω) (a.1 - b.1) (op (lineRep k ω) (a.2 - b.2) v))) (T k ω b v)
      = dist (op (planeRep k ω) (a.1 - b.1) (op (lineRep k ω) (a.2 - b.2) v)) v := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact Unitary.norm_map (translation k ω b) _
    _ ≤ dist (op (planeRep k ω) (a.1 - b.1) (op (lineRep k ω) (a.2 - b.2) v))
          (op (planeRep k ω) (a.1 - b.1) v) + dist (op (planeRep k ω) (a.1 - b.1) v) v :=
        dist_triangle _ _ _
    _ = dist (op (lineRep k ω) (a.2 - b.2) v) v + dist (op (planeRep k ω) (a.1 - b.1) v) v := by
        rw [dist_op (A := E) (planeRep k ω)]
    _ < ε / 2 + ε / 2 := add_lt_add e2 e1
    _ = ε := by ring

/-- Continuous extension of the orbit of `v` to all of `ℂ × ℝ`. -/
def Ext3 (v : Hilbert k ω) : ℂ × ℝ → Hilbert k ω :=
  (emb_ui.isDenseInducing emb_dense).extend (fun a : V => T k ω a v)

lemma Ext3_eq {v : Hilbert k ω} (h1 : v ∈ space (A := E) (planeRep k ω))
    (h2 : v ∈ space (A := AF) (lineRep k ω)) (a : V) : Ext3 k ω v (emb a) = T k ω a v :=
  uniformly_extend_of_ind emb_ui emb_dense (orbit3_uc k ω h1 h2) a

lemma Ext3_continuous {v : Hilbert k ω} (h1 : v ∈ space (A := E) (planeRep k ω))
    (h2 : v ∈ space (A := AF) (lineRep k ω)) : Continuous (Ext3 k ω v) :=
  (uniformContinuous_uniformly_extend emb_ui emb_dense (orbit3_uc k ω h1 h2)).continuous

lemma Ext3_inner {v w : Hilbert k ω} (hv1 : v ∈ space (A := E) (planeRep k ω))
    (hv2 : v ∈ space (A := AF) (lineRep k ω)) (hw1 : w ∈ space (A := E) (planeRep k ω))
    (hw2 : w ∈ space (A := AF) (lineRep k ω)) (x y : ℂ × ℝ) :
    ⟪Ext3 k ω v x, Ext3 k ω w (x + y)⟫_ℂ = ⟪v, Ext3 k ω w y⟫_ℂ := by
  have hc := Ext3_continuous k ω hv1 hv2
  have hd := Ext3_continuous k ω hw1 hw2
  refine emb_dense.induction_on₂
    (p := fun x y => ⟪Ext3 k ω v x, Ext3 k ω w (x + y)⟫_ℂ = ⟪v, Ext3 k ω w y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq ((hc.comp continuous_fst).inner (hd.comp (continuous_fst.add continuous_snd)))
      (continuous_const.inner (hd.comp continuous_snd))
  · intro a b
    change ⟪Ext3 k ω v (emb a), Ext3 k ω w (emb a + emb b)⟫_ℂ = ⟪v, Ext3 k ω w (emb b)⟫_ℂ
    rw [← emb_add, Ext3_eq k ω hv1 hv2, Ext3_eq k ω hw1 hw2, Ext3_eq k ω hw1 hw2, T_add]
    exact Unitary.inner_map_map (translation k ω a) v (T k ω b w)

/-! ### The projections and the correlation split -/

instance line_complete : CompleteSpace (space (A := AF) (lineRep k ω)) :=
  (isClosed_space (A := AF) (lineRep k ω)).completeSpace_coe

abbrev P0 : Hilbert k ω →L[ℂ] Hilbert k ω := (space (A := AF) (lineRep k ω)).starProjection

def gv (i : Fin k) : Hilbert k ω := PE k ω (colorVector k ω i)
def pv (i : Fin k) : Hilbert k ω := P0 k ω (gv k ω i)
def wv (i : Fin k) : Hilbert k ω := gv k ω i - pv k ω i

lemma line_comm (x : V) (t : AF) (w : Hilbert k ω) :
    T k ω x (op (lineRep k ω) t w) = op (lineRep k ω) t (T k ω x w) := by
  rw [lineRep_op, lineRep_op, T_comm]

lemma gv_plane (i : Fin k) : gv k ω i ∈ space (A := E) (planeRep k ω) :=
  (space (A := E) (planeRep k ω)).starProjection_apply_mem _

lemma pv_line (i : Fin k) : pv k ω i ∈ space (A := AF) (lineRep k ω) :=
  (space (A := AF) (lineRep k ω)).starProjection_apply_mem _

lemma P0_comm_T (x : V) (v : Hilbert k ω) : P0 k ω (T k ω x v) = T k ω x (P0 k ω v) :=
  comm_projection (lineRep k ω) (translation k ω x) (fun a w => line_comm k ω x a w) v

lemma pv_plane (i : Fin k) : pv k ω i ∈ space (A := E) (planeRep k ω) :=
  comm_mem_space (planeRep k ω) (P0 k ω)
    (fun z w => by rw [planeRep_op, planeRep_op]; exact P0_comm_T k ω (z, 0) w) (gv_plane k ω i)

lemma wv_plane (i : Fin k) : wv k ω i ∈ space (A := E) (planeRep k ω) :=
  Submodule.sub_mem _ (gv_plane k ω i) (pv_plane k ω i)

lemma wv_orth (i : Fin k) : wv k ω i ∈ (space (A := AF) (lineRep k ω))ᗮ :=
  (space (A := AF) (lineRep k ω)).sub_starProjection_mem_orthogonal _

lemma corr_split (i : Fin k) (x : V) (hx : sq x = 1) (hz : x.1 ≠ 0) :
    ⟪pv k ω i, T k ω x (pv k ω i)⟫_ℂ = -⟪wv k ω i, T k ω x (wv k ω i)⟫_ℂ := by
  have h0 : ⟪gv k ω i, T k ω x (gv k ω i)⟫_ℂ = 0 :=
    plane_projection_unit_correlation k ω i x hx hz
  have hTx : ∀ a w, T k ω x (op (lineRep k ω) a w) = op (lineRep k ω) a (T k ω x w) :=
    line_comm k ω x
  have h1 : ⟪pv k ω i, T k ω x (wv k ω i)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp
      (comm_mem_orthogonal (lineRep k ω) (translation k ω x) hTx (wv_orth k ω i)) _ (pv_line k ω i)
  have h2 : ⟪wv k ω i, T k ω x (pv k ω i)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (wv_orth k ω i) _
      (comm_mem_space (lineRep k ω) _ hTx (pv_line k ω i))
  have hg : gv k ω i = pv k ω i + wv k ω i := by simp [wv]
  rw [hg, map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2] at h0
  linear_combination h0

/-! ### Algebraic points along a direction -/

def rho (t : ℝ) : ℝ := Real.sqrt (1 - t ^ 2)

lemma rho_continuous : Continuous rho := by
  unfold rho; fun_prop

lemma rho_alg (t : AF) : IsAlgebraic ℚ (rho t) := by
  have ht : IsAlgebraic ℚ (t : ℝ) := mem_algebraicClosure_iff.mp t.property
  by_cases h : 0 ≤ 1 - (t : ℝ) ^ 2
  · apply IsAlgebraic.of_pow (n := 2) (by norm_num)
    rw [rho, Real.sq_sqrt h]
    exact isAlgebraic_one.sub (ht.pow 2)
  · rw [rho, Real.sqrt_eq_zero_of_nonpos (by linarith)]
    exact isAlgebraic_zero

lemma rho_alg_complex (t : AF) : IsAlgebraic ℚ ((rho t : ℝ) : ℂ) := by
  have := (rho_alg t).algHom (Complex.ofRealAm.restrictScalars ℚ)
  simpa using this

def eu (u : K) (t : AF) : E :=
  ⟨((rho t : ℝ) : ℂ) * ((u : Circle) : ℂ),
    mem_algebraicClosure_iff.mpr ((rho_alg_complex t).mul u.property)⟩

def xu (u : K) (t : AF) : V := (eu u t, t)

lemma emb_xu (u : K) (t : AF) : emb (xu u t) = (((rho t : ℝ) : ℂ) * ((u : Circle) : ℂ), (t : ℝ)) := rfl

lemma sq_xu (u : K) (t : AF) (ht : |(t : ℝ)| ≤ 1) : sq (xu u t) = 1 := by
  have h0 : 0 ≤ 1 - (t : ℝ) ^ 2 := by nlinarith [abs_le.mp ht, sq_abs (t : ℝ)]
  simp only [sq, xu, eu]
  rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, rho,
    Real.sq_sqrt h0]
  ring

lemma xu_ne (u : K) (t : AF) (ht : |(t : ℝ)| < 1) : (xu u t).1 ≠ 0 := by
  intro h
  have h0 : 0 < 1 - (t : ℝ) ^ 2 := by nlinarith [abs_lt.mp ht, sq_abs (t : ℝ)]
  have hc := congrArg (fun z : E => ‖(z : ℂ)‖) h
  simp only [xu, eu, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    ZeroMemClass.coe_zero, norm_zero, rho] at hc
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hc
  exact (Real.sqrt_pos.mpr h0).ne' hc

end HN3
end
end OAI
