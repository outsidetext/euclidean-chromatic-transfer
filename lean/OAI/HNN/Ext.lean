import OAI.HNN.Blocks

/-!
# Continuous extension of orbits to real arguments

A vector that is continuous for every block (and, for `r ≤ 1`, along the axis) has a uniformly
continuous orbit on the algebraic points, hence a continuous extension to
`X m r = (Fin m → ℂ) × (Fin r → ℝ)`. The block-only version extends to `Fin m → ℂ`.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HNN
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

/-- The real model of `ℝ^(2m+r)`. -/
abbrev X (m r : ℕ) := (Fin m → ℂ) × (Fin r → ℝ)

variable {m r : ℕ}

def embP (a : Fin m → E) : Fin m → ℂ := fun j => (a j : ℂ)
def embL (s : Fin r → AF) : Fin r → ℝ := fun i => (s i : ℝ)
def emb (a : V m r) : X m r := (embP a.1, embL a.2)

lemma embP_iso : Isometry (embP (m := m)) :=
  Isometry.piMap (fun _ => Subtype.val) (fun _ => isometry_subtype_coe)

lemma embL_iso : Isometry (embL (r := r)) :=
  Isometry.piMap (fun _ => Subtype.val) (fun _ => isometry_subtype_coe)

lemma emb_iso : Isometry (emb (m := m) (r := r)) := embP_iso.prodMap embL_iso

lemma embP_dense : DenseRange (embP (m := m)) :=
  DenseRange.piMap (fun _ => dense_E.denseRange_val)

lemma embL_dense : DenseRange (embL (r := r)) :=
  DenseRange.piMap (fun _ => HN3.dense_AF.denseRange_val)

lemma emb_dense : DenseRange (emb (m := m) (r := r)) := embP_dense.prodMap embL_dense

lemma embP_add (a b : Fin m → E) : embP (a + b) = embP a + embP b := by
  funext j; simp [embP]

lemma emb_add (a b : V m r) : emb (a + b) = emb a + emb b := by
  simp only [emb, Prod.fst_add, Prod.snd_add, embP_add]
  refine Prod.ext rfl ?_
  funext i; simp [embL]

variable {D : Set ℝ} {k : ℕ} (ω : Space m r D k)

/-! ### Telescoping bound -/

lemma T_sum_bound {ι : Type*} (s : Finset ι) (a : ι → V m r) (v : Hilbert ω) :
    ‖T ω (∑ i ∈ s, a i) v - v‖ ≤ ∑ i ∈ s, ‖T ω (a i) v - v‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [T_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, T_add]
    calc ‖T ω (a j) (T ω (∑ i ∈ s, a i) v) - v‖
        ≤ ‖T ω (a j) (T ω (∑ i ∈ s, a i) v) - T ω (a j) v‖ + ‖T ω (a j) v - v‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖T ω (∑ i ∈ s, a i) v - v‖ + ‖T ω (a j) v - v‖ := by
          rw [← map_sub, Unitary.norm_map (translation ω (a j))]
      _ ≤ _ := by linarith

lemma decomp (c : V m r) : c = ∑ j, ((Pi.single j (c.1 j), 0) : V m r) + (0, c.2) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum]
    rw [add_zero]
    exact (Finset.univ_sum_single c.1).symm
  · simp [Prod.snd_sum]

lemma T_bound (c : V m r) (v : Hilbert ω) :
    ‖T ω c v - v‖ ≤ ∑ j, ‖op (planeRep ω j) (c.1 j) v - v‖ + ‖T ω (0, c.2) v - v‖ := by
  conv_lhs => rw [decomp c, T_add]
  calc ‖T ω (∑ j, ((Pi.single j (c.1 j), 0) : V m r)) (T ω (0, c.2) v) - v‖
      ≤ ‖T ω (∑ j, ((Pi.single j (c.1 j), 0) : V m r)) (T ω (0, c.2) v) -
          T ω (∑ j, ((Pi.single j (c.1 j), 0) : V m r)) v‖ +
        ‖T ω (∑ j, ((Pi.single j (c.1 j), 0) : V m r)) v - v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖T ω (0, c.2) v - v‖ + ‖T ω (∑ j, ((Pi.single j (c.1 j), 0) : V m r)) v - v‖ := by
        rw [← map_sub, Unitary.norm_map]
    _ ≤ ‖T ω (0, c.2) v - v‖ + ∑ j, ‖op (planeRep ω j) (c.1 j) v - v‖ := by
        gcongr
        exact T_sum_bound ω _ _ v
    _ = _ := add_comm _ _

/-- The single axis coordinate (zero if there is no axis). -/
def lineCoord (s : Fin r → AF) : AF := if h : 0 < r then s ⟨0, h⟩ else 0

lemma lineCoord_continuous : Continuous (lineCoord (r := r)) := by
  unfold lineCoord
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

lemma lineCoord_zero : lineCoord (0 : Fin r → AF) = 0 := by
  unfold lineCoord; split_ifs <;> rfl

lemma line_eq (hr : r ≤ 1) (s : Fin r → AF) : s = fun _ => lineCoord s := by
  funext i
  have h0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hi : i = ⟨0, h0⟩ := Fin.ext (by have := i.isLt; omega)
  simp [lineCoord, h0, hi]

lemma tendsto_blocks {v : Hilbert ω} (hv : ∀ j, v ∈ space (A := E) (planeRep ω j)) :
    Tendsto (fun c : V m r => ∑ j, ‖op (planeRep ω j) (c.1 j) v - v‖) (𝓝 0) (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ _j : Fin m, (0 : ℝ) by simp]
  refine tendsto_finsetSum _ fun j _ => ?_
  have h1 : Tendsto (fun c : V m r => c.1 j) (𝓝 0) (𝓝 0) :=
    ((continuous_apply j).comp continuous_fst).tendsto' _ _ rfl
  have h2 := (hv j).comp h1
  rw [show (0 : ℝ) = ‖v - v‖ by simp]
  exact (h2.sub_const v).norm

/-- Joint continuity at the origin of the whole translation orbit. -/
lemma orbit_tendsto (hr : r ≤ 1) {v : Hilbert ω} (hv : ∀ j, v ∈ space (A := E) (planeRep ω j))
    (hl : v ∈ space (A := AF) (lineRep ω)) :
    Tendsto (fun c : V m r => T ω c v) (𝓝 0) (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun c => norm_nonneg _) (fun c => T_bound ω c v) ?_
  rw [show (0 : ℝ) = 0 + 0 by simp]
  refine (tendsto_blocks ω hv).add ?_
  have h1 : Tendsto (fun c : V m r => lineCoord c.2) (𝓝 0) (𝓝 0) := by
    have h0 := (lineCoord_continuous.comp continuous_snd).tendsto (0 : V m r)
    rw [Function.comp_apply, Prod.snd_zero, lineCoord_zero] at h0
    exact h0
  have h2 := hl.comp h1
  have he : ∀ c : V m r, T ω (0, c.2) v = op (lineRep ω) (lineCoord c.2) v := by
    intro c
    rw [lineRep_op, ← line_eq hr]
  simp_rw [he]
  rw [show (0 : ℝ) = ‖v - v‖ by simp]
  exact (h2.sub_const v).norm

lemma orbitP_tendsto {v : Hilbert ω} (hv : ∀ j, v ∈ space (A := E) (planeRep ω j)) :
    Tendsto (fun a : Fin m → E => T ω (a, 0) v) (𝓝 0) (𝓝 v) := by
  have hb : ∀ a : Fin m → E, ‖T ω (a, 0) v - v‖ ≤ ∑ j, ‖op (planeRep ω j) (a j) v - v‖ := by
    intro a
    have := T_bound ω ((a, 0) : V m r) v
    dsimp only at this
    have h0 : ‖T ω ((0 : Fin m → E), (0 : Fin r → AF)) v - v‖ = 0 := by
      rw [Prod.mk_zero_zero, T_zero, sub_self, norm_zero]
    rw [h0, add_zero] at this
    exact this
  have ht : Tendsto (fun a : Fin m → E => ∑ j, ‖op (planeRep ω j) (a j) v - v‖) (𝓝 0) (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ _j : Fin m, (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun j _ => ?_
    have h1 : Tendsto (fun a : Fin m → E => a j) (𝓝 0) (𝓝 0) :=
      (continuous_apply j).tendsto' _ _ rfl
    have h2 := (hv j).comp h1
    rw [show (0 : ℝ) = ‖v - v‖ by simp]
    exact (h2.sub_const v).norm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hb ht

lemma uc_of_tendsto {G : Type*} [NormedAddCommGroup G] (f : G → V m r)
    (hf : ∀ a b, f a = f b + f (a - b)) {v : Hilbert ω}
    (h : Tendsto (fun a => T ω (f a) v) (𝓝 0) (𝓝 v)) :
    UniformContinuous (fun a => T ω (f a) v) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhds_nhds.mp h ε hε
  refine ⟨δ, hδ, fun {a b} hab => ?_⟩
  have h1 : dist (a - b) 0 < δ := by rwa [dist_zero_right, ← dist_eq_norm]
  have := hd h1
  rw [hf a b, T_add, dist_eq_norm, ← map_sub, Unitary.norm_map, ← dist_eq_norm]
  exact this

lemma orbit_uc (hr : r ≤ 1) {v : Hilbert ω} (hv : ∀ j, v ∈ space (A := E) (planeRep ω j))
    (hl : v ∈ space (A := AF) (lineRep ω)) : UniformContinuous (fun c : V m r => T ω c v) :=
  uc_of_tendsto ω id (fun a b => by simp) (orbit_tendsto ω hr hv hl)

lemma orbitP_uc {v : Hilbert ω} (hv : ∀ j, v ∈ space (A := E) (planeRep ω j)) :
    UniformContinuous (fun a : Fin m → E => T ω (a, 0) v) :=
  uc_of_tendsto ω (fun a => ((a, 0) : V m r)) (fun a b => by simp) (orbitP_tendsto ω hv)

/-! ### Extensions -/

/-- Extension of the block orbit `a ↦ T (a, 0) v` to `Fin m → ℂ`. -/
def ExtP (v : Hilbert ω) : (Fin m → ℂ) → Hilbert ω :=
  (embP_iso.isUniformInducing.isDenseInducing embP_dense).extend (fun a : Fin m → E => T ω (a, 0) v)

/-- Extension of the full orbit to `X m r`. -/
def Ext (v : Hilbert ω) : X m r → Hilbert ω :=
  (emb_iso.isUniformInducing.isDenseInducing emb_dense).extend (fun a : V m r => T ω a v)

section
variable {v : Hilbert ω}

lemma ExtP_eq (hv : ∀ j, v ∈ space (A := E) (planeRep ω j)) (a : Fin m → E) :
    ExtP ω v (embP a) = T ω (a, 0) v :=
  uniformly_extend_of_ind embP_iso.isUniformInducing embP_dense (orbitP_uc ω hv) a

lemma ExtP_continuous (hv : ∀ j, v ∈ space (A := E) (planeRep ω j)) : Continuous (ExtP ω v) :=
  (uniformContinuous_uniformly_extend embP_iso.isUniformInducing embP_dense
    (orbitP_uc ω hv)).continuous

lemma ExtP_norm (hv : ∀ j, v ∈ space (A := E) (planeRep ω j)) (z : Fin m → ℂ) :
    ‖ExtP ω v z‖ = ‖v‖ := by
  refine embP_dense.induction_on z
    (isClosed_eq (continuous_norm.comp (ExtP_continuous ω hv)) continuous_const) ?_
  intro a
  rw [ExtP_eq ω hv]
  exact Unitary.norm_map _ _

variable (hr : r ≤ 1)
include hr

lemma Ext_eq (hv : ∀ j, v ∈ space (A := E) (planeRep ω j))
    (hl : v ∈ space (A := AF) (lineRep ω)) (a : V m r) : Ext ω v (emb a) = T ω a v :=
  uniformly_extend_of_ind emb_iso.isUniformInducing emb_dense (orbit_uc ω hr hv hl) a

lemma Ext_continuous (hv : ∀ j, v ∈ space (A := E) (planeRep ω j))
    (hl : v ∈ space (A := AF) (lineRep ω)) : Continuous (Ext ω v) :=
  (uniformContinuous_uniformly_extend emb_iso.isUniformInducing emb_dense
    (orbit_uc ω hr hv hl)).continuous

lemma Ext_inner {w : Hilbert ω} (hv : ∀ j, v ∈ space (A := E) (planeRep ω j))
    (hl : v ∈ space (A := AF) (lineRep ω)) (hw : ∀ j, w ∈ space (A := E) (planeRep ω j))
    (hwl : w ∈ space (A := AF) (lineRep ω)) (x y : X m r) :
    ⟪Ext ω v x, Ext ω w (x + y)⟫_ℂ = ⟪v, Ext ω w y⟫_ℂ := by
  have hc := Ext_continuous ω hr hv hl
  have hd := Ext_continuous ω hr hw hwl
  refine emb_dense.induction_on₂
    (p := fun x y => ⟪Ext ω v x, Ext ω w (x + y)⟫_ℂ = ⟪v, Ext ω w y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq ((hc.comp continuous_fst).inner (hd.comp (continuous_fst.add continuous_snd)))
      (continuous_const.inner (hd.comp continuous_snd))
  · intro a b
    rw [← emb_add, Ext_eq ω hr hv hl, Ext_eq ω hr hw hwl, Ext_eq ω hr hw hwl, T_add]
    exact Unitary.inner_map_map (translation ω a) v (T ω b w)

end

end HNN
end
end OAI
