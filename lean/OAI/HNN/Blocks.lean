import OAI.HNN.Model

/-!
# Projecting block by block

For each coordinate plane `j` let `PJ j` be the projection onto the vectors continuous under
translations of that plane. Composing them over all blocks (`QL`) keeps rotation-invariant
vectors rotation-invariant, lands in the continuous vectors of every block, and, by twisted
rigidity, preserves the correlation `⟪v, T a v⟫` at every *generic* algebraic vector `a`
(all block components nonzero). A final projection `P0` onto the vectors continuous along the
last axes gives the label vectors `pv`.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HNN
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable {m r : ℕ} {D : Set ℝ} {k : ℕ} (ω : Space m r D k)

/-! ### Colour indicators -/

def colorValue (i : Fin k) (η : Space m r D k) : ℂ := if η.val 0 = i then 1 else 0

lemma color_memLp (i : Fin k) : MemLp (colorValue (m := m) (r := r) (D := D) i) 2 (measure ω) := by
  refine MemLp.of_bound ?_ 1 ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton i).preimage
      (show Measurable (fun η : Space m r D k => η.val 0) from
        ((continuous_apply (0 : V m r)).comp continuous_subtype_val).measurable)
  · exact .of_forall fun η => by dsimp [colorValue]; split_ifs <;> simp

abbrev colorVector (i : Fin k) : Hilbert ω := (color_memLp ω i).toLp (colorValue i)

lemma color_ae (i : Fin k) : colorVector ω i =ᵐ[measure ω] colorValue i :=
  (color_memLp ω i).coeFn_toLp

lemma rmap_zero (b : Fin m → K) : rmap b (0 : V m r) = 0 := by
  refine Prod.ext ?_ rfl
  funext j
  simp [rmap]

lemma color_rotation_fixed (i : Fin k) (b : Fin m → K) :
    R ω b (colorVector ω i) = colorVector ω i := by
  change Lp.compMeasurePreserving (rotate b) (rotate_preserving ω b) _ = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (colorVector ω i) (rotate_preserving ω b),
    (rotate_preserving ω b).quasiMeasurePreserving.ae (color_ae ω i), color_ae ω i]
    with η h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, colorValue, rotate_apply, rmap_zero]

lemma sq_neg (x : V m r) : sq (-x) = sq x := by simp [sq]

/-- Properness: zero correlation of each colour at every algebraic vector of forbidden length. -/
lemma color_correlation (i : Fin k) (x : V m r) {d : ℝ} (hd : d ∈ D) (hx : sq x = d ^ 2) :
    ⟪colorVector ω i, T ω x (colorVector ω i)⟫_ℂ = 0 := by
  rw [translation_apply, L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [color_ae ω i,
    Lp.coeFn_compMeasurePreserving (colorVector ω i) (trans_preserving ω x),
    (trans_preserving ω x).quasiMeasurePreserving.ae (color_ae ω i)] with η h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, colorValue, trans_apply, zero_add]
  have hp : η.val 0 ≠ η.val x := η.property 0 x d hd (by rw [zero_sub, sq_neg, hx])
  by_cases hi : η.val 0 = i
  · have hj : η.val x ≠ i := fun h => hp (hi.trans h.symm)
    simp [hi, hj]
  · simp [hi]

/-! ### Block projections -/

instance plane_complete (j : Fin m) : CompleteSpace (space (A := E) (planeRep ω j)) :=
  (isClosed_space (A := E) (planeRep ω j)).completeSpace_coe

abbrev PJ (j : Fin m) : Hilbert ω →L[ℂ] Hilbert ω := (space (A := E) (planeRep ω j)).starProjection

lemma T_comm_plane (j : Fin m) (x : V m r) (z : E) (w : Hilbert ω) :
    T ω x (op (planeRep ω j) z w) = op (planeRep ω j) z (T ω x w) := by
  rw [planeRep_op, planeRep_op, T_comm]

lemma PJ_comm_T (j : Fin m) (x : V m r) (v : Hilbert ω) : PJ ω j (T ω x v) = T ω x (PJ ω j v) :=
  HN3.comm_projection (planeRep ω j) (translation ω x) (fun a w => T_comm_plane ω j x a w) v

lemma PJ_rotation_fixed (j : Fin m) (v : Hilbert ω) (b : Fin m → K) (hv : R ω b v = v) :
    R ω b (PJ ω j v) = PJ ω j v :=
  projection_covariance_fixed (planeRep ω j) (rotation ω b)
    (Homeomorph.mulLeft₀ (kCoeff (b j)) (kCoeff_ne_zero (b j))) (mul_zero _)
    (plane_covariance ω j b) v hv

/-- A projection onto the continuous vectors of one block preserves continuity in another. -/
lemma PJ_mem (i j : Fin m) {v : Hilbert ω} (hv : v ∈ space (A := E) (planeRep ω j)) :
    PJ ω i v ∈ space (A := E) (planeRep ω j) :=
  HN3.comm_mem_space (planeRep ω j) (PJ ω i)
    (fun z w => by rw [planeRep_op, planeRep_op, PJ_comm_T]) hv

/-- A generic algebraic vector has all block components nonzero. -/
def Generic (a : V m r) : Prop := ∀ j, a.1 j ≠ 0

/-- One block step: projecting a rotation-invariant vector onto the continuous vectors of block
`j` preserves its correlation at every algebraic `a` with `a.1 j ≠ 0`. -/
theorem PJ_correlation (j : Fin m) (w : Hilbert ω) (hw : ∀ b, R ω b w = w) (a : V m r)
    (ha : a.1 j ≠ 0) :
    ⟪PJ ω j w, T ω a (PJ ω j w)⟫_ℂ = ⟪w, T ω a w⟫_ℂ := by
  set g := PJ ω j w
  set b := w - g
  have hg : g ∈ space (A := E) (planeRep ω j) := (space (A := E) (planeRep ω j)).starProjection_apply_mem w
  have hb : b ∈ (space (A := E) (planeRep ω j))ᗮ :=
    (space (A := E) (planeRep ω j)).sub_starProjection_mem_orthogonal w
  have hbfix : ∀ κ, (blockRot ω j κ : Hilbert ω →L[ℂ] Hilbert ω) b = b := fun κ => by
    change R ω _ (w - g) = w - g
    rw [map_sub, hw, PJ_rotation_fixed ω j w _ (hw _)]
  let c : V m r := a - (Pi.single j (a.1 j), 0)
  have hc : c.1 j = 0 := by simp [c]
  let Y := translation ω c
  have hYU : ∀ z w, (Y : Hilbert ω →L[ℂ] Hilbert ω) (op (planeRep ω j) z w) =
      op (planeRep ω j) z ((Y : Hilbert ω →L[ℂ] Hilbert ω) w) := fun z w => T_comm_plane ω j _ z w
  have hYW : ∀ κ w, (Y : Hilbert ω →L[ℂ] Hilbert ω) ((blockRot ω j κ : Hilbert ω →L[ℂ] Hilbert ω) w) =
      (blockRot ω j κ : Hilbert ω →L[ℂ] Hilbert ω) ((Y : Hilbert ω →L[ℂ] Hilbert ω) w) := by
    intro κ w
    change T ω c (R ω _ w) = R ω _ (T ω c w)
    rw [R_T, rmap_mulSingle_of_zero j κ c hc]
  have hsplit : ∀ w, T ω a w = op (planeRep ω j) (a.1 j) ((Y : Hilbert ω →L[ℂ] Hilbert ω) w) := by
    intro w
    rw [planeRep_op]
    change T ω a w = T ω (Pi.single j (a.1 j), 0) (T ω c w)
    rw [← T_add]
    simp [c]
  have hbb : ⟪b, T ω a b⟫_ℂ = 0 := by
    rw [hsplit]
    exact HN3.twisted_residual (planeRep ω j) (blockRot ω j) (block_covariance ω j) Y hYU hYW b hb
      hbfix (a.1 j) ha
  have hTx : ∀ z w, T ω a (op (planeRep ω j) z w) = op (planeRep ω j) z (T ω a w) :=
    fun z w => T_comm_plane ω j a z w
  have h1 : ⟪g, T ω a b⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp (HN3.comm_mem_orthogonal (planeRep ω j) (translation ω a) hTx hb) g hg
  have h2 : ⟪b, T ω a g⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp hb _ (HN3.comm_mem_space (planeRep ω j) _ hTx hg)
  have hf : w = g + b := by simp [b]
  conv_rhs => rw [hf]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, hbb]
  simp

/-! ### Composition over a list of blocks -/

/-- `QL l` applies the block projections of the list `l`, last element first. -/
def QL : List (Fin m) → (Hilbert ω →L[ℂ] Hilbert ω)
  | [] => ContinuousLinearMap.id ℂ _
  | j :: l => (PJ ω j).comp (QL l)

@[simp] lemma QL_nil (v : Hilbert ω) : QL ω [] v = v := rfl
@[simp] lemma QL_cons (j : Fin m) (l : List (Fin m)) (v : Hilbert ω) :
    QL ω (j :: l) v = PJ ω j (QL ω l v) := rfl

lemma QL_comm_T (l : List (Fin m)) (x : V m r) (v : Hilbert ω) :
    QL ω l (T ω x v) = T ω x (QL ω l v) := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [QL_cons, QL_cons, ih, PJ_comm_T]

lemma QL_mem (l : List (Fin m)) (v : Hilbert ω) (j : Fin m) (hj : j ∈ l) :
    QL ω l v ∈ space (A := E) (planeRep ω j) := by
  induction l with
  | nil => simp at hj
  | cons i l ih =>
    rw [QL_cons]
    rcases List.mem_cons.mp hj with h | h
    · subst h; exact (space (A := E) (planeRep ω j)).starProjection_apply_mem _
    · exact PJ_mem ω i j (ih h)

lemma QL_fixed (l : List (Fin m)) (v : Hilbert ω) (hv : ∀ b, R ω b v = v) (b : Fin m → K) :
    R ω b (QL ω l v) = QL ω l v := by
  induction l generalizing b with
  | nil => exact hv b
  | cons j l ih => rw [QL_cons]; exact PJ_rotation_fixed ω j _ b (ih b)

lemma QL_correlation (l : List (Fin m)) (v : Hilbert ω) (hv : ∀ b, R ω b v = v) (a : V m r)
    (ha : Generic a) : ⟪QL ω l v, T ω a (QL ω l v)⟫_ℂ = ⟪v, T ω a v⟫_ℂ := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [QL_cons, PJ_correlation ω j _ (QL_fixed ω l v hv) a (ha j), ih]

lemma QL_range (l : List (Fin m)) (v : Hilbert ω)
    (hv : ∀ᵐ η ∂measure ω, (v η).im = 0 ∧ 0 ≤ (v η).re ∧ (v η).re ≤ 1) :
    ∀ᵐ η ∂measure ω, (QL ω l v η).im = 0 ∧ 0 ≤ (QL ω l v η).re ∧ (QL ω l v η).re ≤ 1 := by
  induction l with
  | nil => exact hv
  | cons j l ih =>
    rw [QL_cons]
    exact projection_range (measure ω) (planeRep ω j) (fun z : E => trans (Pi.single j z, 0))
      (fun z => trans_preserving ω (Pi.single j z, 0)) (fun z v => rfl) _ ih

/-! ### The label vectors -/

instance line_complete : CompleteSpace (space (A := AF) (lineRep ω)) :=
  (isClosed_space (A := AF) (lineRep ω)).completeSpace_coe

abbrev P0 : Hilbert ω →L[ℂ] Hilbert ω := (space (A := AF) (lineRep ω)).starProjection

/-- All block projections. -/
abbrev Qall : Hilbert ω →L[ℂ] Hilbert ω := QL ω (List.finRange m)

def gv (i : Fin k) : Hilbert ω := Qall ω (colorVector ω i)
def pv (i : Fin k) : Hilbert ω := P0 ω (gv ω i)
def wv (i : Fin k) : Hilbert ω := gv ω i - pv ω i

lemma line_comm (x : V m r) (t : AF) (w : Hilbert ω) :
    T ω x (op (lineRep ω) t w) = op (lineRep ω) t (T ω x w) := by
  rw [lineRep_op, lineRep_op, T_comm]

lemma P0_comm_T (x : V m r) (v : Hilbert ω) : P0 ω (T ω x v) = T ω x (P0 ω v) :=
  HN3.comm_projection (lineRep ω) (translation ω x) (fun a w => line_comm ω x a w) v

lemma gv_plane (i : Fin k) (j : Fin m) : gv ω i ∈ space (A := E) (planeRep ω j) :=
  QL_mem ω _ _ j (List.mem_finRange j)

lemma pv_line (i : Fin k) : pv ω i ∈ space (A := AF) (lineRep ω) :=
  (space (A := AF) (lineRep ω)).starProjection_apply_mem _

lemma P0_mem_plane (j : Fin m) {v : Hilbert ω} (hv : v ∈ space (A := E) (planeRep ω j)) :
    P0 ω v ∈ space (A := E) (planeRep ω j) :=
  HN3.comm_mem_space (planeRep ω j) (P0 ω)
    (fun z w => by rw [planeRep_op, planeRep_op]; exact P0_comm_T ω _ w) hv

lemma pv_plane (i : Fin k) (j : Fin m) : pv ω i ∈ space (A := E) (planeRep ω j) :=
  P0_mem_plane ω j (gv_plane ω i j)

lemma wv_plane (i : Fin k) (j : Fin m) : wv ω i ∈ space (A := E) (planeRep ω j) :=
  Submodule.sub_mem _ (gv_plane ω i j) (pv_plane ω i j)

lemma wv_orth (i : Fin k) : wv ω i ∈ (space (A := AF) (lineRep ω))ᗮ :=
  (space (A := AF) (lineRep ω)).sub_starProjection_mem_orthogonal _

lemma gv_correlation (i : Fin k) (x : V m r) (hg : Generic x) {d : ℝ} (hd : d ∈ D)
    (hx : sq x = d ^ 2) : ⟪gv ω i, T ω x (gv ω i)⟫_ℂ = 0 := by
  rw [gv, QL_correlation ω _ _ (color_rotation_fixed ω i) x hg]
  exact color_correlation ω i x hd hx

lemma corr_split (i : Fin k) (x : V m r) (hg : Generic x) {d : ℝ} (hd : d ∈ D)
    (hx : sq x = d ^ 2) :
    ⟪pv ω i, T ω x (pv ω i)⟫_ℂ = -⟪wv ω i, T ω x (wv ω i)⟫_ℂ := by
  have h0 := gv_correlation ω i x hg hd hx
  have hTx : ∀ a w, T ω x (op (lineRep ω) a w) = op (lineRep ω) a (T ω x w) := line_comm ω x
  have h1 : ⟪pv ω i, T ω x (wv ω i)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp
      (HN3.comm_mem_orthogonal (lineRep ω) (translation ω x) hTx (wv_orth ω i)) _ (pv_line ω i)
  have h2 : ⟪wv ω i, T ω x (pv ω i)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp (wv_orth ω i) _
      (HN3.comm_mem_space (lineRep ω) _ hTx (pv_line ω i))
  have hg' : gv ω i = pv ω i + wv ω i := by simp [wv]
  rw [hg', map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2] at h0
  linear_combination h0

/-! ### Range and sum -/

def oneV : Hilbert ω := (memLp_const (1 : ℂ)).toLp (fun _ : Space m r D k => (1 : ℂ))

lemma oneV_ae : oneV ω =ᵐ[measure ω] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _

lemma T_oneV (a : V m r) : T ω a (oneV ω) = oneV ω := by
  rw [translation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (oneV ω) (trans_preserving ω a),
    (trans_preserving ω a).quasiMeasurePreserving.ae (oneV_ae ω), oneV_ae ω] with η h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

lemma oneV_plane (j : Fin m) : oneV ω ∈ space (A := E) (planeRep ω j) := by
  change Tendsto (fun a : E => op (planeRep ω j) a (oneV ω)) (𝓝 0) (𝓝 (oneV ω))
  simp only [planeRep_op, T_oneV]
  exact tendsto_const_nhds

lemma oneV_line : oneV ω ∈ space (A := AF) (lineRep ω) := by
  change Tendsto (fun a : AF => op (lineRep ω) a (oneV ω)) (𝓝 0) (𝓝 (oneV ω))
  simp only [lineRep_op, T_oneV]
  exact tendsto_const_nhds

lemma QL_oneV (l : List (Fin m)) : QL ω l (oneV ω) = oneV ω := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [QL_cons, ih, Submodule.starProjection_eq_self_iff.mpr (oneV_plane ω j)]

lemma color_sum : ∑ i : Fin k, colorVector ω i = oneV ω := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ) (colorVector ω),
    ae_all_iff.mpr (color_ae ω), oneV_ae ω] with η h1 h2 h3
  rw [h1, h3]
  simp_rw [h2, colorValue]
  simp

lemma pv_sum : ∑ i : Fin k, pv ω i = oneV ω := by
  simp only [pv, gv]
  rw [← map_sum, ← map_sum, color_sum, QL_oneV,
    Submodule.starProjection_eq_self_iff.mpr (oneV_line ω)]

lemma pv_range (i : Fin k) : ∀ᵐ η ∂measure ω,
    ((pv ω i) η).im = 0 ∧ 0 ≤ ((pv ω i) η).re ∧ ((pv ω i) η).re ≤ 1 := by
  apply projection_range (measure ω) (lineRep ω) (fun t : AF => trans (0, fun _ => t))
    (fun t => trans_preserving ω (0, fun _ => t)) (fun t v => rfl)
  apply QL_range
  filter_upwards [color_ae ω i] with η h
  rw [h]
  dsimp [colorValue]
  split_ifs <;> norm_num

end HNN
end
end OAI
