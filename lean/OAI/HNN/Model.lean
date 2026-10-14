import OAI.HN3.Line

/-!
# The n-dimensional label model

`ℝⁿ` with `n = 2m + r` is modelled as `(Fin m → ℂ) × (Fin r → ℝ)`; its algebraic points are
`V m r = (Fin m → E) × (Fin r → AF)`. Labelings of `V m r` avoiding a set `D` of distances form
a compact space with commuting actions of algebraic translations and blockwise algebraic
rotations. An invariant probability measure gives Koopman representations: one plane
representation per block and one representation along the last axes.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace HNN
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

abbrev AF := HN3.AF

/-- Algebraic points of `ℝ^(2m+r)`. -/
abbrev V (m r : ℕ) := (Fin m → E) × (Fin r → AF)

variable {m r : ℕ}

/-- Squared Euclidean norm of an algebraic point. -/
def sq (x : V m r) : ℝ := ∑ j, ‖(x.1 j : ℂ)‖ ^ 2 + ∑ i, ((x.2 i : ℝ)) ^ 2

/-- Blockwise rotation by algebraic units. -/
def rmap (b : Fin m → K) (x : V m r) : V m r := (fun j => kCoeff (b j) * x.1 j, x.2)

lemma sq_rmap_sub (b : Fin m → K) (x y : V m r) : sq (rmap b x - rmap b y) = sq (x - y) := by
  simp only [sq, rmap, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : ((kCoeff (b j) * x.1 j - kCoeff (b j) * y.1 j : E) : ℂ) =
      ((b j).val : ℂ) * ((x.1 j - y.1 j : E) : ℂ) := by
    push_cast [kCoeff]; ring
  rw [this, norm_mul, Circle.norm_coe, one_mul]

/-- Labelings with no two points at a distance in `D` of the same label. -/
def Proper (D : Set ℝ) {k : ℕ} (ω : V m r → Fin k) : Prop :=
  ∀ x y : V m r, ∀ d ∈ D, sq (x - y) = d ^ 2 → ω x ≠ ω y

abbrev Space (m r : ℕ) (D : Set ℝ) (k : ℕ) := {ω : V m r → Fin k // Proper D ω}

variable {D : Set ℝ} {k : ℕ}

lemma closed_proper : IsClosed {ω : V m r → Fin k | Proper D ω} := by
  unfold Proper
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun (x : V m r) => isClosed_iInter fun (y : V m r) =>
    isClosed_iInter fun d => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  have hc : Continuous (fun ω : V m r → Fin k => (ω x, ω y)) :=
    (continuous_apply x).prodMk (continuous_apply y)
  exact (isClosed_discrete {p : Fin k × Fin k | p.1 ≠ p.2}).preimage hc

instance : CompactSpace (Space m r D k) := isCompact_iff_compactSpace.mp closed_proper.isCompact

def trans (a : V m r) (ω : Space m r D k) : Space m r D k := ⟨fun x => ω.val (x + a), by
  intro x y d hd h
  apply ω.property (x + a) (y + a) d hd
  simpa only [add_sub_add_right_eq_sub] using h⟩

def rotate (b : Fin m → K) (ω : Space m r D k) : Space m r D k := ⟨fun x => ω.val (rmap b x), by
  intro x y d hd h
  apply ω.property (rmap b x) (rmap b y) d hd
  rw [sq_rmap_sub, h]⟩

@[simp] lemma trans_apply (a : V m r) (ω : Space m r D k) (x : V m r) :
    (trans a ω).val x = ω.val (x + a) := rfl
@[simp] lemma rotate_apply (b : Fin m → K) (ω : Space m r D k) (x : V m r) :
    (rotate b ω).val x = ω.val (rmap b x) := rfl

lemma trans_continuous (a : V m r) : Continuous (trans (D := D) (k := k) a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma rotate_continuous (b : Fin m → K) : Continuous (rotate (r := r) (D := D) (k := k) b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (rmap b x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space m r D k) : trans 0 ω = ω := by
  apply Subtype.ext; funext x; simp

lemma trans_add (a b : V m r) (ω : Space m r D k) : trans a (trans b ω) = trans (a + b) ω := by
  apply Subtype.ext; funext x; simp [add_assoc]

lemma kCoeff_one : kCoeff 1 = 1 := rfl

lemma rmap_one (x : V m r) : rmap 1 x = x := by
  simp [rmap]

lemma rmap_mul (a b : Fin m → K) (x : V m r) : rmap a (rmap b x) = rmap (b * a) x := by
  have he : ∀ j, kCoeff ((b * a) j) = kCoeff (b j) * kCoeff (a j) := fun j => rfl
  simp only [rmap, he]
  refine Prod.ext ?_ rfl
  funext j
  simp only
  ring

lemma rmap_add (b : Fin m → K) (x y : V m r) : rmap b (x + y) = rmap b x + rmap b y := by
  simp only [rmap, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add]; rfl

@[simp] lemma rotate_one (ω : Space m r D k) : rotate 1 ω = ω := by
  apply Subtype.ext; funext x; simp [rmap_one]

lemma rotate_mul (a b : Fin m → K) (ω : Space m r D k) :
    rotate a (rotate b ω) = rotate (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (rmap b (rmap a x)) = ω.val (rmap (a * b) x)
  rw [rmap_mul]

lemma covariance (a : V m r) (b : Fin m → K) (ω : Space m r D k) :
    trans a (rotate b ω) = rotate b (trans (rmap b a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, rmap_add]

def transHomeo (a : V m r) : Space m r D k ≃ₜ Space m r D k where
  toFun := trans a
  invFun := trans (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := trans_continuous a
  continuous_invFun := trans_continuous (-a)

def rotateHomeo (b : Fin m → K) : Space m r D k ≃ₜ Space m r D k where
  toFun := rotate b
  invFun := rotate b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := rotate_continuous b
  continuous_invFun := rotate_continuous b⁻¹

/-- The algebraic translation group with the discrete topology. -/
def TV (m r : ℕ) := V m r
instance : AddCommGroup (TV m r) := inferInstanceAs (AddCommGroup (V m r))
instance : TopologicalSpace (TV m r) := ⊥
instance : DiscreteTopology (TV m r) := ⟨rfl⟩
def toTV (a : V m r) : TV m r := a
def ofTV (a : TV m r) : V m r := a

/-- The blockwise rotation group, discrete. -/
abbrev TB (m : ℕ) := Fin m → Rot

def rotOf (b : TB m) : Fin m → K := fun j => rotMul (b j)
def ofRot (b : Fin m → K) : TB m := fun j => mulRot (b j)

def tr (a : TV m r) : Space m r D k → Space m r D k := trans (ofTV a)
def ro (b : TB m) : Space m r D k → Space m r D k := rotate (rotOf b)

def measure (ω : Space m r D k) : Measure (Space m r D k) :=
  EuclideanFiveColor.StationaryMean.measure (tr (r := r) (D := D) (k := k))
    (ro (r := r) (D := D) (k := k)) ω

instance (ω : Space m r D k) : IsProbabilityMeasure (measure ω) :=
  inferInstanceAs (IsProbabilityMeasure (EuclideanFiveColor.StationaryMean.measure
    (tr (r := r) (D := D) (k := k)) (ro (r := r) (D := D) (k := k)) ω))

lemma trans_preserving (ω : Space m r D k) (a : V m r) :
    MeasurePreserving (trans a) (measure ω) (measure ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average _ _ ω (transHomeo a)
  intro f
  exact EuclideanFiveColor.StationaryMean.average_translation _ _ ω
    (fun a b x => trans_add _ _ x) (fun b a => toTV (rmap (rotOf b) (ofTV a)))
    (fun a b x => covariance _ _ x) (toTV a) f (trans_continuous a)

lemma rotate_preserving (ω : Space m r D k) (b : Fin m → K) :
    MeasurePreserving (rotate b) (measure ω) (measure ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average _ _ ω (rotateHomeo b)
  intro f
  exact EuclideanFiveColor.StationaryMean.average_rotation _ _ ω
    (fun a b x => rotate_mul _ _ x) (ofRot b) f (rotate_continuous b)

variable (ω : Space m r D k)

abbrev Hilbert := Lp ℂ 2 (measure ω)

def translation (a : V m r) : unitary (Hilbert ω →L[ℂ] Hilbert ω) :=
  Koopman.unitary (measure ω) (transHomeo a).toMeasurableEquiv (trans_preserving ω a)

def rotation (b : Fin m → K) : unitary (Hilbert ω →L[ℂ] Hilbert ω) :=
  Koopman.unitary (measure ω) (rotateHomeo b).toMeasurableEquiv (rotate_preserving ω b)

lemma translation_apply (a : V m r) (v : Hilbert ω) :
    (translation ω a : Hilbert ω →L[ℂ] Hilbert ω) v =
      Lp.compMeasurePreserving (trans a) (trans_preserving ω a) v := rfl

lemma rotation_apply (b : Fin m → K) (v : Hilbert ω) :
    (rotation ω b : Hilbert ω →L[ℂ] Hilbert ω) v =
      Lp.compMeasurePreserving (rotate b) (rotate_preserving ω b) v := rfl

abbrev T (a : V m r) : Hilbert ω →L[ℂ] Hilbert ω := (translation ω a : Hilbert ω →L[ℂ] Hilbert ω)
abbrev R (b : Fin m → K) : Hilbert ω →L[ℂ] Hilbert ω :=
  (rotation ω b : Hilbert ω →L[ℂ] Hilbert ω)

lemma T_zero (v : Hilbert ω) : T ω 0 v = v := by
  change Lp.compMeasurePreserving (trans 0) (trans_preserving ω 0) v = v
  have he : trans (D := D) (k := k) (0 : V m r) = id := funext trans_zero
  simp only [he, Lp.compMeasurePreserving_id_apply]

lemma T_add (a b : V m r) (v : Hilbert ω) : T ω (a + b) v = T ω a (T ω b v) := by
  change Lp.compMeasurePreserving (trans (a + b)) _ v =
    Lp.compMeasurePreserving (trans a) _ (Lp.compMeasurePreserving (trans b) _ v)
  rw [← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact (congrArg (fun c => trans c x) (add_comm _ _)).trans (trans_add _ _ x).symm

lemma T_comm (a b : V m r) (v : Hilbert ω) : T ω a (T ω b v) = T ω b (T ω a v) := by
  rw [← T_add, ← T_add, add_comm]

lemma R_T (b : Fin m → K) (a : V m r) (v : Hilbert ω) :
    R ω b (T ω a v) = T ω (rmap b a) (R ω b v) := by
  simp only [R, T, rotation_apply, translation_apply, ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance a b x

/-- Translations within the `j`-th coordinate plane. -/
def planeRep (j : Fin m) : DiscreteE →* unitary (Hilbert ω →L[ℂ] Hilbert ω) where
  toFun a := translation ω (Pi.single j (Multiplicative.toAdd a), 0)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T ω (Pi.single j 0, 0) v = v
    rw [Pi.single_zero]
    exact T_zero ω v
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T ω ((Pi.single j (Multiplicative.toAdd a + Multiplicative.toAdd b), 0)) v =
      T ω (Pi.single j (Multiplicative.toAdd a), 0) (T ω (Pi.single j (Multiplicative.toAdd b), 0) v)
    rw [← T_add]
    congr 2
    refine Prod.ext ?_ (by simp)
    simp [Pi.single_add]

lemma planeRep_op (j : Fin m) (z : E) (v : Hilbert ω) :
    op (planeRep ω j) z v = T ω (Pi.single j z, 0) v := rfl

lemma rmap_single (b : Fin m → K) (j : Fin m) (z : E) :
    rmap b ((Pi.single j z, 0) : V m r) = (Pi.single j (kCoeff (b j) * z), 0) := by
  refine Prod.ext ?_ rfl
  funext i
  by_cases h : i = j
  · subst h; simp [rmap]
  · simp [rmap, Pi.single_apply, h]

lemma plane_covariance (j : Fin m) (b : Fin m → K) (z : E) (v : Hilbert ω) :
    R ω b (op (planeRep ω j) z v) = op (planeRep ω j) (kCoeff (b j) * z) (R ω b v) := by
  rw [planeRep_op, planeRep_op, R_T, rmap_single]

/-- Rotations of the `j`-th coordinate plane. -/
def blockRot (j : Fin m) (κ : K) : unitary (Hilbert ω →L[ℂ] Hilbert ω) :=
  rotation ω (Pi.mulSingle j κ)

lemma block_covariance (j : Fin m) (κ : K) (z : E) (v : Hilbert ω) :
    (blockRot ω j κ : Hilbert ω →L[ℂ] Hilbert ω) (op (planeRep ω j) z v) =
      op (planeRep ω j) (kCoeff κ * z) ((blockRot ω j κ : Hilbert ω →L[ℂ] Hilbert ω) v) := by
  have := plane_covariance ω j (Pi.mulSingle j κ) z v
  rwa [Pi.mulSingle_eq_same] at this

lemma rmap_mulSingle_of_zero (j : Fin m) (κ : K) (c : V m r) (hc : c.1 j = 0) :
    rmap (Pi.mulSingle j κ) c = c := by
  refine Prod.ext ?_ rfl
  funext i
  by_cases h : i = j
  · subst h; simp [rmap, hc]
  · simp [rmap, Pi.mulSingle_apply, h]

/-- Translations along the last axes, all coordinates equal. -/
def lineRep : Multiplicative AF →* unitary (Hilbert ω →L[ℂ] Hilbert ω) where
  toFun t := translation ω (0, fun _ => Multiplicative.toAdd t)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact T_zero ω v
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T ω ((0, fun _ => Multiplicative.toAdd a + Multiplicative.toAdd b)) v =
      T ω (0, fun _ => Multiplicative.toAdd a) (T ω (0, fun _ => Multiplicative.toAdd b) v)
    rw [← T_add]
    congr 2
    refine Prod.ext (by simp) ?_
    funext i
    simp

lemma lineRep_op (t : AF) (v : Hilbert ω) : op (lineRep ω) t v = T ω (0, fun _ => t) v := rfl

lemma R_line (b : Fin m → K) (s : Fin r → AF) (v : Hilbert ω) :
    R ω b (T ω (0, s) v) = T ω (0, s) (R ω b v) := by
  rw [R_T]
  congr 2
  refine Prod.ext ?_ rfl
  funext j
  simp [rmap]

end HNN
end
end OAI
