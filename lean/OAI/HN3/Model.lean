import OAI.Geometry.PlaneColoring.BorelTransfer

/-!
# Three-dimensional label model

Proper labelings of the algebraic points `E × AF` of `ℂ × ℝ ≅ ℝ³`, an invariant law under
algebraic translations and algebraic rotations about the vertical axis, and the Koopman
representations on its `L²` space.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
namespace HN3
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

abbrev AF := algebraicClosure ℚ ℝ

instance AF_countable : Countable AF := by
  apply Set.Countable.to_subtype
  have heq : (algebraicClosure ℚ ℝ : Set ℝ) = {x | IsAlgebraic ℚ x} := by
    ext z; exact mem_algebraicClosure_iff
  rw [heq]
  exact Algebraic.countable ℚ ℝ

/-- Algebraic points of three-space. -/
abbrev V := E × AF

/-- Squared Euclidean norm of an algebraic point. -/
def sq (x : V) : ℝ := ‖(x.1 : ℂ)‖ ^ 2 + ((x.2 : ℝ)) ^ 2

/-- Rotation about the vertical axis by an algebraic unit. -/
def rmap (b : K) (x : V) : V := (kCoeff b * x.1, x.2)

lemma sq_rmap_sub (b : K) (x y : V) : sq (rmap b x - rmap b y) = sq (x - y) := by
  simp only [sq, rmap, Prod.fst_sub, Prod.snd_sub]
  congr 1
  have : ((kCoeff b * x.1 - kCoeff b * y.1 : E) : ℂ) = (b.val : ℂ) * ((x.1 - y.1 : E) : ℂ) := by
    push_cast [kCoeff]; ring
  rw [this, norm_mul, Circle.norm_coe, one_mul]

variable (k : ℕ)

def Proper (ω : V → Fin k) : Prop := ∀ x y : V, sq (x - y) = 1 → ω x ≠ ω y
abbrev Space := {ω : V → Fin k // Proper k ω}

lemma closed_proper : IsClosed {ω : V → Fin k | Proper k ω} := by
  unfold Proper
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun (x : V) => isClosed_iInter fun (y : V) => isClosed_iInter fun _ => ?_
  have hc : Continuous (fun ω : V → Fin k => (ω x, ω y)) :=
    (continuous_apply x).prodMk (continuous_apply y)
  exact (isClosed_discrete {p : Fin k × Fin k | p.1 ≠ p.2}).preimage hc

instance : CompactSpace (Space k) := isCompact_iff_compactSpace.mp (closed_proper k).isCompact

def trans (a : V) (ω : Space k) : Space k := ⟨fun x => ω.val (x + a), by
  intro x y h
  apply ω.property (x + a) (y + a)
  simpa only [add_sub_add_right_eq_sub] using h⟩

def rotate (b : K) (ω : Space k) : Space k := ⟨fun x => ω.val (rmap b x), by
  intro x y h
  apply ω.property (rmap b x) (rmap b y)
  rw [sq_rmap_sub, h]⟩

@[simp] lemma trans_apply (a : V) (ω : Space k) (x : V) : (trans k a ω).val x = ω.val (x + a) := rfl
@[simp] lemma rotate_apply (b : K) (ω : Space k) (x : V) :
    (rotate k b ω).val x = ω.val (rmap b x) := rfl

lemma trans_continuous (a : V) : Continuous (trans k a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma rotate_continuous (b : K) : Continuous (rotate k b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (rmap b x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space k) : trans k 0 ω = ω := by apply Subtype.ext; funext x; simp

lemma trans_add (a b : V) (ω : Space k) : trans k a (trans k b ω) = trans k (a + b) ω := by
  apply Subtype.ext; funext x; simp [add_assoc]

lemma rmap_one (x : V) : rmap 1 x = x := by
  have h1 : kCoeff 1 = 1 := rfl
  simp [rmap, h1]

lemma rmap_mul (a b : K) (x : V) : rmap a (rmap b x) = rmap (b * a) x := by
  have he : kCoeff (b * a) = kCoeff b * kCoeff a := rfl
  simp only [rmap, he]; ext <;> simp; ring

lemma rmap_add (b : K) (x y : V) : rmap b (x + y) = rmap b x + rmap b y := by
  simp only [rmap, Prod.fst_add, Prod.snd_add, mul_add]; rfl

@[simp] lemma rotate_one (ω : Space k) : rotate k 1 ω = ω := by
  apply Subtype.ext; funext x; simp [rmap_one]

lemma rotate_mul (a b : K) (ω : Space k) : rotate k a (rotate k b ω) = rotate k (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (rmap b (rmap a x)) = ω.val (rmap (a * b) x)
  rw [rmap_mul]

lemma covariance (a : V) (b : K) (ω : Space k) :
    trans k a (rotate k b ω) = rotate k b (trans k (rmap b a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, rmap_add]

def transHomeo (a : V) : Space k ≃ₜ Space k where
  toFun := trans k a
  invFun := trans k (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := trans_continuous k a
  continuous_invFun := trans_continuous k (-a)

def rotateHomeo (b : K) : Space k ≃ₜ Space k where
  toFun := rotate k b
  invFun := rotate k b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := rotate_continuous k b
  continuous_invFun := rotate_continuous k b⁻¹

/-- The algebraic translation group with the discrete topology. -/
def TV := V
instance : AddCommGroup TV := inferInstanceAs (AddCommGroup V)
instance : TopologicalSpace TV := ⊥
instance : DiscreteTopology TV := ⟨rfl⟩
def toTV (a : V) : TV := a
def ofTV (a : TV) : V := a

def tr (a : TV) : Space k → Space k := trans k (ofTV a)
def ro (b : Rot) : Space k → Space k := rotate k (rotMul b)

def measure (ω : Space k) : Measure (Space k) :=
  EuclideanFiveColor.StationaryMean.measure (tr k) (ro k) ω

instance (ω : Space k) : IsProbabilityMeasure (measure k ω) :=
  inferInstanceAs (IsProbabilityMeasure (EuclideanFiveColor.StationaryMean.measure (tr k) (ro k) ω))

lemma trans_preserving (ω : Space k) (a : V) :
    MeasurePreserving (trans k a) (measure k ω) (measure k ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average (tr k) (ro k) ω (transHomeo k a)
  intro f
  exact EuclideanFiveColor.StationaryMean.average_translation (tr k) (ro k) ω
    (fun a b x => trans_add k _ _ x) (fun b a => toTV (rmap (rotMul b) (ofTV a)))
    (fun a b x => covariance k _ _ x) (toTV a) f (trans_continuous k a)

lemma rotate_preserving (ω : Space k) (b : K) :
    MeasurePreserving (rotate k b) (measure k ω) (measure k ω) := by
  apply EuclideanFiveColor.StationaryMean.preserving_of_average (tr k) (ro k) ω (rotateHomeo k b)
  intro f
  exact EuclideanFiveColor.StationaryMean.average_rotation (tr k) (ro k) ω
    (fun a b x => rotate_mul k _ _ x) (mulRot b) f (rotate_continuous k b)

variable (ω : Space k)

abbrev Hilbert := Lp ℂ 2 (measure k ω)

def translation (a : V) : unitary (Hilbert k ω →L[ℂ] Hilbert k ω) :=
  Koopman.unitary (measure k ω) (transHomeo k a).toMeasurableEquiv (trans_preserving k ω a)

def rotation (b : K) : unitary (Hilbert k ω →L[ℂ] Hilbert k ω) :=
  Koopman.unitary (measure k ω) (rotateHomeo k b).toMeasurableEquiv (rotate_preserving k ω b)

lemma translation_apply (a : V) (v : Hilbert k ω) :
    (translation k ω a : Hilbert k ω →L[ℂ] Hilbert k ω) v =
      Lp.compMeasurePreserving (trans k a) (trans_preserving k ω a) v := rfl

lemma rotation_apply (b : K) (v : Hilbert k ω) :
    (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω) v =
      Lp.compMeasurePreserving (rotate k b) (rotate_preserving k ω b) v := rfl

/-- Short name for the operator of translation by `a`. -/
abbrev T (a : V) : Hilbert k ω →L[ℂ] Hilbert k ω := (translation k ω a : Hilbert k ω →L[ℂ] Hilbert k ω)
abbrev R (b : K) : Hilbert k ω →L[ℂ] Hilbert k ω := (rotation k ω b : Hilbert k ω →L[ℂ] Hilbert k ω)

lemma T_zero (v : Hilbert k ω) : T k ω 0 v = v := by
  change Lp.compMeasurePreserving (trans k 0) (trans_preserving k ω 0) v = v
  have he : trans k 0 = id := funext (trans_zero k)
  simp only [he, Lp.compMeasurePreserving_id_apply]

lemma T_add (a b : V) (v : Hilbert k ω) : T k ω (a + b) v = T k ω a (T k ω b v) := by
  change Lp.compMeasurePreserving (trans k (a + b)) _ v =
    Lp.compMeasurePreserving (trans k a) _ (Lp.compMeasurePreserving (trans k b) _ v)
  rw [← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact (congrArg (fun c => trans k c x) (add_comm _ _)).trans (trans_add k _ _ x).symm

lemma T_comm (a b : V) (v : Hilbert k ω) : T k ω a (T k ω b v) = T k ω b (T k ω a v) := by
  rw [← T_add, ← T_add, add_comm]

lemma R_T (b : K) (a : V) (v : Hilbert k ω) : R k ω b (T k ω a v) = T k ω (rmap b a) (R k ω b v) := by
  simp only [R, T, rotation_apply, translation_apply, ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance k a b x

/-- Plane translations as a representation of the discrete algebraic plane. -/
def planeRep : DiscreteE →* unitary (Hilbert k ω →L[ℂ] Hilbert k ω) where
  toFun a := translation k ω (Multiplicative.toAdd a, 0)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact T_zero k ω v
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T k ω ((Multiplicative.toAdd a + Multiplicative.toAdd b, 0)) v =
      T k ω (Multiplicative.toAdd a, 0) (T k ω (Multiplicative.toAdd b, 0) v)
    rw [← T_add]
    simp

lemma planeRep_op (z : E) (v : Hilbert k ω) : op (planeRep k ω) z v = T k ω (z, 0) v := rfl

lemma plane_covariance (b : K) (z : E) (v : Hilbert k ω) :
    R k ω b (op (planeRep k ω) z v) = op (planeRep k ω) (kCoeff b * z) (R k ω b v) := by
  rw [planeRep_op, planeRep_op, R_T]
  rfl

/-- Vertical translations as a representation of the real algebraic line. -/
def lineRep : Multiplicative AF →* unitary (Hilbert k ω →L[ℂ] Hilbert k ω) where
  toFun t := translation k ω (0, Multiplicative.toAdd t)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact T_zero k ω v
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T k ω ((0, Multiplicative.toAdd a + Multiplicative.toAdd b)) v =
      T k ω (0, Multiplicative.toAdd a) (T k ω (0, Multiplicative.toAdd b) v)
    rw [← T_add]
    simp

lemma lineRep_op (t : AF) (v : Hilbert k ω) : op (lineRep k ω) t v = T k ω (0, t) v := rfl

lemma R_line (b : K) (t : AF) (v : Hilbert k ω) :
    R k ω b (T k ω (0, t) v) = T k ω (0, t) (R k ω b v) := by
  rw [R_T]
  congr 2
  simp [rmap]

end HN3
end
end OAI
