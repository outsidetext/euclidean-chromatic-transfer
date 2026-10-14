import OAI.HN3.Model

/-!
# The independent-set model in three dimensions

Independent sets of the algebraic unit-distance graph on `V = E × AF`, encoded as
`{0,1}`-valued functions on `V`, form a compact space with continuous actions of algebraic
translations and algebraic rotations about the vertical axis.

Instead of averaging the orbit of a single point (as `EuclideanFiveColor.StationaryMean` does),
we average a *state*, i.e. a positive normalized linear functional `L` on `C(X, ℝ)`:
`f ↦ mean_b mean_a L (f ∘ r_b ∘ t_a)`. Riesz–Markov turns this into an invariant probability
measure. A random independent set with a per-vertex lower bound is such a state.
-/

set_option linter.unusedSectionVars false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction
namespace HN3
namespace Indep
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors
open PlaneFiveColor.InvariantMean

/-- A state on `C(X, ℝ)`: a positive normalized linear functional. -/
structure State (X : Type*) [TopologicalSpace X] where
  toFun : C(X, ℝ) → ℝ
  map_add : ∀ f g, toFun (f + g) = toFun f + toFun g
  map_smul : ∀ (c : ℝ) f, toFun (c • f) = c * toFun f
  nonneg : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ toFun f
  map_one : toFun 1 = 1

section StateMean
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (L : State X)

lemma State.mono {f g : C(X, ℝ)} (h : ∀ x, f x ≤ g x) : L.toFun f ≤ L.toFun g := by
  have := L.nonneg (g - f) (fun x => by simp [h x])
  have he : L.toFun (g - f) = L.toFun g - L.toFun f := by
    rw [sub_eq_add_neg, L.map_add, ← neg_one_smul ℝ f, L.map_smul]; ring
  linarith

lemma State.const (c : ℝ) : L.toFun (ContinuousMap.const X c) = c := by
  have : ContinuousMap.const X c = c • (1 : C(X, ℝ)) := by ext; simp
  rw [this, L.map_smul, L.map_one, mul_one]

lemma State.abs_le (f : C(X, ℝ)) : |L.toFun f| ≤ ‖f‖ := by
  rw [_root_.abs_le]
  constructor
  · have h := L.mono (f := ContinuousMap.const X (-‖f‖)) (g := f) (fun x => by
      have := f.norm_coe_le_norm x
      rw [Real.norm_eq_abs] at this
      simp only [ContinuousMap.const_apply]
      linarith [neg_abs_le (f x)])
    rwa [L.const] at h
  · have h := L.mono (f := f) (g := ContinuousMap.const X ‖f‖) (fun x => by
      have := f.norm_coe_le_norm x
      rw [Real.norm_eq_abs] at this
      simp only [ContinuousMap.const_apply]
      linarith [le_abs_self (f x)])
    rwa [L.const] at h

lemma comp_norm_le (f : C(X, ℝ)) (g : C(X, X)) : ‖f.comp g‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun _ => f.norm_coe_le_norm _

variable {A B : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  (t : A → C(X, X)) (r : B → C(X, X))

lemma sinner_bound (f : C(X, ℝ)) (b : B) (a : A) :
    ‖L.toFun ((f.comp (r b)).comp (t a))‖ ≤ ‖f‖ := by
  rw [Real.norm_eq_abs]
  exact (L.abs_le _).trans ((comp_norm_le _ _).trans (comp_norm_le _ _))

def sinner (f : C(X, ℝ)) (b : B) : A →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => L.toFun ((f.comp (r b)).comp (t a)))
    continuous_of_discreteTopology ‖f‖ (sinner_bound L t r f b)

lemma sinner_norm (f : C(X, ℝ)) (b : B) : ‖sinner L t r f b‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (sinner_bound L t r f b)

def souter (f : C(X, ℝ)) : B →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun b => mean (sinner L t r f b))
    continuous_of_discreteTopology ‖f‖ (fun b => (mean_norm_le _).trans (sinner_norm L t r f b))

def saverage (f : C(X, ℝ)) : ℝ := mean (souter L t r f)

lemma sinner_add (f g : C(X, ℝ)) (b : B) :
    sinner L t r (f + g) b = sinner L t r f b + sinner L t r g b := by
  ext a
  change L.toFun (((f + g).comp (r b)).comp (t a)) =
    L.toFun ((f.comp (r b)).comp (t a)) + L.toFun ((g.comp (r b)).comp (t a))
  rw [← L.map_add]
  rfl

lemma sinner_smul (c : ℝ) (f : C(X, ℝ)) (b : B) :
    sinner L t r (c • f) b = c • sinner L t r f b := by
  ext a
  change L.toFun (((c • f).comp (r b)).comp (t a)) = c * L.toFun ((f.comp (r b)).comp (t a))
  rw [← L.map_smul]
  rfl

lemma souter_add (f g : C(X, ℝ)) :
    souter L t r (f + g) = souter L t r f + souter L t r g := by
  ext b
  exact (congrArg mean (sinner_add L t r f g b)).trans (mean_add _ _)

lemma souter_smul (c : ℝ) (f : C(X, ℝ)) : souter L t r (c • f) = c • souter L t r f := by
  ext b
  exact (congrArg mean (sinner_smul L t r c f b)).trans (mean_smul _ _)

lemma saverage_add (f g : C(X, ℝ)) :
    saverage L t r (f + g) = saverage L t r f + saverage L t r g := by
  simp only [saverage, souter_add, mean_add]

lemma saverage_smul (c : ℝ) (f : C(X, ℝ)) : saverage L t r (c • f) = c * saverage L t r f := by
  simp only [saverage, souter_smul, mean_smul]

lemma saverage_mono {f g : C(X, ℝ)} (h : f ≤ g) : saverage L t r f ≤ saverage L t r g := by
  have hp : 0 ≤ saverage L t r (g - f) :=
    mean_nonneg _ fun b => mean_nonneg _ fun a => L.nonneg _ fun x => sub_nonneg.mpr (h _)
  have he : saverage L t r (g - f) = saverage L t r g - saverage L t r f := by
    rw [sub_eq_add_neg, saverage_add, ← neg_one_smul ℝ f, saverage_smul]; ring
  linarith

lemma saverage_const (c : ℝ) : saverage L t r (ContinuousMap.const X c) = c := by
  have hi (b : B) : sinner L t r (ContinuousMap.const X c) b = BoundedContinuousFunction.const A c := by
    ext a
    change L.toFun _ = c
    exact L.const c
  have ho : souter L t r (ContinuousMap.const X c) = BoundedContinuousFunction.const B c := by
    ext b
    change mean (sinner L t r _ b) = c
    rw [hi, mean_const]
  rw [saverage, ho, mean_const]

lemma saverage_translation (ht : ∀ a b x, t a (t b x) = t (a + b) x)
    (φ : B → A → A) (hc : ∀ a b x, t a (r b x) = r b (t (φ b a) x))
    (a : A) (f : C(X, ℝ)) :
    saverage L t r (f.comp (t a)) = saverage L t r f := by
  unfold saverage
  congr 1
  ext b
  change mean (sinner L t r (f.comp (t a)) b) = mean (sinner L t r f b)
  have he : sinner L t r (f.comp (t a)) b = shift (φ b a) (sinner L t r f b) := by
    ext z
    change L.toFun (((f.comp (t a)).comp (r b)).comp (t z)) =
      L.toFun ((f.comp (r b)).comp (t (z + φ b a)))
    congr 1
    ext x
    change f (t a (r b (t z x))) = f (r b (t (z + φ b a) x))
    rw [hc, ht, add_comm]
  rw [he, mean_shift]

lemma saverage_rotation (hr : ∀ a b x, r a (r b x) = r (a + b) x)
    (b : B) (f : C(X, ℝ)) :
    saverage L t r (f.comp (r b)) = saverage L t r f := by
  unfold saverage
  have he : souter L t r (f.comp (r b)) = shift b (souter L t r f) := by
    ext c
    change mean (sinner L t r (f.comp (r b)) c) = mean (sinner L t r f (c + b))
    congr 1
    ext z
    change L.toFun (((f.comp (r b)).comp (r c)).comp (t z)) =
      L.toFun ((f.comp (r (c + b))).comp (t z))
    congr 1
    ext x
    change f (r b (r c (t z x))) = f (r (c + b) (t z x))
    rw [hr, add_comm]
  rw [he, mean_shift]

variable [T2Space X] [MeasurableSpace X] [BorelSpace X]

def sfunctional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := saverage L t r f.toContinuousMap
  map_add' := fun f g => saverage_add L t r f.toContinuousMap g.toContinuousMap
  map_smul' := fun c f => saverage_smul L t r c f.toContinuousMap
  monotone' := fun _ _ h => saverage_mono L t r h

def smeasure : Measure X := RealRMK.rieszMeasure (sfunctional L t r)

instance : IsFiniteMeasure (smeasure L t r) := by dsimp [smeasure]; infer_instance
instance : (smeasure L t r).Regular := by dsimp [smeasure]; infer_instance

lemma sintegral (f : C(X, ℝ)) : ∫ x, f x ∂smeasure L t r = saverage L t r f :=
  RealRMK.integral_rieszMeasure (sfunctional L t r)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)

instance : IsProbabilityMeasure (smeasure L t r) := by
  have he := sintegral L t r (ContinuousMap.const X 1)
  rw [saverage_const] at he
  change (∫ _ : X, (1 : ℝ) ∂smeasure L t r) = 1 at he
  simp only [integral_const, smul_eq_mul, mul_one] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he

lemma spreserving_of_average (s : X ≃ₜ X)
    (hav : ∀ f : C(X, ℝ), saverage L t r (f.comp ⟨s, s.continuous⟩) = saverage L t r f) :
    MeasurePreserving s (smeasure L t r) (smeasure L t r) := by
  refine ⟨s.continuous.measurable, ?_⟩
  have : (Measure.map s (smeasure L t r)).Regular := Measure.Regular.map s
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(smeasure L t r).map s) =
    ∫ x, f.toContinuousMap x ∂smeasure L t r
  rw [integral_map s.continuous.measurable.aemeasurable
    f.continuous.measurable.aestronglyMeasurable]
  exact (sintegral L t r (f.toContinuousMap.comp ⟨s, s.continuous⟩)).trans
    ((hav f.toContinuousMap).trans (sintegral L t r f.toContinuousMap).symm)

end StateMean

/-! ## Independent sets of the algebraic unit-distance graph -/

def IsIndep (ω : V → Fin 2) : Prop := ∀ x y : V, sq (x - y) = 1 → ¬ (ω x = 1 ∧ ω y = 1)
abbrev ISpace := {ω : V → Fin 2 // IsIndep ω}

lemma closed_indep : IsClosed {ω : V → Fin 2 | IsIndep ω} := by
  unfold IsIndep
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun (x : V) => isClosed_iInter fun (y : V) => isClosed_iInter fun _ => ?_
  have hc : Continuous (fun ω : V → Fin 2 => (ω x, ω y)) :=
    (continuous_apply x).prodMk (continuous_apply y)
  exact (isClosed_discrete {p : Fin 2 × Fin 2 | ¬ (p.1 = 1 ∧ p.2 = 1)}).preimage hc

instance : CompactSpace ISpace := isCompact_iff_compactSpace.mp closed_indep.isCompact

def trans (a : V) (ω : ISpace) : ISpace := ⟨fun x => ω.val (x + a), by
  intro x y h
  apply ω.property (x + a) (y + a)
  simpa only [add_sub_add_right_eq_sub] using h⟩

def rotate (b : K) (ω : ISpace) : ISpace := ⟨fun x => ω.val (rmap b x), by
  intro x y h
  apply ω.property (rmap b x) (rmap b y)
  rw [sq_rmap_sub, h]⟩

@[simp] lemma trans_apply (a : V) (ω : ISpace) (x : V) : (trans a ω).val x = ω.val (x + a) := rfl
@[simp] lemma rotate_apply (b : K) (ω : ISpace) (x : V) :
    (rotate b ω).val x = ω.val (rmap b x) := rfl

lemma trans_continuous (a : V) : Continuous (trans a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma rotate_continuous (b : K) : Continuous (rotate b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (rmap b x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : ISpace) : trans 0 ω = ω := by apply Subtype.ext; funext x; simp

lemma trans_add (a b : V) (ω : ISpace) : trans a (trans b ω) = trans (a + b) ω := by
  apply Subtype.ext; funext x; simp [add_assoc]

@[simp] lemma rotate_one (ω : ISpace) : rotate 1 ω = ω := by
  apply Subtype.ext; funext x; simp [rmap_one]

lemma rotate_mul (a b : K) (ω : ISpace) : rotate a (rotate b ω) = rotate (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (rmap b (rmap a x)) = ω.val (rmap (a * b) x)
  rw [rmap_mul]

lemma covariance (a : V) (b : K) (ω : ISpace) :
    trans a (rotate b ω) = rotate b (trans (rmap b a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, rmap_add]

def transHomeo (a : V) : ISpace ≃ₜ ISpace where
  toFun := trans a
  invFun := trans (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := trans_continuous a
  continuous_invFun := trans_continuous (-a)

def rotateHomeo (b : K) : ISpace ≃ₜ ISpace where
  toFun := rotate b
  invFun := rotate b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := rotate_continuous b
  continuous_invFun := rotate_continuous b⁻¹

def tC (a : TV) : C(ISpace, ISpace) := ⟨trans (ofTV a), trans_continuous _⟩
def rC (b : Rot) : C(ISpace, ISpace) := ⟨rotate (rotMul b), rotate_continuous _⟩

variable (L : State ISpace)

/-- The invariant law obtained by averaging the state `L`. -/
def measure : Measure ISpace := smeasure L tC rC

instance : IsProbabilityMeasure (measure L) :=
  inferInstanceAs (IsProbabilityMeasure (smeasure L tC rC))

lemma integral_measure (f : C(ISpace, ℝ)) : ∫ x, f x ∂measure L = saverage L tC rC f :=
  sintegral L tC rC f

lemma trans_preserving (a : V) :
    MeasurePreserving (trans a) (measure L) (measure L) := by
  apply spreserving_of_average L tC rC (transHomeo a)
  intro f
  exact saverage_translation L tC rC (fun a b x => trans_add _ _ x)
    (fun b a => toTV (rmap (rotMul b) (ofTV a))) (fun a b x => covariance _ _ x) (toTV a) f

lemma rotate_preserving (b : K) :
    MeasurePreserving (rotate b) (measure L) (measure L) := by
  apply spreserving_of_average L tC rC (rotateHomeo b)
  intro f
  exact saverage_rotation L tC rC (fun a b x => rotate_mul _ _ x) (mulRot b) f

abbrev Hilbert := Lp ℂ 2 (measure L)

def translation (a : V) : unitary (Hilbert L →L[ℂ] Hilbert L) :=
  Koopman.unitary (measure L) (transHomeo a).toMeasurableEquiv (trans_preserving L a)

def rotation (b : K) : unitary (Hilbert L →L[ℂ] Hilbert L) :=
  Koopman.unitary (measure L) (rotateHomeo b).toMeasurableEquiv (rotate_preserving L b)

lemma translation_apply (a : V) (v : Hilbert L) :
    (translation L a : Hilbert L →L[ℂ] Hilbert L) v =
      Lp.compMeasurePreserving (trans a) (trans_preserving L a) v := rfl

lemma rotation_apply (b : K) (v : Hilbert L) :
    (rotation L b : Hilbert L →L[ℂ] Hilbert L) v =
      Lp.compMeasurePreserving (rotate b) (rotate_preserving L b) v := rfl

abbrev T (a : V) : Hilbert L →L[ℂ] Hilbert L := (translation L a : Hilbert L →L[ℂ] Hilbert L)
abbrev R (b : K) : Hilbert L →L[ℂ] Hilbert L := (rotation L b : Hilbert L →L[ℂ] Hilbert L)

lemma T_zero (v : Hilbert L) : T L 0 v = v := by
  change Lp.compMeasurePreserving (trans 0) (trans_preserving L 0) v = v
  have he : trans 0 = id := funext trans_zero
  simp only [he, Lp.compMeasurePreserving_id_apply]

lemma T_add (a b : V) (v : Hilbert L) : T L (a + b) v = T L a (T L b v) := by
  change Lp.compMeasurePreserving (trans (a + b)) _ v =
    Lp.compMeasurePreserving (trans a) _ (Lp.compMeasurePreserving (trans b) _ v)
  rw [← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact (congrArg (fun c => trans c x) (add_comm _ _)).trans (trans_add _ _ x).symm

lemma T_comm (a b : V) (v : Hilbert L) : T L a (T L b v) = T L b (T L a v) := by
  rw [← T_add, ← T_add, add_comm]

lemma R_T (b : K) (a : V) (v : Hilbert L) : R L b (T L a v) = T L (rmap b a) (R L b v) := by
  simp only [R, T, rotation_apply, translation_apply, ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance a b x

def planeRep : DiscreteE →* unitary (Hilbert L →L[ℂ] Hilbert L) where
  toFun a := translation L (Multiplicative.toAdd a, 0)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact T_zero L v
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T L ((Multiplicative.toAdd a + Multiplicative.toAdd b, 0)) v =
      T L (Multiplicative.toAdd a, 0) (T L (Multiplicative.toAdd b, 0) v)
    rw [← T_add]
    simp

lemma planeRep_op (z : E) (v : Hilbert L) : op (planeRep L) z v = T L (z, 0) v := rfl

lemma plane_covariance (b : K) (z : E) (v : Hilbert L) :
    R L b (op (planeRep L) z v) = op (planeRep L) (kCoeff b * z) (R L b v) := by
  rw [planeRep_op, planeRep_op, R_T]
  rfl

def lineRep : Multiplicative AF →* unitary (Hilbert L →L[ℂ] Hilbert L) where
  toFun t := translation L (0, Multiplicative.toAdd t)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    exact T_zero L v
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change T L ((0, Multiplicative.toAdd a + Multiplicative.toAdd b)) v =
      T L (0, Multiplicative.toAdd a) (T L (0, Multiplicative.toAdd b) v)
    rw [← T_add]
    simp

lemma lineRep_op (t : AF) (v : Hilbert L) : op (lineRep L) t v = T L (0, t) v := rfl

lemma R_line (b : K) (t : AF) (v : Hilbert L) :
    R L b (T L (0, t) v) = T L (0, t) (R L b v) := by
  rw [R_T]
  congr 2
  simp [rmap]

end Indep
end HN3
end
end OAI
