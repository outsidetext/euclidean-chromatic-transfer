import OAI.Soifer.Torus
import OAI.HNN.Corollary

/-!
# From a bounded plane set to a torus set

For `A ⊆ [-T,T]²` and `L > 2T`, the set `E = {θ | L·lift(θ) ∈ A}` of the unit torus, where
`lift` takes representatives in `(-1/2, 1/2]`, has measure `|A|/L²`; and if `2T + r < L` then
torus translates by `(r/L)u`, `|u| = 1`, of points of `E` that stay in `E` come from pairs of
points of `A` at plane distance exactly `r`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set UnitAddTorus
open OAI.EuclideanFiveColor OAI.HNN

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Representative of a point of `ℝ/ℤ` in `(-1/2, 1/2]`. -/
def rep (x : UnitAddCircle) : ℝ := (AddCircle.equivIoc 1 (-1 / 2) x : ℝ)

lemma rep_measurable : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc 1 (-1 / 2)).measurable

lemma rep_coe (x : UnitAddCircle) : ((rep x : ℝ) : UnitAddCircle) = x := AddCircle.coe_equivIoc

lemma rep_of_mem {y : ℝ} (hy : y ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) :
    rep (y : UnitAddCircle) = y := AddCircle.equivIoc_coe_of_mem hy

/-- The plane point `L · lift θ`. -/
def lift (L : ℝ) (θ : Tor) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i => L * rep (θ i))

lemma lift_measurable (L : ℝ) : Measurable (lift L) :=
  (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun i => (rep_measurable.comp (measurable_pi_apply i)).const_mul L)

/-- The torus set attached to `A`. -/
def torusSet (L : ℝ) (A : Set (EuclideanSpace ℝ (Fin 2))) : Set Tor := lift L ⁻¹' A

lemma torusSet_measurable (L : ℝ) {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) :
    MeasurableSet (torusSet L A) := lift_measurable L hA

lemma circle_eq_int {a b : ℝ} (h : (a : UnitAddCircle) = (b : UnitAddCircle)) :
    ∃ m : ℤ, a - b = m := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp h)
  exact ⟨k, by rw [← hk, zsmul_eq_mul, mul_one]⟩

lemma int_eq_zero_of_abs_lt {m : ℤ} {L : ℝ} (hL : 0 < L) (h : |(m : ℝ) * L| < L) : m = 0 := by
  rw [abs_mul, abs_of_pos hL] at h
  have h1 : |(m : ℝ)| < 1 := by nlinarith [abs_nonneg (m : ℝ)]
  have h2 := abs_lt.mp h1
  have h3 : (-1 : ℤ) < m := by exact_mod_cast h2.1
  have h4 : m < 1 := by exact_mod_cast h2.2
  omega

/-- Torus translates by `(r/L)u` inside the torus set come from plane distances `r`. -/
lemma torusSet_avoid {L T r : ℝ} (hL : 0 < L) (hr : 0 < r) (hTL : 2 * T + r < L)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hAT : A ⊆ cube 2 T)
    (hAr : ∀ x ∈ A, ∀ y ∈ A, dist x y ≠ r) (t : Angles) :
    ∀ θ ∈ torusSet L A, θ + tp ((r / L) • direction t) ∉ torusSet L A := by
  intro θ hθ hθ'
  set u : ℂ := (r / L) • direction t with hu
  set x := lift L θ
  set y := lift L (θ + tp u)
  have hx : x ∈ A := hθ
  have hy : y ∈ A := hθ'
  have hcomp : ∀ i : Fin 2, y.ofLp i = x.ofLp i + L * ![u.re, u.im] i := by
    intro i
    have hc : ((rep ((θ + tp u) i) : ℝ) : UnitAddCircle) =
        ((rep (θ i) + ![u.re, u.im] i : ℝ) : UnitAddCircle) := by
      rw [rep_coe, AddCircle.coe_add, rep_coe]
      rfl
    obtain ⟨m, hm⟩ := circle_eq_int hc
    have hxi : |x.ofLp i| ≤ T := hAT hx i
    have hyi : |y.ofLp i| ≤ T := hAT hy i
    have hui : |![u.re, u.im] i| ≤ ‖u‖ := by
      fin_cases i
      · exact Complex.abs_re_le_norm u
      · exact Complex.abs_im_le_norm u
    have hun : ‖u‖ = r / L := by
      rw [hu, norm_smul, direction_norm, mul_one, Real.norm_of_nonneg (by positivity)]
    have hxv : x.ofLp i = L * rep (θ i) := rfl
    have hyv : y.ofLp i = L * rep ((θ + tp u) i) := rfl
    have hLm : (m : ℝ) * L = y.ofLp i - x.ofLp i - L * ![u.re, u.im] i := by
      rw [hxv, hyv, ← hm]; ring
    have hbound : |(m : ℝ) * L| < L := by
      rw [hLm]
      have h1 : |L * ![u.re, u.im] i| ≤ r := by
        rw [abs_mul, abs_of_pos hL]
        calc L * |![u.re, u.im] i| ≤ L * (r / L) := by
              exact mul_le_mul_of_nonneg_left (hun ▸ hui) hL.le
          _ = r := by field_simp
      have h2 := abs_sub (y.ofLp i - x.ofLp i) (L * ![u.re, u.im] i)
      have h3 := abs_sub (y.ofLp i) (x.ofLp i)
      linarith
    have := int_eq_zero_of_abs_lt hL hbound
    rw [this, Int.cast_zero, zero_mul] at hLm
    linarith
  apply hAr x hx y hy
  have hsq : dist x y ^ 2 = r ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, hcomp 0, hcomp 1]
    simp only [Real.dist_eq, sq_abs, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hn : u.re ^ 2 + u.im ^ 2 = (r / L) ^ 2 := by
      have := Complex.sq_norm u
      rw [Complex.normSq_apply] at this
      rw [hu, norm_smul, direction_norm, mul_one, Real.norm_of_nonneg (by positivity)] at this
      nlinarith
    have : (x.ofLp 0 - (x.ofLp 0 + L * u.re)) ^ 2 + (x.ofLp 1 - (x.ofLp 1 + L * u.im)) ^ 2 =
        L ^ 2 * (u.re ^ 2 + u.im ^ 2) := by ring
    rw [this, hn]
    field_simp
  nlinarith [dist_nonneg (x := x) (y := y), sq_nonneg (dist x y - r), sq_nonneg (dist x y + r)]

/-- The torus set has measure `|A|/L²`. -/
lemma volume_torusSet {L T : ℝ} (hL : 0 < L) (hTL : 2 * T < L)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : MeasurableSet A) (hAT : A ⊆ cube 2 T) :
    volume (torusSet L A) = ENNReal.ofReal (L ^ 2)⁻¹ * volume A := by
  set box : Set (Fin 2 → ℝ) := {x | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
    ((fun _ => (-1 / 2 : ℝ)) i + 1)} with hbox
  have hboxm : MeasurableSet box := by
    rw [hbox, ofPred_forall]
    exact MeasurableSet.iInter fun i => measurable_pi_apply i measurableSet_Ioc
  set P : Set (Fin 2 → ℝ) := (fun x => L • x) ⁻¹' (WithLp.toLp 2 ⁻¹' A) with hP
  have hPm : MeasurableSet P :=
    (measurable_const_smul L) ((WithLp.measurable_toLp 2 _) hA)
  have hPbox : P ⊆ box := by
    intro x hx i
    have h := hAT hx i
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hL] at h
    have : |x i| < 1 / 2 := by
      by_contra hc
      push Not at hc
      nlinarith
    constructor <;> linarith [abs_lt.mp this]
  have h1 := UnitAddTorus.lintegral_preimage ((torusSet L A).indicator 1) (fun _ => -1 / 2)
  rw [lintegral_indicator_one (torusSet_measurable L hA)] at h1
  rw [h1]
  have h2 : ∫⁻ x in box, (torusSet L A).indicator 1 (fun i => ((x i : ℝ) : UnitAddCircle)) =
      ∫⁻ x in box, P.indicator 1 x := by
    apply setLIntegral_congr_fun hboxm
    intro x hx
    beta_reduce
    have hl : lift L (fun i => ((x i : ℝ) : UnitAddCircle)) = WithLp.toLp 2 (L • x) := by
      simp only [lift]
      congr 1
      funext i
      rw [rep_of_mem (hx i), Pi.smul_apply, smul_eq_mul]
    by_cases hm : WithLp.toLp 2 (L • x) ∈ A
    · have h3 : (fun i => ((x i : ℝ) : UnitAddCircle)) ∈ torusSet L A := by
        show lift L _ ∈ A
        rw [hl]; exact hm
      rw [Set.indicator_of_mem h3, Set.indicator_of_mem (show x ∈ P from hm)]
      rfl
    · have h3 : (fun i => ((x i : ℝ) : UnitAddCircle)) ∉ torusSet L A := by
        show lift L _ ∉ A
        rw [hl]; exact hm
      rw [Set.indicator_of_notMem h3, Set.indicator_of_notMem (show x ∉ P from hm)]
  rw [h2, lintegral_indicator_one hPm, Measure.restrict_apply hPm, inter_eq_left.mpr hPbox, hP,
    Measure.addHaar_preimage_smul volume hL.ne', Module.finrank_fin_fun,
    (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage hA.nullMeasurableSet]
  congr 2
  rw [abs_of_pos (by positivity)]

/-- Volume of the square `[-T,T]²`. -/
lemma volume_cube2 {T : ℝ} (hT : 0 ≤ T) :
    volume (cube 2 T) = ENNReal.ofReal ((2 * T) ^ 2) := by
  have hc : cube 2 T = WithLp.ofLp ⁻¹' Icc (fun _ : Fin 2 => -T) (fun _ => T) := by
    ext x
    simp only [cube, Set.mem_ofPred_eq, mem_preimage, Set.mem_Icc, Pi.le_def, abs_le]
    constructor
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    · intro h i; exact ⟨h.1 i, h.2 i⟩
  rw [hc, (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage measurableSet_Icc.nullMeasurableSet,
    Real.volume_Icc_pi, Fin.prod_univ_two, ← ENNReal.ofReal_mul (by linarith)]
  congr 1
  ring

end
end OAI.Soifer
