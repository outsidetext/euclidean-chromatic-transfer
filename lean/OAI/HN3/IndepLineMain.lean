import OAI.HN3.IndepRigidity
import OAI.HN3.LineMain

/-!
# The line average for the independent-set model

Copy of the model-specific part of `HN3.LineMain` for the single indicator on
`(ISpace, measure L)`: the fully continuous projection `pv L` has zero correlation at every
real unit vector of `ℂ × ℝ`.
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

/-- The real inner product on `L²` is the real part of the complex one. -/
lemma rinner (x y : Hilbert L) : inner ℝ x y = RCLike.re ⟪x, y⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) x y)]
  congr 1

/-- The real-linear isometry underlying a unitary. -/
def realIso (Y : unitary (Hilbert L →L[ℂ] Hilbert L)) : Hilbert L ≃ₗᵢ[ℝ] Hilbert L :=
  { (Unitary.linearIsometryEquiv Y).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (Unitary.linearIsometryEquiv Y).norm_map }

def Sline (t : AF) : Hilbert L ≃ₗᵢ[ℝ] Hilbert L := realIso L (translation L (0, t))

lemma Sline_apply (t : AF) (v : Hilbert L) : Sline L t v = T L (0, t) v := rfl

lemma Sline_add (s t : AF) (v : Hilbert L) : Sline L s (Sline L t v) = Sline L (s + t) v := by
  simp only [Sline_apply]
  rw [← T_add, Prod.mk_add_mk, add_zero]

lemma ext_norm {v : Hilbert L} (hv : v ∈ space (A := E) (planeRep L)) (x : ℂ) :
    ‖orbitExtension (planeRep L) v x‖ = ‖v‖ := by
  refine dense_E.denseRange_val.induction_on x
    (isClosed_eq (continuous_norm.comp (orbitExtension_continuous _ hv)) continuous_const) ?_
  intro a
  change ‖orbitExtension (planeRep L) v (a : ℂ)‖ = ‖v‖
  rw [orbitExtension_eq _ hv]
  exact norm_op (A := E) _ _ _

section Window
variable (u : K) (φ : ℝ → ℝ)

def win (t : ℝ) : Hilbert L := φ t • orbitExtension (planeRep L) (wv L) (dcurve u t)

variable {φ} (hφc : Continuous φ) (hφ1 : ∀ t, 1 ≤ |t| → φ t = 0) {B : ℝ} (hφb : ∀ t, |φ t| ≤ B)

include hφ1 in
lemma win_support : ∀ t : ℝ, ((1 : ℕ) : ℝ) < |t| → win L u φ t = 0 := by
  intro t ht
  simp only [Nat.cast_one] at ht
  simp [win, hφ1 t ht.le]

include hφb in
lemma win_bound : ∀ t, ‖win L u φ t‖ ≤ B * ‖wv L‖ := by
  intro t
  rw [win, norm_smul, Real.norm_eq_abs, ext_norm L (wv_plane L)]
  exact mul_le_mul_of_nonneg_right (hφb t) (norm_nonneg _)

include hφc in
lemma win_continuous : Continuous (win L u φ) :=
  hφc.smul ((orbitExtension_continuous _ (wv_plane L)).comp (dcurve_continuous u))

include hφc hφ1 in
lemma win_uc : UniformContinuous (win L u φ) := by
  apply HasCompactSupport.uniformContinuous_of_continuous _ (win_continuous L u hφc)
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) (fun t ht => ?_)
  have : 1 < |t| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  exact win_support L u hφ1 t (by simpa using this)

/-- The smoothed vector along the direction `u`. -/
def Vvec : Hilbert L :=
  HN3.vsmoothed (Sline L) (win L u φ) (win_support L u hφ1) (win_bound L u hφb)

lemma win_alg (t : AF) : win L u φ t = φ t • T L (eu u t, 0) (wv L) := by
  rw [win, dcurve_alg, orbitExtension_eq _ (wv_plane L)]
  rfl

lemma Sline_win (t : AF) : Sline L t (win L u φ t) = φ t • T L (xu u t) (wv L) := by
  rw [win_alg, Sline_apply, ContinuousLinearMap.map_smul_of_tower, ← T_add]
  congr 2
  ext <;> simp [xu]

include hφc hφ1 in
lemma Vvec_mem : Vvec L u hφ1 hφb ∈ space (A := AF) (lineRep L) := by
  change Tendsto (fun a : AF => op (lineRep L) a (Vvec L u hφ1 hφb)) (𝓝 0)
    (𝓝 (Vvec L u hφ1 hφb))
  exact HN3.vsmoothed_tendsto (Sline L) (Sline_add L) _ (win_uc L u hφc hφ1)
    (win_support L u hφ1) (win_bound L u hφb)

lemma line_orth_T (x : V) {v : Hilbert L} (hv : v ∈ (space (A := AF) (lineRep L))ᗮ) :
    T L x v ∈ (space (A := AF) (lineRep L))ᗮ :=
  comm_mem_orthogonal (lineRep L) (translation L x) (fun a w => line_comm L x a w) hv

include hφ1 in
lemma pair_support (y : Hilbert L) : ∀ t : PlaneFiveColor.InvariantMean.AF,
    ((1 : ℕ) : ℝ) < |(t : ℝ)| → inner ℝ y (Sline L t (win L u φ t)) = 0 := by
  intro t ht
  rw [win_support L u hφ1 t ht, map_zero, inner_zero_right]

include hφb in
lemma pair_bound (y : Hilbert L) : ∀ t : PlaneFiveColor.InvariantMean.AF,
    ‖inner ℝ y (Sline L t (win L u φ t))‖ ≤ ‖y‖ * (B * ‖wv L‖) := by
  intro t
  refine (norm_inner_le_norm (𝕜 := ℝ) _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (win_bound L u hφb t) (norm_nonneg _)

lemma Vvec_pair (y : Hilbert L) :
    inner ℝ (Vvec L u hφ1 hφb) y = PlaneFiveColor.InvariantMean.integralReal
      (fun t => inner ℝ y (Sline L t (win L u φ t)))
      (pair_support L u hφ1 y) (pair_bound L u hφb y) := by
  unfold Vvec HN3.vsmoothed
  exact PlaneFiveColor.InvariantMean.weakIntegral_pair (fun t => Sline L t (win L u φ t)) y
    (HN3.vwindow_support (Sline L) _ (win_support L u hφ1))
    (HN3.vwindow_bound (Sline L) _ (win_bound L u hφb))
    (pair_support L u hφ1 y) (pair_bound L u hφb y)

lemma Vvec_orth : Vvec L u hφ1 hφb ∈ (space (A := AF) (lineRep L))ᗮ := by
  have key : ∀ y ∈ space (A := AF) (lineRep L), inner ℝ (Vvec L u hφ1 hφb) y = 0 := by
    intro y hy
    rw [Vvec_pair]
    apply integralReal_zero_fun
    intro t
    rw [Sline_win, rinner L]
    have hm : φ t • T L (xu u t) (wv L) ∈ (space (A := AF) (lineRep L))ᗮ :=
      Submodule.smul_of_tower_mem _ _ (line_orth_T L _ (wv_orth L))
    rw [(Submodule.mem_orthogonal _ _).mp hm y hy]
    simp
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h1 : RCLike.re ⟪y, Vvec L u hφ1 hφb⟫_ℂ = 0 := by
    rw [← rinner L, real_inner_comm]; exact key y hy
  have h2 : RCLike.re ⟪Complex.I • y, Vvec L u hφ1 hφb⟫_ℂ = 0 := by
    rw [← rinner L, real_inner_comm]
    exact key (Complex.I • y) (Submodule.smul_mem _ _ hy)
  rw [inner_smul_left, Complex.conj_I] at h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

include hφc in
lemma Vvec_zero : Vvec L u hφ1 hφb = 0 := by
  have h := (Submodule.mem_orthogonal' _ _).mp (Vvec_orth L u hφ1 hφb) _
    (Vvec_mem L u hφc hφ1 hφb)
  exact inner_self_eq_zero.mp h

end Window

/-- The correlation function of `pv` along the direction curve. -/
def bfun (u : K) (t : ℝ) : ℂ :=
  ⟪pv L, Ext3 L (pv L) (dcurve u t, t)⟫_ℂ

lemma bfun_continuous (u : K) : Continuous (bfun L u) :=
  continuous_const.inner ((Ext3_continuous L (pv_plane L) (pv_line L)).comp
    ((dcurve_continuous u).prodMk continuous_id))

lemma bfun_alg (u : K) (t : AF) :
    bfun L u t = ⟪pv L, T L (xu u t) (pv L)⟫_ℂ := by
  rw [bfun, dcurve_alg, ← Ext3_eq L (pv_plane L) (pv_line L)]
  rfl

theorem line_test (u : K) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ1 : ∀ t, 1 ≤ |t| → φ t = 0) {B : ℝ} (hφb : ∀ t, |φ t| ≤ B) (c : ℂ) :
    ∫ t, φ t * RCLike.re (conj c * bfun L u t) = 0 := by
  have h0 : inner ℝ (Vvec L u hφ1 hφb) (c • wv L) = 0 := by
    rw [Vvec_zero L u hφc hφ1 hφb, inner_zero_left]
  rw [Vvec_pair] at h0
  let G : C(ℝ, ℝ) := ⟨fun t => -(φ t * RCLike.re (conj c * bfun L u t)), by
    have := bfun_continuous L u
    fun_prop⟩
  have Gs : ∀ t : ℝ, ((1 : ℕ) : ℝ) < |t| → G t = 0 := by
    intro t ht
    simp only [Nat.cast_one] at ht
    simp [G, hφ1 t ht.le]
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, ‖G t‖ ≤ M := by
    obtain ⟨M, hM⟩ := (map_continuous G).bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) (fun t ht => by
        apply Gs
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
        simp only [Nat.cast_one]
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h))
    exact ⟨M, hM⟩
  have hpt : ∀ t : PlaneFiveColor.InvariantMean.AF,
      inner ℝ (c • wv L) (Sline L t (win L u φ t)) = G t := by
    intro t
    rw [Sline_win, real_inner_smul_right, rinner L, inner_smul_left]
    change φ t * RCLike.re (conj c * ⟪wv L, T L (xu u t) (wv L)⟫_ℂ) =
      -(φ (t : ℝ) * RCLike.re (conj c * bfun L u t))
    by_cases ht : |(t : ℝ)| < 1
    · rw [bfun_alg, corr_split L (xu u t) (sq_xu u t ht.le) (xu_ne u t ht)]
      simp only [mul_neg, map_neg, neg_neg]
    · rw [hφ1 t (not_lt.mp ht)]
      simp
  rw [PlaneFiveColor.InvariantMean.integralReal_congr _ (fun t => G t) _ _
    (fun t ht => Gs t ht) (fun t => hM t) hpt,
    PlaneFiveColor.InvariantMean.integralReal_ordinary] at h0
  have : ∫ t, -(φ t * RCLike.re (conj c * bfun L u t)) = 0 := h0
  rw [integral_neg] at this
  exact neg_eq_zero.mp this

theorem bfun_zero (u : K) (t : ℝ) (ht : |t| < 1) : bfun L u t = 0 := by
  have hU : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have key : ∀ c : ℂ, RCLike.re (conj c * bfun L u t) = 0 := by
    intro c
    let f : ℝ → ℝ := fun s => RCLike.re (conj c * bfun L u s)
    have hf : Continuous f := by
      have := bfun_continuous L u
      fun_prop
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (hf.locallyIntegrable.locallyIntegrableOn _) (fun g hg hgs hgU => by
        obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgs
        have hg1 : ∀ s, 1 ≤ |s| → g s = 0 := by
          intro s hs
          apply image_eq_zero_of_notMem_tsupport
          intro hst
          have := hgU hst
          rw [Set.mem_Ioo] at this
          rcases le_abs'.mp hs with h | h <;> linarith [this.1, this.2]
        simpa [smul_eq_mul, f] using
          line_test L u hg.continuous hg1 (B := M) (fun s => by simpa using hM s) c)
    exact cont_zero_of_ae hf hU hae t hmem
  have h1 := key 1
  have h2 := key Complex.I
  simp only [map_one, one_mul, RCLike.re_to_complex] at h1
  simp only [Complex.conj_I, RCLike.re_to_complex, neg_mul, Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg] at h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

/-- Zero correlation of the fully continuous projection at every real unit vector of `ℂ × ℝ`. -/
theorem pv_unit_correlation (y : ℂ × ℝ) (hy : ‖y.1‖ ^ 2 + y.2 ^ 2 = 1) :
    ⟪pv L, Ext3 L (pv L) y⟫_ℂ = 0 := by
  have hcont := Ext3_continuous L (pv_plane L) (pv_line L)
  -- along the curve, for every circle direction and every `|t| ≤ 1`
  have hcirc : ∀ t : ℝ, |t| < 1 → ∀ z : Circle,
      ⟪pv L, Ext3 L (pv L) (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0 := by
    intro t ht z
    apply circle_closed_induction (p := fun z : ℂ =>
      ⟪pv L, Ext3 L (pv L) (((rho t : ℝ) : ℂ) * z, t)⟫_ℂ = 0)
    · exact isClosed_eq (continuous_const.inner (hcont.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const))) continuous_const
    · intro b
      exact bfun_zero L b t ht
  have hIcc : ∀ z : Circle, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ⟪pv L, Ext3 L (pv L) (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0 := by
    intro z
    have hcl : IsClosed {t : ℝ | ⟪pv L, Ext3 L (pv L)
        (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0} :=
      isClosed_eq (continuous_const.inner (hcont.comp
        (((Complex.continuous_ofReal.comp rho_continuous).mul continuous_const).prodMk
          continuous_id))) continuous_const
    have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {t : ℝ | ⟪pv L, Ext3 L (pv L)
        (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0} := by
      intro t ht
      exact hcirc t (abs_lt.mpr ⟨ht.1, ht.2⟩) z
    have := closure_minimal hsub hcl
    rw [closure_Ioo (by norm_num)] at this
    exact fun t ht => this ht
  have h2 : y.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖y.1‖]
  have ht : y.2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg (y.2 - 1), sq_nonneg (y.2 + 1)]
  have hrho : rho y.2 = ‖y.1‖ := by
    rw [rho, show 1 - y.2 ^ 2 = ‖y.1‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg _)]
  by_cases h0 : y.1 = 0
  · have := hIcc 1 y.2 ht
    rw [hrho, h0, norm_zero] at this
    have hy' : y = (0, y.2) := Prod.ext h0 rfl
    rw [hy']
    simpa using this
  · have hn : ‖y.1‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hb : ‖y.1 / (‖y.1‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]
    let z : Circle := ⟨y.1 / (‖y.1‖ : ℂ), mem_sphere_zero_iff_norm.mpr hb⟩
    have := hIcc z y.2 ht
    have hz : ((rho y.2 : ℝ) : ℂ) * (z : ℂ) = y.1 := by
      rw [hrho]
      change (‖y.1‖ : ℂ) * (y.1 / (‖y.1‖ : ℂ)) = y.1
      field_simp [Complex.ofReal_ne_zero.mpr hn]
    rw [hz] at this
    simpa using this

end Indep
end HN3
end
end OAI
