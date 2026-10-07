import OAI.HN3.Line

/-!
# The line average: zero correlation of the fully continuous projection

For each algebraic direction `u ∈ K`, the invariant-mean average of
`t ↦ T(0,t) (φ t • T(√(1-t²)u, 0) w)` is both continuous for vertical translations and
orthogonal to all such vectors, hence zero. Pairing it with `c • w` shows that
`t ↦ ⟪pv, Ext3 pv (√(1-t²)u, t)⟫` integrates to zero against every test function on `(-1,1)`.
That function therefore vanishes, and by density so does the correlation at every real unit vector.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HN3
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable (k : ℕ) (ω : Space k)

/-- The real inner product on `L²` is the real part of the complex one. -/
lemma rinner (x y : Hilbert k ω) : inner ℝ x y = RCLike.re ⟪x, y⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) x y)]
  congr 1

/-- The real-linear isometry underlying a unitary. -/
def realIso (Y : unitary (Hilbert k ω →L[ℂ] Hilbert k ω)) : Hilbert k ω ≃ₗᵢ[ℝ] Hilbert k ω :=
  { (Unitary.linearIsometryEquiv Y).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (Unitary.linearIsometryEquiv Y).norm_map }

def Sline (t : AF) : Hilbert k ω ≃ₗᵢ[ℝ] Hilbert k ω := realIso k ω (translation k ω (0, t))

lemma Sline_apply (t : AF) (v : Hilbert k ω) : Sline k ω t v = T k ω (0, t) v := rfl

lemma Sline_add (s t : AF) (v : Hilbert k ω) : Sline k ω s (Sline k ω t v) = Sline k ω (s + t) v := by
  simp only [Sline_apply]
  rw [← T_add, Prod.mk_add_mk, add_zero]

lemma ext_norm {v : Hilbert k ω} (hv : v ∈ space (A := E) (planeRep k ω)) (x : ℂ) :
    ‖orbitExtension (planeRep k ω) v x‖ = ‖v‖ := by
  refine dense_E.denseRange_val.induction_on x
    (isClosed_eq (continuous_norm.comp (orbitExtension_continuous _ hv)) continuous_const) ?_
  intro a
  change ‖orbitExtension (planeRep k ω) v (a : ℂ)‖ = ‖v‖
  rw [orbitExtension_eq _ hv]
  exact norm_op (A := E) _ _ _

/-- Direction curve through the unit sphere. -/
def dcurve (u : K) (t : ℝ) : ℂ := ((rho t : ℝ) : ℂ) * ((u : Circle) : ℂ)

lemma dcurve_continuous (u : K) : Continuous (dcurve u) := by
  unfold dcurve
  exact (Complex.continuous_ofReal.comp rho_continuous).mul continuous_const

lemma dcurve_alg (u : K) (t : AF) : dcurve u t = ((eu u t : E) : ℂ) := rfl

section Window
variable (i : Fin k) (u : K) (φ : ℝ → ℝ)

def win (t : ℝ) : Hilbert k ω := φ t • orbitExtension (planeRep k ω) (wv k ω i) (dcurve u t)

variable {φ} (hφc : Continuous φ) (hφ1 : ∀ t, 1 ≤ |t| → φ t = 0) {B : ℝ} (hφb : ∀ t, |φ t| ≤ B)

include hφ1 in
lemma win_support : ∀ t : ℝ, ((1 : ℕ) : ℝ) < |t| → win k ω i u φ t = 0 := by
  intro t ht
  simp only [Nat.cast_one] at ht
  simp [win, hφ1 t ht.le]

include hφb in
lemma win_bound : ∀ t, ‖win k ω i u φ t‖ ≤ B * ‖wv k ω i‖ := by
  intro t
  rw [win, norm_smul, Real.norm_eq_abs, ext_norm k ω (wv_plane k ω i)]
  exact mul_le_mul_of_nonneg_right (hφb t) (norm_nonneg _)

include hφc in
lemma win_continuous : Continuous (win k ω i u φ) :=
  hφc.smul ((orbitExtension_continuous _ (wv_plane k ω i)).comp (dcurve_continuous u))

include hφc hφ1 in
lemma win_uc : UniformContinuous (win k ω i u φ) := by
  apply HasCompactSupport.uniformContinuous_of_continuous _ (win_continuous k ω i u hφc)
  refine HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1)) (fun t ht => ?_)
  have : 1 < |t| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h
  exact win_support k ω i u hφ1 t (by simpa using this)

/-- The smoothed vector along the direction `u`. -/
def Vvec : Hilbert k ω :=
  HN3.vsmoothed (Sline k ω) (win k ω i u φ) (win_support k ω i u hφ1) (win_bound k ω i u hφb)

lemma win_alg (t : AF) : win k ω i u φ t = φ t • T k ω (eu u t, 0) (wv k ω i) := by
  rw [win, dcurve_alg, orbitExtension_eq _ (wv_plane k ω i)]
  rfl

lemma Sline_win (t : AF) : Sline k ω t (win k ω i u φ t) = φ t • T k ω (xu u t) (wv k ω i) := by
  rw [win_alg, Sline_apply, ContinuousLinearMap.map_smul_of_tower, ← T_add]
  congr 2
  ext <;> simp [xu]

include hφc hφ1 in
lemma Vvec_mem : Vvec k ω i u hφ1 hφb ∈ space (A := AF) (lineRep k ω) := by
  change Tendsto (fun a : AF => op (lineRep k ω) a (Vvec k ω i u hφ1 hφb)) (𝓝 0)
    (𝓝 (Vvec k ω i u hφ1 hφb))
  exact HN3.vsmoothed_tendsto (Sline k ω) (Sline_add k ω) _ (win_uc k ω i u hφc hφ1)
    (win_support k ω i u hφ1) (win_bound k ω i u hφb)

lemma line_orth_T (x : V) {v : Hilbert k ω} (hv : v ∈ (space (A := AF) (lineRep k ω))ᗮ) :
    T k ω x v ∈ (space (A := AF) (lineRep k ω))ᗮ :=
  comm_mem_orthogonal (lineRep k ω) (translation k ω x) (fun a w => line_comm k ω x a w) hv

lemma integralReal_zero_fun (h : PlaneFiveColor.InvariantMean.AF → ℝ) {N : ℕ} {C : ℝ}
    (hs : ∀ t : PlaneFiveColor.InvariantMean.AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ C) (h0 : ∀ t, h t = 0) :
    PlaneFiveColor.InvariantMean.integralReal h hs hb = 0 := by
  have hs0 : ∀ t : ℝ, ((0 : ℕ) : ℝ) < |t| → (0 : C(ℝ, ℝ)) t = 0 := fun _ _ => rfl
  have hb0 : ∀ t : ℝ, ‖(0 : C(ℝ, ℝ)) t‖ ≤ 0 := fun _ => by simp
  rw [PlaneFiveColor.InvariantMean.integralReal_congr h (fun t => (0 : C(ℝ, ℝ)) t) hs hb
    (fun t ht => hs0 t ht) (fun t => hb0 t) (fun t => by simp [h0 t]),
    PlaneFiveColor.InvariantMean.integralReal_ordinary]
  simp

include hφ1 in
lemma pair_support (y : Hilbert k ω) : ∀ t : PlaneFiveColor.InvariantMean.AF,
    ((1 : ℕ) : ℝ) < |(t : ℝ)| → inner ℝ y (Sline k ω t (win k ω i u φ t)) = 0 := by
  intro t ht
  rw [win_support k ω i u hφ1 t ht, map_zero, inner_zero_right]

include hφb in
lemma pair_bound (y : Hilbert k ω) : ∀ t : PlaneFiveColor.InvariantMean.AF,
    ‖inner ℝ y (Sline k ω t (win k ω i u φ t))‖ ≤ ‖y‖ * (B * ‖wv k ω i‖) := by
  intro t
  refine (norm_inner_le_norm (𝕜 := ℝ) _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (win_bound k ω i u hφb t) (norm_nonneg _)

lemma Vvec_pair (y : Hilbert k ω) :
    inner ℝ (Vvec k ω i u hφ1 hφb) y = PlaneFiveColor.InvariantMean.integralReal
      (fun t => inner ℝ y (Sline k ω t (win k ω i u φ t)))
      (pair_support k ω i u hφ1 y) (pair_bound k ω i u hφb y) := by
  unfold Vvec HN3.vsmoothed
  exact PlaneFiveColor.InvariantMean.weakIntegral_pair (fun t => Sline k ω t (win k ω i u φ t)) y
    (HN3.vwindow_support (Sline k ω) _ (win_support k ω i u hφ1))
    (HN3.vwindow_bound (Sline k ω) _ (win_bound k ω i u hφb))
    (pair_support k ω i u hφ1 y) (pair_bound k ω i u hφb y)

lemma Vvec_orth : Vvec k ω i u hφ1 hφb ∈ (space (A := AF) (lineRep k ω))ᗮ := by
  have key : ∀ y ∈ space (A := AF) (lineRep k ω), inner ℝ (Vvec k ω i u hφ1 hφb) y = 0 := by
    intro y hy
    rw [Vvec_pair]
    apply integralReal_zero_fun
    intro t
    rw [Sline_win, rinner k ω]
    have hm : φ t • T k ω (xu u t) (wv k ω i) ∈ (space (A := AF) (lineRep k ω))ᗮ :=
      Submodule.smul_of_tower_mem _ _ (line_orth_T k ω _ (wv_orth k ω i))
    rw [(Submodule.mem_orthogonal _ _).mp hm y hy]
    simp
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h1 : RCLike.re ⟪y, Vvec k ω i u hφ1 hφb⟫_ℂ = 0 := by
    rw [← rinner k ω, real_inner_comm]; exact key y hy
  have h2 : RCLike.re ⟪Complex.I • y, Vvec k ω i u hφ1 hφb⟫_ℂ = 0 := by
    rw [← rinner k ω, real_inner_comm]
    exact key (Complex.I • y) (Submodule.smul_mem _ _ hy)
  rw [inner_smul_left, Complex.conj_I] at h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

include hφc in
lemma Vvec_zero : Vvec k ω i u hφ1 hφb = 0 := by
  have h := (Submodule.mem_orthogonal' _ _).mp (Vvec_orth k ω i u hφ1 hφb) _
    (Vvec_mem k ω i u hφc hφ1 hφb)
  exact inner_self_eq_zero.mp h

end Window

/-- The correlation function of `pv` along the direction curve. -/
def bfun (i : Fin k) (u : K) (t : ℝ) : ℂ :=
  ⟪pv k ω i, Ext3 k ω (pv k ω i) (dcurve u t, t)⟫_ℂ

lemma bfun_continuous (i : Fin k) (u : K) : Continuous (bfun k ω i u) :=
  continuous_const.inner ((Ext3_continuous k ω (pv_plane k ω i) (pv_line k ω i)).comp
    ((dcurve_continuous u).prodMk continuous_id))

lemma bfun_alg (i : Fin k) (u : K) (t : AF) :
    bfun k ω i u t = ⟪pv k ω i, T k ω (xu u t) (pv k ω i)⟫_ℂ := by
  rw [bfun, dcurve_alg, ← Ext3_eq k ω (pv_plane k ω i) (pv_line k ω i)]
  rfl

theorem line_test (i : Fin k) (u : K) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ1 : ∀ t, 1 ≤ |t| → φ t = 0) {B : ℝ} (hφb : ∀ t, |φ t| ≤ B) (c : ℂ) :
    ∫ t, φ t * RCLike.re (conj c * bfun k ω i u t) = 0 := by
  have h0 : inner ℝ (Vvec k ω i u hφ1 hφb) (c • wv k ω i) = 0 := by
    rw [Vvec_zero k ω i u hφc hφ1 hφb, inner_zero_left]
  rw [Vvec_pair] at h0
  let G : C(ℝ, ℝ) := ⟨fun t => -(φ t * RCLike.re (conj c * bfun k ω i u t)), by
    have := bfun_continuous k ω i u
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
      inner ℝ (c • wv k ω i) (Sline k ω t (win k ω i u φ t)) = G t := by
    intro t
    rw [Sline_win, real_inner_smul_right, rinner k ω, inner_smul_left]
    change φ t * RCLike.re (conj c * ⟪wv k ω i, T k ω (xu u t) (wv k ω i)⟫_ℂ) =
      -(φ (t : ℝ) * RCLike.re (conj c * bfun k ω i u t))
    by_cases ht : |(t : ℝ)| < 1
    · rw [bfun_alg, corr_split k ω i (xu u t) (sq_xu u t ht.le) (xu_ne u t ht)]
      simp only [mul_neg, map_neg, neg_neg]
    · rw [hφ1 t (not_lt.mp ht)]
      simp
  rw [PlaneFiveColor.InvariantMean.integralReal_congr _ (fun t => G t) _ _
    (fun t ht => Gs t ht) (fun t => hM t) hpt,
    PlaneFiveColor.InvariantMean.integralReal_ordinary] at h0
  have : ∫ t, -(φ t * RCLike.re (conj c * bfun k ω i u t)) = 0 := h0
  rw [integral_neg] at this
  exact neg_eq_zero.mp this

/-- A continuous function on an open set that is almost everywhere zero there is zero there. -/
lemma cont_zero_of_ae {f : ℝ → ℝ} (hf : Continuous f) {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ U → f t = 0) : ∀ t ∈ U, f t = 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨t0, ht0, hne⟩ := hc
  have hW : IsOpen (U ∩ {t | f t ≠ 0}) := hU.inter (isOpen_ne_fun hf continuous_const)
  have hpos := hW.measure_pos (volume : Measure ℝ) ⟨t0, ht0, hne⟩
  have hzero : (volume : Measure ℝ) (U ∩ {t | f t ≠ 0}) = 0 := by
    rw [ae_iff] at h
    refine measure_mono_null (fun t ht => ?_) h
    simp only [Set.mem_setOf_eq, not_imp]
    exact ⟨ht.1, ht.2⟩
  exact hpos.ne' hzero

theorem bfun_zero (i : Fin k) (u : K) (t : ℝ) (ht : |t| < 1) : bfun k ω i u t = 0 := by
  have hU : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have key : ∀ c : ℂ, RCLike.re (conj c * bfun k ω i u t) = 0 := by
    intro c
    let f : ℝ → ℝ := fun s => RCLike.re (conj c * bfun k ω i u s)
    have hf : Continuous f := by
      have := bfun_continuous k ω i u
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
          line_test k ω i u hg.continuous hg1 (B := M) (fun s => by simpa using hM s) c)
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
theorem pv_unit_correlation (i : Fin k) (y : ℂ × ℝ) (hy : ‖y.1‖ ^ 2 + y.2 ^ 2 = 1) :
    ⟪pv k ω i, Ext3 k ω (pv k ω i) y⟫_ℂ = 0 := by
  have hcont := Ext3_continuous k ω (pv_plane k ω i) (pv_line k ω i)
  -- along the curve, for every circle direction and every `|t| ≤ 1`
  have hcirc : ∀ t : ℝ, |t| < 1 → ∀ z : Circle,
      ⟪pv k ω i, Ext3 k ω (pv k ω i) (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0 := by
    intro t ht z
    apply circle_closed_induction (p := fun z : ℂ =>
      ⟪pv k ω i, Ext3 k ω (pv k ω i) (((rho t : ℝ) : ℂ) * z, t)⟫_ℂ = 0)
    · exact isClosed_eq (continuous_const.inner (hcont.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const))) continuous_const
    · intro b
      exact bfun_zero k ω i b t ht
  have hIcc : ∀ z : Circle, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      ⟪pv k ω i, Ext3 k ω (pv k ω i) (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0 := by
    intro z
    have hcl : IsClosed {t : ℝ | ⟪pv k ω i, Ext3 k ω (pv k ω i)
        (((rho t : ℝ) : ℂ) * (z : ℂ), t)⟫_ℂ = 0} :=
      isClosed_eq (continuous_const.inner (hcont.comp
        (((Complex.continuous_ofReal.comp rho_continuous).mul continuous_const).prodMk
          continuous_id))) continuous_const
    have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ {t : ℝ | ⟪pv k ω i, Ext3 k ω (pv k ω i)
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

end HN3
end
end OAI
