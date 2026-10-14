import OAI.HNN.Even
import OAI.HN3.LineMain

/-!
# Odd dimension: the axis

For `r = 1`, fix a forbidden algebraic length `d > 0` and a generic algebraic unit vector `u` of
`E^m`. The points `(√(d²-t²)·u, t)`, `t ∈ AF ∩ (-d,d)`, are generic algebraic vectors of length
`d`. An invariant-mean average along the axis of `t ↦ T(0,t) (φ t • T(√(d²-t²)u, 0) w)` is both
continuous along the axis and orthogonal to all such vectors, hence zero. This forces the
correlation of `pv` along the curve to vanish, and density of generic algebraic unit vectors
gives zero correlation at every real vector of length `d`.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HNN
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable {m : ℕ} {D : Set ℝ} {k : ℕ} (ω : Space m 1 D k)

/-- The real inner product on `L²` is the real part of the complex one. -/
lemma rinner (x y : Hilbert ω) : inner ℝ x y = RCLike.re ⟪x, y⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) x y)]
  congr 1

/-- The real-linear isometry underlying a unitary. -/
def realIso (Y : unitary (Hilbert ω →L[ℂ] Hilbert ω)) : Hilbert ω ≃ₗᵢ[ℝ] Hilbert ω :=
  { (Unitary.linearIsometryEquiv Y).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (Unitary.linearIsometryEquiv Y).norm_map }

def Sline (t : AF) : Hilbert ω ≃ₗᵢ[ℝ] Hilbert ω := realIso ω (translation ω (0, fun _ => t))

lemma Sline_apply (t : AF) (v : Hilbert ω) : Sline ω t v = T ω (0, fun _ => t) v := rfl

lemma Sline_add (s t : AF) (v : Hilbert ω) : Sline ω s (Sline ω t v) = Sline ω (s + t) v := by
  simp only [Sline_apply]
  rw [← T_add]
  congr 2
  exact Prod.ext (by simp) (by funext i; simp)

/-! ### Algebraic points along a direction -/

def rho (d t : ℝ) : ℝ := Real.sqrt (d ^ 2 - t ^ 2)

lemma rho_continuous (d : ℝ) : Continuous (rho d) := by
  unfold rho; fun_prop

lemma rho_alg {d : ℝ} (hdA : IsAlgebraic ℚ d) (t : AF) : IsAlgebraic ℚ (rho d t) := by
  have ht : IsAlgebraic ℚ (t : ℝ) := mem_algebraicClosure_iff.mp t.property
  by_cases h : 0 ≤ d ^ 2 - (t : ℝ) ^ 2
  · apply IsAlgebraic.of_pow (n := 2) (by norm_num)
    rw [rho, Real.sq_sqrt h]
    exact (hdA.pow 2).sub (ht.pow 2)
  · rw [rho, Real.sqrt_eq_zero_of_nonpos (by linarith)]
    exact isAlgebraic_zero

def dcurve (d : ℝ) (u : Fin m → E) (t : ℝ) : Fin m → ℂ :=
  fun j => ((rho d t : ℝ) : ℂ) * (u j : ℂ)

lemma dcurve_continuous (d : ℝ) (u : Fin m → E) : Continuous (dcurve d u) :=
  continuous_pi fun _ => (Complex.continuous_ofReal.comp (rho_continuous d)).mul continuous_const

def eu {d : ℝ} (hdA : IsAlgebraic ℚ d) (u : Fin m → E) (t : AF) : Fin m → E := fun j =>
  ⟨((rho d t : ℝ) : ℂ) * (u j : ℂ),
    mul_mem (mem_algebraicClosure_iff.mpr (alg_complex (rho_alg hdA t))) (u j).property⟩

def xu {d : ℝ} (hdA : IsAlgebraic ℚ d) (u : Fin m → E) (t : AF) : V m 1 := (eu hdA u t, fun _ => t)

lemma emb_xu {d : ℝ} (hdA : IsAlgebraic ℚ d) (u : Fin m → E) (t : AF) :
    emb (xu hdA u t) = (dcurve d u t, fun _ => (t : ℝ)) := rfl

lemma rho_sq {d t : ℝ} (ht : |t| ≤ d) : rho d t ^ 2 = d ^ 2 - t ^ 2 := by
  rw [rho, Real.sq_sqrt]
  nlinarith [abs_nonneg t, sq_abs t]

lemma nsq_dcurve (d : ℝ) (u : Fin m → E) (t : ℝ) :
    nsq (dcurve d u t) = rho d t ^ 2 * nsq (embP u) := by
  simp [nsq, dcurve, embP, mul_pow, Finset.mul_sum, Complex.norm_real, sq_abs]

lemma sq_xu {d : ℝ} (hdA : IsAlgebraic ℚ d) {u : Fin m → E} (hu1 : nsq (embP u) = 1) (t : AF)
    (ht : |(t : ℝ)| ≤ d) : sq (xu hdA u t) = d ^ 2 := by
  rw [← usq_emb, emb_xu, usq]
  simp only [nsq_dcurve, hu1, mul_one, rho_sq ht, Finset.univ_unique, Finset.sum_singleton]
  ring

lemma rho_pos {d t : ℝ} (ht : |t| < d) : 0 < rho d t := by
  apply Real.sqrt_pos.mpr
  nlinarith [abs_nonneg t, sq_abs t]

lemma xu_generic {d : ℝ} (hdA : IsAlgebraic ℚ d) {u : Fin m → E} (hu0 : ∀ j, u j ≠ 0) (t : AF)
    (ht : |(t : ℝ)| < d) : Generic (xu hdA u t) := by
  intro j h
  have hc := congrArg Subtype.val h
  simp only [xu, eu, ZeroMemClass.coe_zero, mul_eq_zero, Complex.ofReal_eq_zero] at hc
  rcases hc with h1 | h1
  · exact (rho_pos ht).ne' h1
  · exact hu0 j (Subtype.ext h1)

/-! ### The window and the smoothed vector -/

section Window
variable (i : Fin k) (d : ℝ) (u : Fin m → E) (φ : ℝ → ℝ)

def win (t : ℝ) : Hilbert ω := φ t • ExtP ω (wv ω i) (dcurve d u t)

variable {d φ} (hφc : Continuous φ) (hφ1 : ∀ t, d ≤ |t| → φ t = 0) {B : ℝ}
  (hφb : ∀ t, |φ t| ≤ B)

include hφ1 in
lemma win_support : ∀ t : ℝ, ((⌈d⌉₊ : ℕ) : ℝ) < |t| → win ω i d u φ t = 0 := by
  intro t ht
  simp [win, hφ1 t ((Nat.le_ceil d).trans ht.le)]

include hφb in
lemma win_bound : ∀ t, ‖win ω i d u φ t‖ ≤ B * ‖wv ω i‖ := by
  intro t
  rw [win, norm_smul, Real.norm_eq_abs, ExtP_norm ω (wv_plane ω i)]
  exact mul_le_mul_of_nonneg_right (hφb t) (norm_nonneg _)

include hφc in
lemma win_continuous : Continuous (win ω i d u φ) :=
  hφc.smul ((ExtP_continuous ω (wv_plane ω i)).comp (dcurve_continuous d u))

lemma outside_Icc {N t : ℝ} (ht : t ∉ Set.Icc (-N) N) : N < |t| := by
  by_contra h
  push Not at h
  exact ht (abs_le.mp h)

include hφc hφ1 in
lemma win_uc : UniformContinuous (win ω i d u φ) := by
  apply HasCompactSupport.uniformContinuous_of_continuous _ (win_continuous ω i u hφc)
  refine HasCompactSupport.intro (isCompact_Icc (a := -((⌈d⌉₊ : ℕ) : ℝ)) (b := ((⌈d⌉₊ : ℕ) : ℝ)))
    (fun t ht => ?_)
  exact win_support ω i u hφ1 t (outside_Icc ht)

/-- The smoothed vector along the direction `u`. -/
def Vvec : Hilbert ω :=
  HN3.vsmoothed (Sline ω) (win ω i d u φ) (win_support ω i u hφ1) (win_bound ω i u hφb)

lemma win_alg (hdA : IsAlgebraic ℚ d) (t : AF) :
    win ω i d u φ t = φ t • T ω (eu hdA u t, 0) (wv ω i) := by
  rw [win, show dcurve d u t = embP (eu hdA u t) from rfl, ExtP_eq ω (wv_plane ω i)]

lemma Sline_win (hdA : IsAlgebraic ℚ d) (t : AF) :
    Sline ω t (win ω i d u φ t) = φ t • T ω (xu hdA u t) (wv ω i) := by
  rw [win_alg ω i u hdA, Sline_apply, ContinuousLinearMap.map_smul_of_tower, ← T_add]
  rw [show ((0 : Fin m → E), (fun _ => t : Fin 1 → AF)) + (eu hdA u t, 0) = xu hdA u t from
    Prod.ext (by simp [xu]) (by funext j; simp [xu])]

include hφc hφ1 in
lemma Vvec_mem : Vvec ω i u hφ1 hφb ∈ space (A := AF) (lineRep ω) := by
  change Tendsto (fun a : AF => op (lineRep ω) a (Vvec ω i u hφ1 hφb)) (𝓝 0)
    (𝓝 (Vvec ω i u hφ1 hφb))
  exact HN3.vsmoothed_tendsto (Sline ω) (Sline_add ω) _ (win_uc ω i u hφc hφ1)
    (win_support ω i u hφ1) (win_bound ω i u hφb)

lemma line_orth_T (x : V m 1) {v : Hilbert ω} (hv : v ∈ (space (A := AF) (lineRep ω))ᗮ) :
    T ω x v ∈ (space (A := AF) (lineRep ω))ᗮ :=
  HN3.comm_mem_orthogonal (lineRep ω) (translation ω x) (fun a w => line_comm ω x a w) hv

include hφ1 in
lemma pair_support (y : Hilbert ω) : ∀ t : PlaneFiveColor.InvariantMean.AF,
    ((⌈d⌉₊ : ℕ) : ℝ) < |(t : ℝ)| → inner ℝ y (Sline ω t (win ω i d u φ t)) = 0 := by
  intro t ht
  rw [win_support ω i u hφ1 t ht, map_zero, inner_zero_right]

include hφb in
lemma pair_bound (y : Hilbert ω) : ∀ t : PlaneFiveColor.InvariantMean.AF,
    ‖inner ℝ y (Sline ω t (win ω i d u φ t))‖ ≤ ‖y‖ * (B * ‖wv ω i‖) := by
  intro t
  refine (norm_inner_le_norm (𝕜 := ℝ) _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_left (win_bound ω i u hφb t) (norm_nonneg _)

lemma Vvec_pair (y : Hilbert ω) :
    inner ℝ (Vvec ω i u hφ1 hφb) y = PlaneFiveColor.InvariantMean.integralReal
      (fun t => inner ℝ y (Sline ω t (win ω i d u φ t)))
      (pair_support ω i u hφ1 y) (pair_bound ω i u hφb y) := by
  unfold Vvec HN3.vsmoothed
  exact PlaneFiveColor.InvariantMean.weakIntegral_pair (fun t => Sline ω t (win ω i d u φ t)) y
    (HN3.vwindow_support (Sline ω) _ (win_support ω i u hφ1))
    (HN3.vwindow_bound (Sline ω) _ (win_bound ω i u hφb))
    (pair_support ω i u hφ1 y) (pair_bound ω i u hφb y)

lemma Vvec_orth (hdA : IsAlgebraic ℚ d) :
    Vvec ω i u hφ1 hφb ∈ (space (A := AF) (lineRep ω))ᗮ := by
  have key : ∀ y ∈ space (A := AF) (lineRep ω), inner ℝ (Vvec ω i u hφ1 hφb) y = 0 := by
    intro y hy
    rw [Vvec_pair]
    apply HN3.integralReal_zero_fun
    intro t
    rw [Sline_win ω i u hdA, rinner ω]
    have hm : φ t • T ω (xu hdA u t) (wv ω i) ∈ (space (A := AF) (lineRep ω))ᗮ :=
      Submodule.smul_of_tower_mem _ _ (line_orth_T ω _ (wv_orth ω i))
    rw [(Submodule.mem_orthogonal _ _).mp hm y hy]
    simp
  rw [Submodule.mem_orthogonal]
  intro y hy
  have h1 : RCLike.re ⟪y, Vvec ω i u hφ1 hφb⟫_ℂ = 0 := by
    rw [← rinner ω, real_inner_comm]; exact key y hy
  have h2 : RCLike.re ⟪Complex.I • y, Vvec ω i u hφ1 hφb⟫_ℂ = 0 := by
    rw [← rinner ω, real_inner_comm]
    exact key (Complex.I • y) (Submodule.smul_mem _ _ hy)
  rw [inner_smul_left, Complex.conj_I] at h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

include hφc in
lemma Vvec_zero (hdA : IsAlgebraic ℚ d) : Vvec ω i u hφ1 hφb = 0 := by
  have h := (Submodule.mem_orthogonal' _ _).mp (Vvec_orth ω i u hφ1 hφb hdA) _
    (Vvec_mem ω i u hφc hφ1 hφb)
  exact inner_self_eq_zero.mp h

end Window

/-! ### The correlation along the curve -/

/-- The correlation function of `pv` along the curve `t ↦ (√(d²-t²)u, t)`. -/
def bfun (i : Fin k) (d : ℝ) (u : Fin m → E) (t : ℝ) : ℂ :=
  ⟪pv ω i, Ext ω (pv ω i) (dcurve d u t, fun _ => t)⟫_ℂ

lemma bfun_continuous (i : Fin k) (d : ℝ) (u : Fin m → E) : Continuous (bfun ω i d u) :=
  continuous_const.inner ((Ext_continuous ω le_rfl (pv_plane ω i) (pv_line ω i)).comp
    ((dcurve_continuous d u).prodMk (continuous_pi fun _ => continuous_id)))

lemma bfun_alg (i : Fin k) {d : ℝ} (hdA : IsAlgebraic ℚ d) (u : Fin m → E) (t : AF) :
    bfun ω i d u t = ⟪pv ω i, T ω (xu hdA u t) (pv ω i)⟫_ℂ := by
  rw [bfun, ← emb_xu hdA, Ext_eq ω le_rfl (pv_plane ω i) (pv_line ω i)]

section Test
variable (i : Fin k) {d : ℝ} (hd : d ∈ D) (hdA : IsAlgebraic ℚ d) {u : Fin m → E}
  (hu0 : ∀ j, u j ≠ 0) (hu1 : nsq (embP u) = 1)
include hd hdA hu0 hu1

theorem line_test {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ1 : ∀ t, d ≤ |t| → φ t = 0) {B : ℝ} (hφb : ∀ t, |φ t| ≤ B) (c : ℂ) :
    ∫ t, φ t * RCLike.re (conj c * bfun ω i d u t) = 0 := by
  have h0 : inner ℝ (Vvec ω i u hφ1 hφb) (c • wv ω i) = 0 := by
    rw [Vvec_zero ω i u hφc hφ1 hφb hdA, inner_zero_left]
  rw [Vvec_pair] at h0
  let G : C(ℝ, ℝ) := ⟨fun t => -(φ t * RCLike.re (conj c * bfun ω i d u t)), by
    have := bfun_continuous ω i d u
    fun_prop⟩
  have Gs : ∀ t : ℝ, ((⌈d⌉₊ : ℕ) : ℝ) < |t| → G t = 0 := by
    intro t ht
    simp [G, hφ1 t ((Nat.le_ceil d).trans ht.le)]
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, ‖G t‖ ≤ M := by
    obtain ⟨M, hM⟩ := (map_continuous G).bounded_above_of_compact_support
      (HasCompactSupport.intro (isCompact_Icc (a := -((⌈d⌉₊ : ℕ) : ℝ)) (b := ((⌈d⌉₊ : ℕ) : ℝ)))
        (fun t ht => Gs t (outside_Icc ht)))
    exact ⟨M, hM⟩
  have hpt : ∀ t : PlaneFiveColor.InvariantMean.AF,
      inner ℝ (c • wv ω i) (Sline ω t (win ω i d u φ t)) = G t := by
    intro t
    rw [Sline_win ω i u hdA, real_inner_smul_right, rinner ω, inner_smul_left]
    change φ t * RCLike.re (conj c * ⟪wv ω i, T ω (xu hdA u t) (wv ω i)⟫_ℂ) =
      -(φ (t : ℝ) * RCLike.re (conj c * bfun ω i d u t))
    by_cases ht : |(t : ℝ)| < d
    · rw [bfun_alg ω i hdA, corr_split ω i (xu hdA u t) (xu_generic hdA hu0 t ht) hd
        (sq_xu hdA hu1 t ht.le)]
      simp only [mul_neg, map_neg, neg_neg]
    · rw [hφ1 t (not_lt.mp ht)]
      simp
  rw [PlaneFiveColor.InvariantMean.integralReal_congr _ (fun t => G t) _ _
    (fun t ht => Gs t ht) (fun t => hM t) hpt,
    PlaneFiveColor.InvariantMean.integralReal_ordinary] at h0
  have : ∫ t, -(φ t * RCLike.re (conj c * bfun ω i d u t)) = 0 := h0
  rw [integral_neg] at this
  exact neg_eq_zero.mp this

theorem bfun_zero (t : ℝ) (ht : |t| < d) : bfun ω i d u t = 0 := by
  have hU : IsOpen (Set.Ioo (-d) d) := isOpen_Ioo
  have hmem : t ∈ Set.Ioo (-d) d := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have key : ∀ c : ℂ, RCLike.re (conj c * bfun ω i d u t) = 0 := by
    intro c
    let f : ℝ → ℝ := fun s => RCLike.re (conj c * bfun ω i d u s)
    have hf : Continuous f := by
      have := bfun_continuous ω i d u
      fun_prop
    have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (hf.locallyIntegrable.locallyIntegrableOn _) (fun g hg hgs hgU => by
        obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgs
        have hg1 : ∀ s, d ≤ |s| → g s = 0 := by
          intro s hs
          apply image_eq_zero_of_notMem_tsupport
          intro hst
          have := hgU hst
          rw [Set.mem_Ioo] at this
          rcases le_abs'.mp hs with h | h <;> linarith [this.1, this.2]
        simpa [smul_eq_mul, f] using
          line_test ω i hd hdA hu0 hu1 hg.continuous hg1 (B := M) (fun s => by simpa using hM s) c)
    exact HN3.cont_zero_of_ae hf hU hae t hmem
  have h1 := key 1
  have h2 := key Complex.I
  simp only [map_one, one_mul, RCLike.re_to_complex] at h1
  simp only [Complex.conj_I, RCLike.re_to_complex, neg_mul, Complex.neg_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_neg] at h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

end Test

/-- Zero correlation of `pv` at every real vector of forbidden length, odd dimension. -/
theorem pv_corr_odd (hm : 0 < m) (i : Fin k) {d : ℝ} (hd : d ∈ D) (hdA : IsAlgebraic ℚ d)
    (hd0 : 0 < d) (y : X m 1) (hy : usq y = d ^ 2) :
    ⟪pv ω i, Ext ω (pv ω i) y⟫_ℂ = 0 := by
  have hc := Ext_continuous ω le_rfl (pv_plane ω i) (pv_line ω i)
  let G : (Fin m → ℂ) × ℝ → ℂ := fun p => ⟪pv ω i, Ext ω (pv ω i) (p.1, fun _ => p.2)⟫_ℂ
  have hG : Continuous G :=
    continuous_const.inner (hc.comp (continuous_fst.prodMk (continuous_pi fun _ => continuous_snd)))
  -- along all real unit directions, for `|s| < d`
  have hsph : ∀ s : ℝ, |s| < d → ∀ z : Fin m → ℂ, nsq z = 1 →
      G (((rho d s : ℝ) : ℂ) • z, s) = 0 := by
    intro s hs z hz
    have hcl : IsClosed {z : Fin m → ℂ | G (((rho d s : ℝ) : ℂ) • z, s) = 0} :=
      isClosed_eq (hG.comp ((continuous_const_smul ((rho d s : ℝ) : ℂ)).prodMk continuous_const))
        continuous_const
    have hsub : {y | ∃ u : Fin m → E, (∀ j, u j ≠ 0) ∧ nsq (embP u) = 1 ^ 2 ∧ embP u = y} ⊆
        {z : Fin m → ℂ | G (((rho d s : ℝ) : ℂ) • z, s) = 0} := by
      rintro _ ⟨u, hu0, hu1, rfl⟩
      rw [one_pow] at hu1
      have := bfun_zero ω i hd hdA hu0 hu1 s hs
      exact this
    exact closure_minimal hsub hcl (sphere_closure isAlgebraic_one one_pos (by rw [hz, one_pow]))
  have hIcc : ∀ z : Fin m → ℂ, nsq z = 1 → ∀ s ∈ Set.Icc (-d) d,
      G (((rho d s : ℝ) : ℂ) • z, s) = 0 := by
    intro z hz
    have hcl : IsClosed {s : ℝ | G (((rho d s : ℝ) : ℂ) • z, s) = 0} :=
      isClosed_eq (hG.comp (((Complex.continuous_ofReal.comp (rho_continuous d)).smul
        continuous_const).prodMk continuous_id)) continuous_const
    have hsub : Set.Ioo (-d) d ⊆ {s : ℝ | G (((rho d s : ℝ) : ℂ) • z, s) = 0} :=
      fun s hs => hsph s (abs_lt.mpr ⟨hs.1, hs.2⟩) z hz
    have := closure_minimal hsub hcl
    rw [closure_Ioo (by linarith)] at this
    exact fun s hs => this hs
  set s := y.2 0
  have hy2 : y = (y.1, fun _ => s) := Prod.ext rfl (funext fun i => by
    rw [show i = 0 from Subsingleton.elim _ _])
  have hys : nsq y.1 + s ^ 2 = d ^ 2 := by simpa [usq] using hy
  have hs2 : s ^ 2 ≤ d ^ 2 := by nlinarith [nsq_nonneg y.1]
  have hsI : s ∈ Set.Icc (-d) d := by
    constructor
    · by_contra h; push Not at h; nlinarith
    · by_contra h; push Not at h; nlinarith
  have hrho : rho d s = Real.sqrt (nsq y.1) := by rw [rho, ← hys]; ring_nf
  rw [hy2]
  by_cases h0 : nsq y.1 = 0
  · have hz : y.1 = 0 := by
      funext j
      have hle := Finset.single_le_sum (f := fun j => ‖y.1 j‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ j)
      have : ‖y.1 j‖ ^ 2 = 0 := le_antisymm (by unfold nsq at h0; linarith) (by positivity)
      simpa using this
    let e : Fin m → ℂ := Pi.single ⟨0, hm⟩ 1
    have he : nsq e = 1 := by
      unfold nsq
      rw [Finset.sum_eq_single ⟨0, hm⟩ (fun b _ hb => by simp [e, hb]) (by simp)]
      simp [e]
    have := hIcc e he s hsI
    rw [hrho, h0, Real.sqrt_zero, Complex.ofReal_zero, zero_smul] at this
    rw [hz]
    exact this
  · have hp : 0 < nsq y.1 := lt_of_le_of_ne (nsq_nonneg _) (Ne.symm h0)
    have hq : Real.sqrt (nsq y.1) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
    let z : Fin m → ℂ := ((1 / Real.sqrt (nsq y.1) : ℝ) : ℂ) • y.1
    have hz : nsq z = 1 := by
      rw [nsq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hp.le]
      field_simp
    have := hIcc z hz s hsI
    have hzz : ((rho d s : ℝ) : ℂ) • z = y.1 := by
      rw [hrho, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel hq, Complex.ofReal_one,
        one_smul]
    rw [hzz] at this
    exact this

end HNN
end
end OAI
