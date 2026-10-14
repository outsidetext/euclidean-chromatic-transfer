import OAI.Analysis.PlaneSpectrum.CircleDecay

/-!
# Fourier core on the torus

Let `E` be a measurable subset of the torus `(ℝ/ℤ)²` of measure `α`, and `ρ_0, …, ρ_{J-1}`
radii with consecutive ratios at least `4K`. If no translate `θ + ρ_j u` (`θ ∈ E`, `u` a unit
vector) lies in `E`, then Parseval for `⟨1_E, 1_E(· + ρ_j u)⟩`, averaged over the unit circle,
gives `0 = Σ_n |ĝ_n|² σ̂(ρ_j ξ_n)` with `σ̂ = circleSymbol`. Splitting frequencies into a low band
(`Re σ̂ ≥ 0`), a high band (`|σ̂| ≤ a/2` by `circleSymbol_sq_bound`) and a middle band, which
is met by at most one `j`, and using that the zero mode carries `α²`, yields `J a ≤ 2` for
every `0 < a ≤ α` with `400/(1+K) ≤ (a/2)²`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set UnitAddTorus ComplexConjugate
open OAI.EuclideanFiveColor

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The two-dimensional unit torus. -/
abbrev Tor := UnitAddTorus (Fin 2)

lemma fourier_arg_add (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

lemma fourier_neg_neg (n : ℤ) (x : UnitAddCircle) : fourier (-n) (-x) = fourier n x := by
  simp only [fourier_apply, neg_smul_neg]

lemma mFourier_arg_add (n : Fin 2 → ℤ) (x y : Tor) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_arg_add,
    Finset.prod_mul_distrib]

lemma mFourier_neg_neg (n : Fin 2 → ℤ) (x : Tor) : mFourier (-n) (-x) = mFourier n x := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_neg_neg]

/-- Fourier coefficients of a translate. -/
lemma coeff_translate (g : Tor → ℂ) (w : Tor) (n : Fin 2 → ℤ) :
    mFourierCoeff (fun θ => g (θ + w)) n = mFourier n w * mFourierCoeff g n := by
  unfold mFourierCoeff
  have h := integral_add_right_eq_self (μ := (volume : Measure Tor))
    (fun θ => mFourier (-n) (θ - w) • g θ) w
  simp only [add_sub_cancel_right] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext θ
  rw [sub_eq_add_neg, mFourier_arg_add, mFourier_neg_neg, smul_eq_mul, smul_eq_mul]
  ring

lemma coeff_congr {g h : Tor → ℂ} (hgh : g =ᵐ[volume] h) (n : Fin 2 → ℤ) :
    mFourierCoeff g n = mFourierCoeff h n :=
  integral_congr_ae (by filter_upwards [hgh] with θ hθ; rw [hθ])

/-- Parseval for norms, for a function (not an `Lp` class). -/
lemma hasSum_wt {g : Tor → ℂ} (hg : MemLp g 2 volume) :
    HasSum (fun n => ‖mFourierCoeff g n‖ ^ 2) (∫ θ, ‖g θ‖ ^ 2) := by
  have h := hasSum_sq_mFourierCoeff (hg.toLp g)
  simp only [coeff_congr hg.coeFn_toLp] at h
  convert h using 1
  exact integral_congr_ae (by filter_upwards [hg.coeFn_toLp] with θ hθ; rw [hθ])

/-- Parseval for `⟨g, g(· + w)⟩`. -/
lemma parseval_translate {g : Tor → ℂ} (hg : MemLp g 2 volume) (w : Tor) :
    HasSum (fun n => ((‖mFourierCoeff g n‖ ^ 2 : ℝ) : ℂ) * mFourier n w)
      (∫ θ, conj (g θ) * g (θ + w)) := by
  have hmp : MeasurePreserving (fun θ : Tor => θ + w) volume volume :=
    measurePreserving_add_right volume w
  have hgw : MemLp (fun θ => g (θ + w)) 2 volume := hg.comp_measurePreserving hmp
  have h := hasSum_prod_mFourierCoeff (hg.toLp g) (hgw.toLp _)
  simp only [coeff_congr hg.coeFn_toLp, coeff_congr hgw.coeFn_toLp, coeff_translate] at h
  have hI : ∫ θ, conj ((hg.toLp g) θ) * (hgw.toLp _) θ = ∫ θ, conj (g θ) * g (θ + w) :=
    integral_congr_ae (by
      filter_upwards [hg.coeFn_toLp, hgw.coeFn_toLp] with θ h1 h2
      rw [h1, h2])
  rw [hI] at h
  convert h using 2 with n
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  ring

/-! ### Circle averages -/

/-- A point of `ℂ` viewed in the torus. -/
def tp (v : ℂ) : Tor := fun i => ((![v.re, v.im] i : ℝ) : UnitAddCircle)

/-- The frequency `n` as a complex number. -/
def xi (n : Fin 2 → ℤ) : ℂ := (n 0 : ℂ) + (n 1 : ℂ) * Complex.I

lemma mFourier_tp (n : Fin 2 → ℤ) (v : ℂ) : mFourier n (tp v) = planePhase v (xi n) := by
  simp only [mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two, tp, fourier_coe_apply,
    planePhase, Real.fourierChar_apply, Complex.inner, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.exp_add]
  congr 1
  simp only [xi, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

lemma planePhase_smul (ρ : ℝ) (h ξ : ℂ) : planePhase (ρ • h) ξ = planePhase h (ρ • ξ) := by
  simp only [planePhase, real_inner_smul_left, real_inner_smul_right]

lemma phase_continuous (ξ : ℂ) : Continuous (fun t : Angles => planePhase (direction t) ξ) := by
  unfold planePhase
  exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
    (direction_continuous.inner continuous_const)

lemma phase_integrable (ξ : ℂ) :
    Integrable (fun t => planePhase (direction t) ξ) angularMeasure :=
  Integrable.of_bound (phase_continuous ξ).aestronglyMeasurable 1
    (Eventually.of_forall fun _ => (planePhase_norm _ _).le)

/-- If `g(θ) g(θ + ρu) = 0` for all `θ` and all unit `u`, then
`Σ_n |ĝ_n|² Re σ̂(ρ ξ_n) = 0`. -/
lemma circle_sum_zero {g : Tor → ℂ} (hg : MemLp g 2 volume) (ρ : ℝ)
    (hvan : ∀ t : Angles, ∀ θ, conj (g θ) * g (θ + tp (ρ • direction t)) = 0) :
    HasSum (fun n => ‖mFourierCoeff g n‖ ^ 2 * (circleSymbol (ρ • xi n)).re) 0 := by
  set w := fun n => ‖mFourierCoeff g n‖ ^ 2 with hwdef
  have hw : Summable w := (hasSum_wt hg).summable
  let F : (Fin 2 → ℤ) → Angles → ℂ := fun n t => (w n : ℂ) * planePhase (direction t) (ρ • xi n)
  have hpt : ∀ t, HasSum (fun n => F n t) 0 := by
    intro t
    have h := parseval_translate hg (tp (ρ • direction t))
    have h0 : (∫ θ, conj (g θ) * g (θ + tp (ρ • direction t))) = 0 := by
      simp only [hvan t, integral_zero]
    rw [h0] at h
    simpa only [F, mFourier_tp, planePhase_smul] using h
  have hint : ∀ n, Integrable (F n) angularMeasure := fun n => (phase_integrable _).const_mul _
  have hnorm : ∀ n, ∫ t, ‖F n t‖ ∂angularMeasure = w n := by
    intro n
    simp only [F, norm_mul, planePhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      integral_const, probReal_univ, one_smul]
    exact abs_of_nonneg (sq_nonneg _)
  have hsum := integral_tsum_of_summable_integral_norm hint (by simpa only [hnorm] using hw)
  have hzero : ∑' n, ∫ t, F n t ∂angularMeasure = 0 := by
    rw [hsum]
    simp only [(hpt _).tsum_eq, integral_zero]
  have hFi : ∀ n, ∫ t, F n t ∂angularMeasure = (w n : ℂ) * circleSymbol (ρ • xi n) := fun n => by
    simp only [F, integral_const_mul, circleSymbol]
  have hS : Summable (fun n => (w n : ℂ) * circleSymbol (ρ • xi n)) := by
    refine Summable.of_norm_bounded hw (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_right (sq_nonneg _) (circleSymbol_norm_le_one _)
  have hH : HasSum (fun n => (w n : ℂ) * circleSymbol (ρ • xi n)) 0 := by
    have h := hS.hasSum
    simp only [← hFi] at h ⊢
    rwa [hzero] at h
  simpa only [RCLike.re_to_complex, Complex.re_ofReal_mul, map_zero] using RCLike.hasSum_re ℂ hH

/-! ### Frequency bands -/

lemma circleSymbol_zero : circleSymbol 0 = 1 := by
  simp [circleSymbol, planePhase]

lemma re_circleSymbol_nonneg {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1 / 4) : 0 ≤ (circleSymbol ξ).re := by
  have h := integral_re (phase_integrable ξ)
  simp only [RCLike.re_to_complex] at h
  rw [circleSymbol, ← h]
  apply integral_nonneg
  intro t
  simp only [planePhase, Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re]
  have hi := abs_real_inner_le_norm (direction t) ξ
  rw [direction_norm, one_mul] at hi
  have hb := abs_le.mp (hi.trans hξ)
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> nlinarith [Real.pi_pos]

lemma norm_circleSymbol_le_of_large {ξ : ℂ} {K a : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hKa : 400 / (1 + K) ≤ (a / 2) ^ 2) (hξ : K ≤ ‖ξ‖) : ‖circleSymbol ξ‖ ≤ a / 2 := by
  have h1 := circleSymbol_sq_bound ξ
  have h2 : 400 / (1 + ‖ξ‖) ≤ 400 / (1 + K) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  nlinarith [norm_nonneg (circleSymbol ξ)]

/-- For each frequency, the sum over the radii of `Re σ̂(ρ_j ξ)` is at least `-(1 + J a/2)`:
every term is `≥ -a/2` except at most one middle-band term, which is `≥ -1`. -/
lemma band_sum (ρ : ℕ → ℝ) (J : ℕ) {a K : ℝ} (ha : 0 < a) (hK : 0 < K)
    (hKa : 400 / (1 + K) ≤ (a / 2) ^ 2) (hρ : ∀ j, 0 < ρ j)
    (hsep : ∀ i j, i < j → 4 * K * ρ i ≤ ρ j) (ξ : ℂ) :
    -(1 + J * a / 2) ≤ ∑ j ∈ Finset.range J, (circleSymbol (ρ j • ξ)).re := by
  classical
  set M := (Finset.range J).filter (fun j => 1 / 4 < ρ j * ‖ξ‖ ∧ ρ j * ‖ξ‖ < K) with hMdef
  have hM : M.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [M, Finset.mem_filter] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hsep i j h
      nlinarith [norm_nonneg ξ, hi.2.1, hj.2.2, mul_le_mul_of_nonneg_right this (norm_nonneg ξ)]
    · have := hsep j i h
      nlinarith [norm_nonneg ξ, hj.2.1, hi.2.2, mul_le_mul_of_nonneg_right this (norm_nonneg ξ)]
  have hterm : ∀ j ∈ Finset.range J,
      -(a / 2) - (if j ∈ M then (1 : ℝ) else 0) ≤ (circleSymbol (ρ j • ξ)).re := by
    intro j hj
    have hn : ‖ρ j • ξ‖ = ρ j * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg (hρ j).le]
    have hre := Complex.abs_re_le_norm (circleSymbol (ρ j • ξ))
    have hre' := neg_abs_le (circleSymbol (ρ j • ξ)).re
    have hif : (0 : ℝ) ≤ (if j ∈ M then (1 : ℝ) else 0) := by split_ifs <;> norm_num
    by_cases h1 : ρ j * ‖ξ‖ ≤ 1 / 4
    · have := re_circleSymbol_nonneg (hn ▸ h1 : ‖ρ j • ξ‖ ≤ 1 / 4)
      linarith
    by_cases h2 : K ≤ ρ j * ‖ξ‖
    · have := norm_circleSymbol_le_of_large ha hK.le hKa (hn ▸ h2 : K ≤ ‖ρ j • ξ‖)
      linarith
    · have hjM : j ∈ M := by
        simp only [M, Finset.mem_filter]
        exact ⟨hj, by linarith, by linarith⟩
      simp only [hjM, ↓reduceIte]
      have := circleSymbol_norm_le_one (ρ j • ξ)
      linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, Finset.sum_boole] at hsum
  have hc : (((Finset.range J).filter (fun j => j ∈ M)).card : ℝ) ≤ 1 := by
    have : (Finset.range J).filter (fun j => j ∈ M) ⊆ M := fun j hj =>
      (Finset.mem_filter.mp hj).2
    exact_mod_cast (Finset.card_le_card this).trans hM
  simp only [nsmul_eq_mul] at hsum
  linarith

/-! ### The torus bound -/

lemma indicator_memLp (E : Set Tor) (hE : MeasurableSet E) :
    MemLp (E.indicator (fun _ => (1 : ℂ))) 2 volume :=
  MemLp.of_bound ((measurable_const.indicator hE).aestronglyMeasurable) 1
    (Eventually.of_forall fun θ => by by_cases h : θ ∈ E <;> simp [h])

/-- **Torus bound.** A measurable `E ⊆ (ℝ/ℤ)²` of measure `≥ a` such that no `θ + ρ_j u`
(`θ ∈ E`, `|u| = 1`, `j < J`) lies in `E`, for radii with ratios `≥ 4K`, has `J a ≤ 2`. -/
theorem torus_bound (E : Set Tor) (hE : MeasurableSet E) (ρ : ℕ → ℝ) (J : ℕ) {a K : ℝ}
    (ha : 0 < a) (haE : a ≤ (volume E).toReal) (hK : 0 < K) (hKa : 400 / (1 + K) ≤ (a / 2) ^ 2)
    (hρ : ∀ j, 0 < ρ j) (hsep : ∀ i j, i < j → 4 * K * ρ i ≤ ρ j)
    (havoid : ∀ j < J, ∀ t : Angles, ∀ θ ∈ E, θ + tp (ρ j • direction t) ∉ E) :
    J * a ≤ 2 := by
  classical
  set g : Tor → ℂ := E.indicator (fun _ => 1) with hgdef
  have hg := indicator_memLp E hE
  set α := (volume E).toReal with hαdef
  set w := fun n => ‖mFourierCoeff g n‖ ^ 2 with hwdef
  have hw : HasSum w α := by
    have h := hasSum_wt hg
    have he : (fun θ => ‖g θ‖ ^ 2) = E.indicator (fun _ => (1 : ℝ)) := by
      funext θ
      by_cases h : θ ∈ E <;> simp [g, h]
    rw [he, integral_indicator_const _ hE, smul_eq_mul, mul_one] at h
    exact h
  have hw0 : w 0 = α ^ 2 := by
    have : mFourierCoeff g 0 = (α : ℂ) := by
      simp only [mFourierCoeff, neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul, g]
      rw [integral_indicator_const _ hE, Measure.real, Complex.real_smul, mul_one]
    simp only [w, this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hα1 : α ≤ 1 := by
    rw [hαdef]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hj : ∀ j ∈ Finset.range J, HasSum (fun n => w n * (circleSymbol (ρ j • xi n)).re) 0 := by
    intro j hj
    apply circle_sum_zero hg
    intro t θ
    by_cases h1 : θ ∈ E
    · have := havoid j (Finset.mem_range.mp hj) t θ h1
      rw [Set.indicator_of_notMem this, mul_zero]
    · rw [Set.indicator_of_notMem h1, map_zero, zero_mul]
  have htot := hasSum_sum hj
  simp only [Finset.sum_const_zero] at htot
  set c := (1 + J * a / 2) with hc
  have hlb : HasSum (fun n => w n * (-c) + (if n = 0 then (J + c) * α ^ 2 else 0))
      (α * (-c) + (J + c) * α ^ 2) :=
    (hw.mul_right _).add (hasSum_ite_eq 0 _)
  have hle : ∀ n, w n * (-c) + (if n = 0 then (J + c) * α ^ 2 else 0) ≤
      ∑ j ∈ Finset.range J, w n * (circleSymbol (ρ j • xi n)).re := by
    intro n
    rw [← Finset.mul_sum]
    have hb := band_sum ρ J ha hK hKa hρ hsep (xi n)
    have hwn : 0 ≤ w n := sq_nonneg _
    by_cases hn : n = 0
    · subst hn
      have hx : xi 0 = 0 := by simp [xi]
      simp only [hx, smul_zero, circleSymbol_zero, Complex.one_re, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, ↓reduceIte, hw0]
      nlinarith
    · simp only [hn, ↓reduceIte, add_zero]
      nlinarith [mul_le_mul_of_nonneg_left hb hwn]
  have key := hasSum_le hle hlb htot
  have hαpos : 0 < α := lt_of_lt_of_le ha haE
  have h1 : -c + (J + c) * α ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hαpos hcon]
  have h2 : (J : ℝ) * a ≤ J * α := mul_le_mul_of_nonneg_left haE (Nat.cast_nonneg _)
  have h3 : 0 ≤ (J : ℝ) * a / 2 * α := by positivity
  nlinarith

end
end OAI.Soifer
