import OAI.Soifer.Delsarte

/-!
# A lacunary Delsarte certificate

With `q = 10⁶`, weights `v_j = (1/2)(3/2)^j` and
`H_K(ξ) = Σ_{j<K} v_j Re σ̂(q^j ξ)`, we prove `H_K(ξ) ≥ -1` for every `ξ`, using only
`|σ̂| ≤ 1`, `Re σ̂(ξ) ≥ 1 - 2π²‖ξ‖²` and `|σ̂(ξ)|² ≤ 400/(1+‖ξ‖)`.

The proof is an induction on `K` through `H_{K+1}(ξ) = (1/2) Re σ̂(ξ) + (3/2) H_K(qξ)`, with
the invariant (μ = 3/2000)
* `‖ξ‖ ≤ 1/10`            ⇒ `H_K(ξ) ≥ -1/2`,
* `‖ξ‖ > 1/10`            ⇒ `H_K(ξ) ≥ -(1/2)(1 + (3/2)·70·μ)`,
* `‖ξ‖ > q^i/10`, `i ≥ 1` ⇒ `H_K(ξ) ≥ -(1/2)·70·μ^i`.
Since `Σ_{j<K} v_j = (3/2)^K - 1`, the Delsarte function `1 + H_K` certifies density
`≤ (2/3)^K`.
-/

namespace OAI.Soifer

noncomputable section
open OAI.EuclideanFiveColor

/-- The lacunarity ratio `q = 10⁶`. -/
def qL : ℝ := 10 ^ 6

lemma qL_eq : qL = 1000000 := by norm_num [qL]

lemma qL_pos : 0 < qL := by rw [qL_eq]; norm_num

/-- The lacunary Delsarte sum. -/
def lacH (K : ℕ) (ξ : ℂ) : ℝ :=
  ∑ j ∈ Finset.range K, (1 / 2) * (3 / 2 : ℝ) ^ j * (circleSymbol (qL ^ j • ξ)).re

lemma lacH_zero (ξ : ℂ) : lacH 0 ξ = 0 := by simp [lacH]

lemma lacH_succ (K : ℕ) (ξ : ℂ) :
    lacH (K + 1) ξ = (1 / 2) * (circleSymbol ξ).re + (3 / 2) * lacH K (qL • ξ) := by
  rw [lacH, Finset.sum_range_succ', lacH, Finset.mul_sum]
  simp only [pow_zero, mul_one, one_smul]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show qL ^ (j + 1) • ξ = qL ^ j • qL • ξ by rw [pow_succ, mul_smul]]
  ring

lemma weights_sum (K : ℕ) :
    ∑ j ∈ Finset.range K, (1 / 2) * (3 / 2 : ℝ) ^ j = (3 / 2) ^ K - 1 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma norm_qL_smul (ξ : ℂ) : ‖qL • ξ‖ = qL * ‖ξ‖ := by
  rw [norm_smul, Real.norm_of_nonneg qL_pos.le]

lemma re_ge_neg_norm (z : ℂ) : -‖z‖ ≤ z.re := by
  have h1 := Complex.abs_re_le_norm z
  have h2 := neg_abs_le z.re
  linarith

/-- The induction invariant. -/
structure LacInv (K : ℕ) : Prop where
  low : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 / 10 → -(1 / 2) ≤ lacH K ξ
  mid : ∀ ξ : ℂ, 1 / 10 < ‖ξ‖ → -(1 / 2) * (1 + 3 / 2 * 70 * (3 / 2000)) ≤ lacH K ξ
  high : ∀ i : ℕ, 1 ≤ i → ∀ ξ : ℂ, qL ^ i / 10 < ‖ξ‖ →
    -(1 / 2) * (70 * (3 / 2000 : ℝ) ^ i) ≤ lacH K ξ

lemma lacInv_all (K : ℕ) : LacInv K := by
  induction K with
  | zero =>
    refine ⟨fun ξ _ => ?_, fun ξ _ => ?_, fun i _ ξ _ => ?_⟩ <;> rw [lacH_zero]
    · norm_num
    · norm_num
    · have : (0 : ℝ) ≤ 70 * (3 / 2000 : ℝ) ^ i := by positivity
      linarith
  | succ K ih =>
    have hq := qL_eq
    refine ⟨fun ξ hξ => ?_, fun ξ hξ => ?_, fun i hi ξ hξ => ?_⟩
    · -- low band
      rw [lacH_succ]
      have h1 := re_circleSymbol_ge ξ
      have hpi := Real.pi_lt_d2
      have hpi0 := Real.pi_pos
      have hn2 : ‖ξ‖ ^ 2 ≤ 1 / 100 := by nlinarith [norm_nonneg ξ]
      have hp2 : Real.pi ^ 2 ≤ 3.15 ^ 2 := by nlinarith
      have hre : (0.8 : ℝ) ≤ (circleSymbol ξ).re := by nlinarith
      by_cases h2 : ‖qL • ξ‖ ≤ 1 / 10
      · have := ih.low _ h2
        linarith
      · have := ih.mid _ (lt_of_not_ge h2)
        norm_num at this ⊢
        linarith
    · -- middle band
      rw [lacH_succ]
      have h1 : -1 ≤ (circleSymbol ξ).re := by
        have := re_ge_neg_norm (circleSymbol ξ)
        have := circleSymbol_norm_le_one ξ
        linarith
      have h2 := ih.high 1 le_rfl (qL • ξ) (by rw [norm_qL_smul, pow_one, hq]; linarith)
      rw [pow_one] at h2
      linarith
    · -- high bands
      rw [lacH_succ]
      have hqi : 0 < qL ^ i := pow_pos qL_pos i
      have h2 := ih.high (i + 1) (by omega) (qL • ξ) (by
        rw [norm_qL_smul, pow_succ]
        rw [hq] at hξ ⊢
        nlinarith)
      set p : ℝ := (3 / 2000 : ℝ) ^ i with hp
      have hp0 : 0 < p := by positivity
      have hpq : p ^ 2 * qL ^ i = (9 / 4) ^ i := by
        rw [hp, hq, ← pow_mul, mul_comm i 2, pow_mul, ← mul_pow]
        norm_num
      have hpq1 : 1 ≤ p ^ 2 * qL ^ i := by rw [hpq]; exact one_le_pow₀ (by norm_num)
      have hs := circleSymbol_sq_bound ξ
      have hs1 : 400 / (1 + ‖ξ‖) ≤ 4000 / qL ^ i := by
        rw [div_le_div_iff₀ (by positivity) hqi]
        nlinarith [norm_nonneg ξ]
      have hs2 : 4000 / qL ^ i ≤ 4000 * p ^ 2 := by
        rw [div_le_iff₀ hqi]
        nlinarith
      set B : ℝ := 70 * p * (1 - 3 / 2 * (3 / 2000)) with hB
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      have hB2 : 4000 * p ^ 2 ≤ B ^ 2 := by rw [hB]; nlinarith
      have hnorm : ‖circleSymbol ξ‖ ≤ B := by nlinarith [norm_nonneg (circleSymbol ξ)]
      have hre := re_ge_neg_norm (circleSymbol ξ)
      rw [pow_succ, ← hp] at h2
      rw [hB] at hnorm
      linarith

/-- **Lacunary certificate.** `1 + H_K ≥ 0` everywhere. -/
theorem lacH_ge (K : ℕ) (ξ : ℂ) : -1 ≤ lacH K ξ := by
  by_cases h : ‖ξ‖ ≤ 1 / 10
  · have := (lacInv_all K).low ξ h
    linarith
  · have := (lacInv_all K).mid ξ (lt_of_not_ge h)
    norm_num at this
    linarith

end
end OAI.Soifer
