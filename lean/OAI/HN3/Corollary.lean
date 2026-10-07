import OAI.HN3.Density

/-!
# Chromatic number of three-space from a density bound

`DensityBound δ` says that every measurable subset of `ℝ³` without two points at distance one
has upper density at most `δ` with respect to centered cubes. DeCorte, Oliveira and Vallentin
(Math. Program. 2022, Table 2) prove `DensityBound 0.1532996`. With the transfer theorem this
excludes proper six-colorings of `ℝ³` with arbitrary color classes.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace HN3

/-- The cube `[-T,T]³` in coordinates `(Re z, Im z, t)`. -/
def cube (T : ℝ) : Set (ℂ × ℝ) := {x | |x.1.re| ≤ T ∧ |x.1.im| ≤ T ∧ |x.2| ≤ T}

lemma cube_measurable (T : ℝ) : MeasurableSet (cube T) := by
  apply IsClosed.measurableSet
  unfold cube
  have h1 : Continuous fun x : ℂ × ℝ => |x.1.re| := by fun_prop
  have h2 : Continuous fun x : ℂ × ℝ => |x.1.im| := by fun_prop
  have h3 : Continuous fun x : ℂ × ℝ => |x.2| := by fun_prop
  exact (isClosed_le h1 continuous_const).inter
    ((isClosed_le h2 continuous_const).inter (isClosed_le h3 continuous_const))

lemma cube_finite (T : ℝ) : volume (cube T) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    ((isCompact_closedBall (0 : ℂ × ℝ) (2 * |T| + 1)).measure_ne_top (μ := volume))
  apply measure_mono
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  have hz : ‖x.1‖ ≤ 2 * |T| + 1 := by
    have := Complex.norm_le_abs_re_add_abs_im x.1
    have hT : T ≤ |T| := le_abs_self T
    linarith
  have ht : ‖x.2‖ ≤ 2 * |T| + 1 := by
    rw [Real.norm_eq_abs]
    have hT : T ≤ |T| := le_abs_self T
    have := abs_nonneg T
    linarith
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le hz ht

lemma cube_pos {T : ℝ} (hT : 0 < T) : volume (cube T) ≠ 0 := by
  apply (Metric.measure_ball_pos volume (0 : ℂ × ℝ) hT).ne' ∘ measure_mono_null ?_
  intro x hx
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · exact (Complex.abs_re_le_norm x.1).trans h1.le
  · exact (Complex.abs_im_le_norm x.1).trans h1.le
  · rw [← Real.norm_eq_abs]; exact h2.le

/-- Every measurable unit-distance-free set has upper cube density at most `δ`. -/
def DensityBound (δ : ℝ) : Prop :=
  ∀ S : Set (ℂ × ℝ), MeasurableSet S → (∀ x ∈ S, ∀ y ∈ S, usq (x - y) ≠ 1) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
      volume (S ∩ cube T) ≤ ENNReal.ofReal (δ + ε) * volume (cube T)

/-- A density bound gives a lower bound for the number of colors of an arbitrary proper
coloring of `ℝ³`. -/
theorem colors_ge_of_density {δ : ℝ} (hδ : DensityBound δ) {k : ℕ} [NeZero k]
    (c : ℂ × ℝ → Fin k) (hc : ∀ x y : ℂ × ℝ, usq (x - y) = 1 → c x ≠ c y) :
    1 ≤ (k : ℝ) * δ := by
  obtain ⟨A, hAm, hAd, hAn, hAu⟩ := proper_partition3 c hc
  by_contra hlt
  push_neg at hlt
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  set ε := (1 - k * δ) / (2 * k) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  have hkε : (k : ℝ) * (δ + ε) < 1 := by
    have : (k : ℝ) * ε = (1 - k * δ) / 2 := by
      rw [hε]; field_simp
    rw [mul_add, this]
    linarith
  have hev : ∀ᶠ T in atTop, ∀ i, volume (A i ∩ cube T) ≤ ENNReal.ofReal (δ + ε) * volume (cube T) :=
    eventually_all.mpr fun i => hδ (A i) (hAm i) (hAu i) ε hεpos
  obtain ⟨T, hT, hT1⟩ := (hev.and (eventually_gt_atTop 0)).exists
  have hsum : volume (cube T) = ∑ i, volume (A i ∩ cube T) := by
    have h1 : volume (cube T) = volume ((⋃ i, A i) ∩ cube T) := by
      apply le_antisymm _ (measure_mono inter_subset_right)
      calc volume (cube T) ≤ volume (((⋃ i, A i) ∩ cube T) ∪ (⋃ i, A i)ᶜ) :=
            measure_mono (fun x hx => by
              by_cases h : x ∈ ⋃ i, A i
              · exact Or.inl ⟨h, hx⟩
              · exact Or.inr h)
        _ ≤ volume ((⋃ i, A i) ∩ cube T) + volume (⋃ i, A i)ᶜ := measure_union_le _ _
        _ = volume ((⋃ i, A i) ∩ cube T) := by rw [hAn, add_zero]
    rw [h1, iUnion_inter, measure_iUnion]
    · rw [tsum_fintype]
    · intro i j hij
      exact (hAd hij).mono inter_subset_left inter_subset_left
    · exact fun i => (hAm i).inter (cube_measurable T)
  have hle : volume (cube T) ≤ (k : ENNReal) * (ENNReal.ofReal (δ + ε) * volume (cube T)) := by
    calc volume (cube T) = ∑ i, volume (A i ∩ cube T) := hsum
      _ ≤ ∑ _i : Fin k, ENNReal.ofReal (δ + ε) * volume (cube T) :=
          Finset.sum_le_sum fun i _ => hT i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfin := cube_finite T
  have hpos := cube_pos hT1
  rw [← mul_assoc] at hle
  have hc1 : (k : ENNReal) * ENNReal.ofReal (δ + ε) < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact (ENNReal.ofReal_lt_one).mpr hkε
  have h := ENNReal.mul_lt_mul_right hpos hfin hc1
  rw [mul_one, mul_comm] at h
  exact absurd hle (not_le.mpr h)

/-- **χ(ℝ³) ≥ 7**, conditional on the published density bound of DeCorte–Oliveira–Vallentin:
there is no proper six-coloring of three-space, even with arbitrary color classes. -/
theorem no_six_coloring_of_density (hDOV : DensityBound 0.1532996) :
    ¬ ∃ c : ℂ × ℝ → Fin 6, ∀ x y : ℂ × ℝ, usq (x - y) = 1 → c x ≠ c y := by
  rintro ⟨c, hc⟩
  have := colors_ge_of_density hDOV c hc
  norm_num at this

end HN3
end
end OAI
