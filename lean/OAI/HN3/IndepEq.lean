import OAI.HN3.IndepFolner

/-!
# `α₁(ℝ³) = m₁(ℝ³)`

The easy direction `m₁ ≤ α₁`: for every nonempty finite point set `P`, the ratio
`α(P)/|P|` is a density bound. If `A` is measurable and unit-distance-free, then for every `x` the
set `{s ∈ P : x + s ∈ A}` is independent, so `∑_{s ∈ P} 1_A(x + s) ≤ α(P)`. Integrating over the
cube `Q_{T+R}` (with `P ⊆ Q_R`) gives `|P| · vol(A ∩ Q_T) ≤ α(P) · vol(Q_{T+R})`, and
`vol(Q_{T+R}) / vol(Q_T) = (1 + R/T)^3 → 1`. With `alpha1_le_m1` this gives `alpha1 = m1`.
-/

set_option linter.unusedSectionVars false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal Pointwise
namespace HN3
namespace Indep

lemma cube_smul {c : ℝ} (hc : 0 < c) (T : ℝ) : cube (c * T) = c • cube T := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  change (|x.1.re| ≤ c * T ∧ |x.1.im| ≤ c * T ∧ |x.2| ≤ c * T) ↔
    (|(c⁻¹ • x).1.re| ≤ T ∧ |(c⁻¹ • x).1.im| ≤ T ∧ |(c⁻¹ • x).2| ≤ T)
  simp only [Prod.smul_fst, Prod.smul_snd, Complex.smul_re, Complex.smul_im, smul_eq_mul,
    abs_mul, abs_inv, abs_of_pos hc, inv_mul_le_iff₀ hc]

lemma volume_cube_smul {c : ℝ} (hc : 0 < c) (T : ℝ) :
    volume (cube (c * T)) =
      ENNReal.ofReal (c ^ Module.finrank ℝ (ℂ × ℝ)) * volume (cube T) := by
  rw [cube_smul hc, Measure.addHaar_smul, abs_of_pos (pow_pos hc _)]

/-- **`m₁ ≤ α(P)/|P|`.** The independence ratio of every nonempty finite point set is a density
bound for measurable unit-distance-free subsets of `ℝ³`. -/
theorem densityBound_ratio (P : Finset (ℂ × ℝ)) (hP : P.Nonempty) :
    DensityBound ((indepNum P : ℝ) / P.card) := by
  classical
  intro A hA hAu ε hε
  set r : ℝ := (indepNum P : ℝ) / P.card with hr
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hr0 : 0 ≤ r := by positivity
  set R : ℝ := ∑ s ∈ P, (|s.1.re| + |s.1.im| + |s.2|) with hR
  have hR0 : 0 ≤ R := sum_nonneg fun s _ => by positivity
  have hPR : ∀ s ∈ P, |s.1.re| ≤ R ∧ |s.1.im| ≤ R ∧ |s.2| ≤ R := by
    intro s hs
    have := single_le_sum (f := fun s : ℂ × ℝ => |s.1.re| + |s.1.im| + |s.2|)
      (fun s _ => by positivity) hs
    have a1 := abs_nonneg s.1.re
    have a2 := abs_nonneg s.1.im
    have a3 := abs_nonneg s.2
    exact ⟨by linarith, by linarith, by linarith⟩
  set d := Module.finrank ℝ (ℂ × ℝ)
  have hlim : Tendsto (fun T : ℝ => r * (1 + R / T) ^ d) atTop (𝓝 (r * (1 + 0) ^ d)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).pow d).const_mul r
  have hev := hlim.eventually (eventually_lt_nhds
    (show r * (1 + 0) ^ d < r + ε by simp only [add_zero, one_pow, mul_one]; linarith))
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with T hT hT0
  have hc : 0 < 1 + R / T := by positivity
  have hcT : (1 + R / T) * T = T + R := by field_simp
  -- the counting inequality
  have key : (P.card : ℝ≥0∞) * volume (A ∩ cube T) ≤
      (indepNum P : ℝ≥0∞) * volume (cube (T + R)) := by
    have hmeas : ∀ s : ℂ × ℝ,
        Measurable fun x : ℂ × ℝ => A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) :=
      fun s => (measurable_one.indicator hA).comp (measurable_add_const s)
    have hlow : ∀ s ∈ P, volume (A ∩ cube T) ≤
        ∫⁻ x in cube (T + R), A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) := by
      intro s hs
      have hB : MeasurableSet ((fun x : ℂ × ℝ => x + s) ⁻¹' (A ∩ cube T)) :=
        (hA.inter (cube_measurable T)).preimage (measurable_add_const s)
      have hsub : (fun x : ℂ × ℝ => x + s) ⁻¹' (A ∩ cube T) ⊆ cube (T + R) := by
        rintro x ⟨-, h1, h2, h3⟩
        obtain ⟨r1, r2, r3⟩ := hPR s hs
        refine ⟨?_, ?_, ?_⟩
        · calc |x.1.re| = |(x + s).1.re - s.1.re| := by simp
            _ ≤ |(x + s).1.re| + |s.1.re| := abs_sub _ _
            _ ≤ T + R := add_le_add h1 r1
        · calc |x.1.im| = |(x + s).1.im - s.1.im| := by simp
            _ ≤ |(x + s).1.im| + |s.1.im| := abs_sub _ _
            _ ≤ T + R := add_le_add h2 r2
        · calc |x.2| = |(x + s).2 - s.2| := by simp
            _ ≤ |(x + s).2| + |s.2| := abs_sub _ _
            _ ≤ T + R := add_le_add h3 r3
      calc volume (A ∩ cube T) = volume ((fun x : ℂ × ℝ => x + s) ⁻¹' (A ∩ cube T)) :=
            (measure_preimage_add_right _ _ _).symm
        _ = ∫⁻ x in cube (T + R),
              ((fun x : ℂ × ℝ => x + s) ⁻¹' (A ∩ cube T)).indicator 1 x := by
            rw [lintegral_indicator_one hB, Measure.restrict_apply hB,
              Set.inter_eq_left.mpr hsub]
        _ ≤ ∫⁻ x in cube (T + R), A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) := by
            apply lintegral_mono
            intro x
            by_cases hx : x ∈ (fun x : ℂ × ℝ => x + s) ⁻¹' (A ∩ cube T)
            · have h1 : A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) = 1 := by
                rw [Set.indicator_of_mem hx.1]; rfl
              rw [Set.indicator_of_mem hx]
              change (1 : ℝ≥0∞) ≤ A.indicator 1 (x + s)
              rw [h1]
            · rw [Set.indicator_of_notMem hx]
              exact bot_le
    have hup : ∀ x : ℂ × ℝ,
        ∑ s ∈ P, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) ≤ (indepNum P : ℝ≥0∞) := by
      intro x
      have he : ∑ s ∈ P, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) =
          ((P.filter fun s => x + s ∈ A).card : ℝ≥0∞) := by
        rw [← sum_boole]
        apply sum_congr rfl
        intro s _
        simp [Set.indicator_apply]
      rw [he]
      have hmem : P.filter (fun s => x + s ∈ A) ∈ indepSets P := by
        refine mem_indepSets.mpr ⟨filter_subset _ _, fun y hy z hz h => ?_⟩
        apply hAu _ (mem_filter.mp hy).2 _ (mem_filter.mp hz).2
        rwa [add_sub_add_left_eq_sub]
      have := Finset.le_sup (f := Finset.card) hmem
      rw [indepNum]
      exact_mod_cast this
    calc (P.card : ℝ≥0∞) * volume (A ∩ cube T) = ∑ _s ∈ P, volume (A ∩ cube T) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ P, ∫⁻ x in cube (T + R), A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) :=
          sum_le_sum hlow
      _ = ∫⁻ x in cube (T + R), ∑ s ∈ P, A.indicator (1 : ℂ × ℝ → ℝ≥0∞) (x + s) :=
          (lintegral_finsetSum _ fun s _ => hmeas s).symm
      _ ≤ ∫⁻ _x in cube (T + R), (indepNum P : ℝ≥0∞) := lintegral_mono hup
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  have hvol : volume (cube (T + R)) = ENNReal.ofReal ((1 + R / T) ^ d) * volume (cube T) := by
    rw [← hcT, volume_cube_smul hc]
  have hX : volume (A ∩ cube T) ≤ ENNReal.ofReal r * volume (cube (T + R)) := by
    have hn0 : (P.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hP.card_pos.ne'
    have hnt : (P.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hnr : (P.card : ℝ≥0∞) * ENNReal.ofReal r = (indepNum P : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hr,
        mul_div_cancel₀ _ hn.ne', ENNReal.ofReal_natCast]
    rw [← ENNReal.mul_le_mul_iff_right hn0 hnt, ← mul_assoc, hnr]
    exact key
  calc volume (A ∩ cube T)
      ≤ ENNReal.ofReal r * (ENNReal.ofReal ((1 + R / T) ^ d) * volume (cube T)) := hvol ▸ hX
    _ = ENNReal.ofReal (r * (1 + R / T) ^ d) * volume (cube T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr0]
    _ ≤ ENNReal.ofReal (r + ε) * volume (cube T) := by
        gcongr

lemma m1_set_nonempty : {δ : ℝ | DensityBound δ}.Nonempty := ⟨1, densityBound_one⟩

lemma m1_set_bddBelow : BddBelow {δ : ℝ | DensityBound δ} :=
  ⟨0, fun _ h => densityBound_nonneg h⟩

lemma alpha1_set_nonempty :
    ((fun S : Finset (ℂ × ℝ) => (indepNum S : ℝ) / S.card) '' {S | S.Nonempty}).Nonempty :=
  ⟨_, {0}, Finset.singleton_nonempty 0, rfl⟩

lemma alpha1_set_bddBelow :
    BddBelow ((fun S : Finset (ℂ × ℝ) => (indepNum S : ℝ) / S.card) '' {S | S.Nonempty}) :=
  ⟨0, by rintro _ ⟨S, _, rfl⟩; positivity⟩

/-- **`m₁(ℝ³) ≤ α₁(ℝ³)`** (averaging translates). -/
theorem m1_le_alpha1 : m1 ≤ alpha1 := by
  unfold alpha1
  apply le_csInf alpha1_set_nonempty
  rintro _ ⟨S, hS, rfl⟩
  exact csInf_le m1_set_bddBelow (densityBound_ratio S hS)

/-- **`α₁(ℝ³) = m₁(ℝ³)`**: finite unit-distance graphs in `ℝ³` attain the measurable density. -/
theorem alpha1_eq_m1 : alpha1 = m1 := le_antisymm alpha1_le_m1 m1_le_alpha1

end Indep
end HN3
end
end OAI
