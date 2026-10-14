import OAI.HN3.IndepSampling
import OAI.HN3.Corollary

/-!
# From an invariant random independent set to a dense measurable unit-distance-free set

Let `L` be a state on `C(ISpace, ℝ)` (a random independent set of the algebraic points) with
`P(a ∈ I) ≥ c` for every `a ∈ V`. The averaged invariant law has `P(0 ∈ I) ≥ c`, and the
one-label transfer gives a measurable field `H(x, η) ∈ [0,1]` with mean `≥ c` at every `x`.
For almost every sample `η`, the Lebesgue density points of `{H(·, η) > 0}` form a measurable
unit-distance-free set. A density bound `δ` for such sets, together with dominated convergence
for the cube averages of `H`, forces `c ≤ max δ 0`.
-/

set_option linter.unusedSectionVars false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace BoundedContinuousFunction
namespace HN3
namespace Indep
open PlaneFiveColor.Spectral EuclideanFiveColor PlaneFiveColor.InvariantMean

/-! ### Evaluation functions and the mean of the indicator -/

/-- The indicator of `a ∈ I` as a continuous function on the space of independent sets. -/
def ev (a : V) : C(ISpace, ℝ) :=
  ⟨fun η => if η.val a = 1 then 1 else 0,
    (continuous_of_discreteTopology (f := fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)).comp
      ((continuous_apply a).comp continuous_subtype_val)⟩

lemma ev_apply (a : V) (η : ISpace) : ev a η = if η.val a = 1 then 1 else 0 := rfl

lemma mean_ge {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (f : G →ᵇ ℝ) {c : ℝ} (h : ∀ x, c ≤ f x) : c ≤ mean f := by
  have h1 := mean_nonneg (f - BoundedContinuousFunction.const G c) (fun x => by simp [h x])
  have h2 : f - BoundedContinuousFunction.const G c =
      f + (-1 : ℝ) • BoundedContinuousFunction.const G c := by
    ext x; simp [sub_eq_add_neg]
  rw [h2, mean_add, mean_smul, mean_const] at h1
  linarith

lemma integral_color_ge (L : State ISpace) {c : ℝ} (hL : ∀ a, c ≤ L.toFun (ev a)) :
    c ≤ ∫ η, (colorValue η).re ∂measure L := by
  have he : (fun η => (colorValue η).re) = fun η => ev 0 η := by
    funext η; simp only [colorValue, ev_apply]; split_ifs <;> simp
  rw [he, integral_measure]
  apply mean_ge
  intro b
  change c ≤ mean (sinner L tC rC (ev 0) b)
  apply mean_ge
  intro a
  change c ≤ L.toFun (((ev 0).comp (rC b)).comp (tC a))
  have hc : ((ev 0).comp (rC b)).comp (tC a) = ev (ofTV a) := by
    ext η
    change ev 0 (rotate (rotMul b) (trans (ofTV a) η)) = ev (ofTV a) η
    simp only [ev_apply, rotate_apply, trans_apply, rmap_zero, zero_add]
  rw [hc]
  exact hL _

/-! ### One class: from almost every direction to every direction -/

section SetDirections
variable (A : Set (ℂ × ℝ)) (hA : MeasurableSet A)

def sClass (n : ℕ) : Set (ℂ × ℝ) := A ∩ Metric.closedBall 0 n

include hA in
lemma sClass_measurable (n : ℕ) : MeasurableSet (sClass A n) := hA.inter measurableSet_closedBall

lemma sClass_finite (n : ℕ) : volume (sClass A n) ≠ ⊤ :=
  ne_top_of_le_ne_top ((isCompact_closedBall (0 : ℂ × ℝ) (n : ℝ)).measure_ne_top)
    (measure_mono Set.inter_subset_right)

def sVector (n : ℕ) : L2P :=
  (memLp_indicator_const 2 (sClass_measurable A hA n) (1 : ℝ)
    (Or.inr (sClass_finite A n))).toLp _

lemma sVector_ae (n : ℕ) :
    sVector A hA n =ᵐ[volume] (sClass A n).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

include hA in
lemma all_directions_set
    (hw : ∀ᵐ p ∂(volume : Measure (ℂ × ℝ)).prod dirMeasure, ¬ (p.1 ∈ A ∧ p.1 + dvec p.2 ∈ A)) :
    ∀ y : ℂ × ℝ, usq y = 1 → ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), ¬ (z ∈ A ∧ z + y ∈ A) := by
  have ho : ∀ᵐ t ∂dirMeasure, ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), ¬ (z ∈ A ∧ z + dvec t ∈ A) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hw)
    exact ((hA.preimage measurable_fst).inter
      (hA.preimage (measurable_fst.add (dvec_continuous.measurable.comp measurable_snd)))).compl
  have hz (n : ℕ) : ∀ t : Dir, ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)),
      sVector A hA n z * sVector A hA n (z + dvec t) = 0 := by
    apply all_parameters_product_zero3 dirMeasure dvec dvec_continuous
    · filter_upwards [sVector_ae A hA n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht, sVector_ae A hA n,
        (measurePreserving_add_right volume (dvec t)).quasiMeasurePreserving.ae
          (sVector_ae A hA n)] with z hne h1 h2
      rw [h1, h2]
      by_cases h : z ∈ sClass A n
      · have hh : z + dvec t ∉ sClass A n := fun hh => hne ⟨h.1, hh.1⟩
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro y hy
  obtain ⟨t, rfl⟩ := dvec_surj y hy
  have hi : ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), ∀ n : ℕ,
      ((sClass A n).indicator (fun _ => (1 : ℝ)) z) *
      ((sClass A n).indicator (fun _ => (1 : ℝ)) (z + dvec t)) = 0 := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz n t, sVector_ae A hA n,
      (measurePreserving_add_right volume (dvec t)).quasiMeasurePreserving.ae
        (sVector_ae A hA n)] with z h0 h1 h2
    simpa only [h1, h2] using h0
  filter_upwards [hi] with z hz
  rintro ⟨h1, h2⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ ‖z + dvec t‖)
  have h1' : z ∈ sClass A n := ⟨h1, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have h2' : z + dvec t ∈ sClass A n := ⟨h2, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz n
  simp [Set.indicator_of_mem h1', Set.indicator_of_mem h2'] at h0

end SetDirections

lemma density_unit_free_set {A : Set (ℂ × ℝ)} (hA : MeasurableSet A)
    (hall : ∀ y : ℂ × ℝ, usq y = 1 → ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), ¬ (z ∈ A ∧ z + y ∈ A))
    {x y : ℂ × ℝ} (hxy : usq (y - x) = 1) (hx : DensityOne3 A x) : ¬ DensityOne3 A y := by
  let u := y - x
  have hd : AEDisjoint volume A ((fun z : ℂ × ℝ => z + u) ⁻¹' A) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hall u hxy] with z hz
    rintro ⟨h1, h2⟩
    exact hz ⟨h1, h2⟩
  have hh := densityOne3_disjoint (hA.preimage (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOne3_translate] at hh
  simpa only [u, add_sub_cancel] using hh

/-- Removing the non-density points of `A` leaves a measurable unit-distance-free set of the
same measure in every cube. -/
lemma unit_free_core {A : Set (ℂ × ℝ)} (hA : MeasurableSet A)
    (hall : ∀ y : ℂ × ℝ, usq y = 1 → ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), ¬ (z ∈ A ∧ z + y ∈ A)) :
    ∃ S : Set (ℂ × ℝ), MeasurableSet S ∧ (∀ x ∈ S, ∀ y ∈ S, usq (x - y) ≠ 1) ∧
      ∀ T, volume (A ∩ cube T) ≤ volume (S ∩ cube T) := by
  let N : Set (ℂ × ℝ) := {x | x ∈ A ∧ ¬ DensityOne3 A x}
  have hN : volume N = 0 := by
    have h := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet
      (volume : Measure (ℂ × ℝ)) hA
    rw [ae_iff] at h
    refine measure_mono_null (fun x hx => ?_) h
    simp only [Set.mem_ofPred_eq]
    intro ht
    apply hx.2
    simpa only [DensityOne3, Set.indicator_of_mem hx.1, Pi.one_apply] using ht
  let N' := toMeasurable volume N
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  refine ⟨A \ N', hA.diff (measurableSet_toMeasurable _ _), ?_, ?_⟩
  · rintro x ⟨hxA, hxN⟩ y ⟨hyA, hyN⟩ hxy
    have hxD : DensityOne3 A x := by
      by_contra h; exact hxN (subset_toMeasurable _ _ ⟨hxA, h⟩)
    have hyD : DensityOne3 A y := by
      by_contra h; exact hyN (subset_toMeasurable _ _ ⟨hyA, h⟩)
    exact density_unit_free_set hA hall hxy hyD hxD
  · intro T
    calc volume (A ∩ cube T) ≤ volume ((A \ N') ∩ cube T ∪ N') := measure_mono (fun x hx => by
          by_cases h : x ∈ N'
          · exact Or.inr h
          · exact Or.inl ⟨⟨hx.1, h⟩, hx.2⟩)
      _ ≤ volume ((A \ N') ∩ cube T) + volume N' := measure_union_le _ _
      _ = volume ((A \ N') ∩ cube T) := by rw [hN', add_zero]

/-! ### Cube averages -/

instance cube_restrict_finite (T : ℝ) : IsFiniteMeasure (volume.restrict (cube T)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (cube_finite T).lt_top⟩

lemma setInt_le_cube (g : ℂ × ℝ → ℝ) (hg : Measurable g) (h1 : ∀ x, g x ≤ 1)
    (h0 : ∀ x, 0 ≤ g x) (T : ℝ) :
    ∫ x in cube T, g x ≤ (volume (cube T)).toReal := by
  have hi : Integrable g (volume.restrict (cube T)) :=
    Integrable.of_bound hg.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)
  calc ∫ x in cube T, g x ≤ ∫ _x in cube T, (1 : ℝ) :=
        integral_mono hi (integrable_const _) h1
    _ = (volume (cube T)).toReal := by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

/-- **Density transfer.** If a state on the independent sets of `V` covers every vertex with
probability at least `c`, then `c` is at most any density bound for measurable
unit-distance-free subsets of `ℝ³`. -/
theorem density_le {δ : ℝ} (hδ : DensityBound δ) (L : State ISpace) {c : ℝ}
    (hL : ∀ a, c ≤ L.toFun (ev a)) : c ≤ max δ 0 := by
  obtain ⟨H, hm, h01, hmean, horth⟩ := exists_label_field L
  have hcp : c ≤ ∫ η, (colorValue η).re ∂measure L := integral_color_ge L hL
  set p := ∫ η, (colorValue η).re ∂measure L with hp
  have hHx : ∀ η : ISpace, Measurable fun x : ℂ × ℝ => H (x, η) :=
    fun η => hm.comp (measurable_id.prodMk measurable_const)
  -- a.e. sample: unit pairs are null in almost every direction
  have hA : ∀ᵐ η ∂measure L, ∀ᵐ q ∂(volume : Measure (ℂ × ℝ)).prod dirMeasure,
      H (q.1, η) * H (q.1 + dvec q.2, η) = 0 := by
    have hmeas : MeasurableSet {z : ((ℂ × ℝ) × Dir) × ISpace |
        H (z.1.1, z.2) * H (z.1.1 + dvec z.1.2, z.2) = 0} := by
      apply measurableSet_eq_fun _ measurable_const
      exact (hm.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hm.comp ((measurable_fst.fst.add
          (dvec_continuous.measurable.comp measurable_fst.snd)).prodMk measurable_snd))
    exact (Measure.ae_ae_comm hmeas).mp
      (.of_forall fun q => horth q.1 (dvec q.2) (dvec_unit q.2))
  -- normalized cube averages
  let Y : ℕ → ISpace → ℝ := fun n η =>
    (∫ x in cube (n : ℝ), H (x, η)) / (volume (cube (n : ℝ))).toReal
  have hY0 : ∀ n η, 0 ≤ Y n η := fun n η =>
    div_nonneg (setIntegral_nonneg (cube_measurable _) fun x _ => (h01 _).1) ENNReal.toReal_nonneg
  have hY1 : ∀ n η, Y n η ≤ 1 := by
    intro n η
    apply div_le_one_of_le₀ _ ENNReal.toReal_nonneg
    exact setInt_le_cube _ (hHx η) (fun x => (h01 _).2) (fun x => (h01 _).1) _
  have hYm : ∀ n, Measurable (Y n) := fun n =>
    (hm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (cube (n : ℝ)))).measurable.div_const _
  have hYi : ∀ n, Integrable (Y n) (measure L) := fun n =>
    Integrable.of_bound (hYm n).aestronglyMeasurable 1 (ae_of_all _ fun η => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hY0 n η)]; exact hY1 n η)
  -- the mean of every cube average is `p`
  have hYint : ∀ n : ℕ, 0 < n → ∫ η, Y n η ∂measure L = p := by
    intro n hn
    have hpos : 0 < (volume (cube (n : ℝ))).toReal :=
      ENNReal.toReal_pos (cube_pos (by exact_mod_cast hn)) (cube_finite _)
    have hint : Integrable (Function.uncurry fun (x : ℂ × ℝ) (η : ISpace) => H (x, η))
        ((volume.restrict (cube (n : ℝ))).prod (measure L)) :=
      Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun q => by
        change ‖H (q.1, q.2)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]; exact (h01 _).2)
    have hswap := integral_integral_swap hint
    simp only [Y]
    rw [integral_div, ← hswap]
    simp_rw [hmean]
    rw [setIntegral_const, smul_eq_mul, measureReal_def]
    field_simp
  -- for a.e. sample, the density bound controls the cube averages eventually
  have hev : ∀ ε' > 0, ∀ᵐ η ∂measure L, ∀ᶠ n in atTop, Y n η ≤ max (δ + ε') 0 := by
    intro ε' hε'
    filter_upwards [hA] with η hη
    let A : Set (ℂ × ℝ) := {x | 0 < H (x, η)}
    have hAm : MeasurableSet A := measurableSet_lt measurable_const (hHx η)
    have hw : ∀ᵐ q ∂(volume : Measure (ℂ × ℝ)).prod dirMeasure,
        ¬ (q.1 ∈ A ∧ q.1 + dvec q.2 ∈ A) := by
      filter_upwards [hη] with q hq
      rintro ⟨h1, h2⟩
      exact (mul_pos h1 h2).ne' hq
    obtain ⟨S, hSm, hSu, hSA⟩ := unit_free_core hAm (all_directions_set A hAm hw)
    have hb := hδ S hSm hSu ε' hε'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hb, eventually_gt_atTop 0] with n hn hn0
    have hpos : 0 < (volume (cube (n : ℝ))).toReal :=
      ENNReal.toReal_pos (cube_pos (by exact_mod_cast hn0)) (cube_finite _)
    have h1 : ∫ x in cube (n : ℝ), H (x, η) ≤ (volume (A ∩ cube (n : ℝ))).toReal := by
      have hle : ∀ x, H (x, η) ≤ A.indicator 1 x := by
        intro x
        by_cases hx : x ∈ A
        · rw [Set.indicator_of_mem hx]; exact (h01 _).2
        · rw [Set.indicator_of_notMem hx]
          exact le_of_not_gt hx
      have hi : Integrable (fun x => H (x, η)) (volume.restrict (cube (n : ℝ))) :=
        Integrable.of_bound (hHx η).aestronglyMeasurable 1 (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h01 _).1]; exact (h01 _).2)
      have hi2 : Integrable (A.indicator (1 : ℂ × ℝ → ℝ)) (volume.restrict (cube (n : ℝ))) :=
        (integrable_const (1 : ℝ)).indicator hAm
      calc ∫ x in cube (n : ℝ), H (x, η) ≤ ∫ x in cube (n : ℝ), A.indicator 1 x :=
            integral_mono hi hi2 hle
        _ = (volume (A ∩ cube (n : ℝ))).toReal := by
            rw [integral_indicator_one hAm, measureReal_def, Measure.restrict_apply hAm]
    have h2 : (volume (A ∩ cube (n : ℝ))).toReal ≤
        max (δ + ε') 0 * (volume (cube (n : ℝ))).toReal := by
      have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (cube_finite _))
        ((hSA _).trans hn)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal'] at h3
    change (∫ x in cube (n : ℝ), H (x, η)) / (volume (cube (n : ℝ))).toReal ≤ _
    rw [div_le_iff₀ hpos]
    linarith
  -- dominated convergence
  by_contra hlt
  push Not at hlt
  set ε' := (c - max δ 0) / 2 with hε'def
  have hε' : 0 < ε' := div_pos (sub_pos.mpr hlt) two_pos
  set m := max (δ + ε') 0 with hmdef
  have hm0 : 0 ≤ m := le_max_right _ _
  have hmc : m < c := by
    apply max_lt
    · have := le_max_left δ 0
      linarith
    · linarith [le_max_right δ 0]
  let W : ℕ → ISpace → ℝ := fun n η => max (Y n η) m
  have hlim : Tendsto (fun n => ∫ η, W n η ∂measure L) atTop (𝓝 (∫ _η, m ∂measure L)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => max 1 m)
    · intro n
      exact ((hYm n).max measurable_const).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      refine ae_of_all _ fun η => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_of_le_right hm0)]
      exact max_le_max (hY1 n η) le_rfl
    · filter_upwards [hev ε' hε'] with η hη
      apply tendsto_const_nhds.congr'
      filter_upwards [hη] with n hn
      exact (max_eq_right hn).symm
  have hle : ∀ᶠ n in atTop, p ≤ ∫ η, W n η ∂measure L := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← hYint n hn]
    exact integral_mono (hYi n) (Integrable.of_bound ((hYm n).max measurable_const).aestronglyMeasurable
      (max 1 m) (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_of_le_right hm0)]
        exact max_le_max (hY1 n η) le_rfl)) (fun η => le_max_left _ _)
  have hpm : p ≤ ∫ _η, m ∂measure L := ge_of_tendsto hlim hle
  rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    one_mul] at hpm
  linarith

end Indep
end HN3
end
end OAI
