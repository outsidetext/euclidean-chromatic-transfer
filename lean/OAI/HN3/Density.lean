import OAI.HN3.Sampling
import OAI.Geometry.PlaneColoring.WeakColoring

/-!
# Density points and the main three-dimensional theorem

A sampled coloring of `ℂ × ℝ` has, for every Euclidean unit vector `y`, almost no monochromatic
pairs `(z, z + y)`. Lebesgue density points of a color class therefore contain no unit pair.
Removing a null set leaves a measurable partition into unit-distance-free classes.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace
namespace HN3
open EuclideanFiveColor

instance volume_addRight : (volume : Measure (ℂ × ℝ)).IsAddRightInvariant := by
  change (Measure.prod volume volume).IsAddRightInvariant
  infer_instance

instance volume_addHaar : (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change (Measure.prod volume volume).IsAddHaarMeasure
  infer_instance

/-- Squared Euclidean norm on `ℂ × ℝ ≅ ℝ³`. -/
def usq (y : ℂ × ℝ) : ℝ := ‖y.1‖ ^ 2 + y.2 ^ 2

/-! ### Direction parameters -/

abbrev Dir := Angles × ℝ
def dirMeasure : Measure Dir := angularMeasure.prod volume
instance : SFinite dirMeasure := by unfold dirMeasure; infer_instance
instance : dirMeasure.IsOpenPosMeasure := by unfold dirMeasure; infer_instance

def clampU (τ : ℝ) : ℝ := max (-1) (min 1 τ)

lemma clampU_continuous : Continuous clampU := by unfold clampU; fun_prop

lemma clampU_sq_le (τ : ℝ) : clampU τ ^ 2 ≤ 1 := by
  have h1 : -1 ≤ clampU τ := le_max_left _ _
  have h2 : clampU τ ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  nlinarith

lemma clampU_of_mem {τ : ℝ} (h1 : -1 ≤ τ) (h2 : τ ≤ 1) : clampU τ = τ := by
  simp [clampU, min_eq_right h2, max_eq_right h1]

def dvec (p : Dir) : ℂ × ℝ :=
  (((Real.sqrt (1 - clampU p.2 ^ 2) : ℝ) : ℂ) * direction p.1, clampU p.2)

lemma dvec_continuous : Continuous dvec := by
  unfold dvec
  have hc := clampU_continuous
  refine Continuous.prodMk ?_ (hc.comp continuous_snd)
  exact (Complex.continuous_ofReal.comp ((continuous_const.sub
    ((hc.comp continuous_snd).pow 2)).sqrt)).mul (direction_continuous.comp continuous_fst)

lemma dvec_unit (p : Dir) : usq (dvec p) = 1 := by
  simp only [usq, dvec]
  rw [norm_mul, direction_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by linarith [clampU_sq_le p.2])]
  ring

lemma dvec_surj (y : ℂ × ℝ) (hy : usq y = 1) : ∃ p, dvec p = y := by
  unfold usq at hy
  have h2 : y.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖y.1‖]
  have hm1 : -1 ≤ y.2 := by nlinarith [sq_nonneg (y.2 + 1)]
  have hm2 : y.2 ≤ 1 := by nlinarith [sq_nonneg (y.2 - 1)]
  have hcl := clampU_of_mem hm1 hm2
  have hr : Real.sqrt (1 - y.2 ^ 2) = ‖y.1‖ := by
    rw [show 1 - y.2 ^ 2 = ‖y.1‖ ^ 2 by linarith, Real.sqrt_sq (norm_nonneg _)]
  by_cases h0 : y.1 = 0
  · refine ⟨(0, y.2), ?_⟩
    simp only [dvec, hcl, hr, h0, norm_zero, Complex.ofReal_zero, zero_mul]
    exact Prod.ext h0.symm rfl
  · have hn : ‖y.1‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    obtain ⟨θ, hθ⟩ := direction_exists (u := y.1 / (‖y.1‖ : ℂ)) (by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self hn])
    refine ⟨(θ, y.2), ?_⟩
    simp only [dvec, hcl, hr, hθ]
    refine Prod.ext ?_ rfl
    change (‖y.1‖ : ℂ) * (y.1 / (‖y.1‖ : ℂ)) = y.1
    field_simp [Complex.ofReal_ne_zero.mpr hn]

/-! ### Translations in `L²(ℂ × ℝ)` -/

abbrev L2P := Lp ℝ 2 (volume : Measure (ℂ × ℝ))

def shift3 (z : ℂ × ℝ) (f : L2P) : L2P :=
  Lp.compMeasurePreserving (fun x => x + z) (measurePreserving_add_right volume z) f

lemma shift3_ae (z : ℂ × ℝ) (f : L2P) : shift3 z f =ᵐ[volume] fun x => f (x + z) :=
  Lp.coeFn_compMeasurePreserving f _

lemma shift3_continuous (f : L2P) : Continuous (fun z => shift3 z f) := by
  let g : C(ℂ × ℝ, C(ℂ × ℝ, ℂ × ℝ)) :=
    (ContinuousMap.mk (fun p : (ℂ × ℝ) × (ℂ × ℝ) => p.2 + p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous
    (fun z => measurePreserving_add_right volume z) (by simp)

lemma product_zero_of_inner_zero3 (f g : L2P) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (h : ⟪f, g⟫ = 0) : ∀ᵐ x ∂volume, f x * g x = 0 := by
  have hi : Integrable (fun x : ℂ × ℝ => f x * g x) volume := by
    simpa [RCLike.inner_apply, mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f g)
  have hn : ∀ᵐ x ∂volume, 0 ≤ f x * g x := by
    filter_upwards [hf, hg] with x hx hy
    exact mul_nonneg hx hy
  rw [L2.inner_def] at h
  apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
  simpa [RCLike.inner_apply, mul_comm] using h

lemma all_parameters_product_zero3 {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    (μ : Measure T) [μ.IsOpenPosMeasure] (d : T → ℂ × ℝ) (hd : Continuous d)
    (f : L2P) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (ho : ∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure (ℂ × ℝ)), f x * f (x + d t) = 0) :
    ∀ t : T, ∀ᵐ x ∂(volume : Measure (ℂ × ℝ)), f x * f (x + d t) = 0 := by
  have hc : Continuous (fun t : T => ⟪f, shift3 (d t) f⟫) :=
    continuous_const.inner ((shift3_continuous f).comp hd)
  have hz : (fun t : T => ⟪f, shift3 (d t) f⟫) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ho] with t ht
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [shift3_ae (d t) f, ht] with x hx hh
    simpa [RCLike.inner_apply, mul_comm, hx] using hh
  have he := (hc.ae_eq_iff_eq μ continuous_const).mp hz
  intro t
  have hg : ∀ᵐ x ∂volume, 0 ≤ shift3 (d t) f x := by
    filter_upwards [shift3_ae (d t) f,
      (measurePreserving_add_right volume (d t)).quasiMeasurePreserving.ae hf] with x hx hh
    simpa only [hx] using hh
  have h0 := product_zero_of_inner_zero3 f (shift3 (d t) f) hf hg (congrFun he t)
  filter_upwards [h0, shift3_ae (d t) f] with x hx hh
  simpa only [hh] using hx

/-! ### From almost every direction to every direction -/

section Directions
variable {k : ℕ} (c : ℂ × ℝ → Fin k) (hc : Measurable c)

def tClass (i : Fin k) (n : ℕ) : Set (ℂ × ℝ) := {z | c z = i} ∩ Metric.closedBall 0 n

include hc in
lemma tClass_measurable (i : Fin k) (n : ℕ) : MeasurableSet (tClass c i n) :=
  (measurableSet_eq_fun hc measurable_const).inter measurableSet_closedBall

lemma tClass_finite (i : Fin k) (n : ℕ) : volume (tClass c i n) ≠ ⊤ :=
  ne_top_of_le_ne_top ((isCompact_closedBall (0 : ℂ × ℝ) (n : ℝ)).measure_ne_top)
    (measure_mono Set.inter_subset_right)

def tVector (i : Fin k) (n : ℕ) : L2P :=
  (memLp_indicator_const 2 (tClass_measurable c hc i n) (1 : ℝ)
    (Or.inr (tClass_finite c i n))).toLp _

lemma tVector_ae (i : Fin k) (n : ℕ) :
    tVector c hc i n =ᵐ[volume] (tClass c i n).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

include hc in
lemma all_directions
    (hw : ∀ᵐ p ∂(volume : Measure (ℂ × ℝ)).prod dirMeasure, c p.1 ≠ c (p.1 + dvec p.2)) :
    ∀ y : ℂ × ℝ, usq y = 1 → ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), c z ≠ c (z + y) := by
  have ho : ∀ᵐ t ∂dirMeasure, ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), c z ≠ c (z + dvec t) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hw)
    exact (measurableSet_eq_fun (hc.comp measurable_fst)
      (hc.comp (measurable_fst.add (dvec_continuous.measurable.comp measurable_snd)))).compl
  have hz (i : Fin k) (n : ℕ) : ∀ t : Dir, ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)),
      tVector c hc i n z * tVector c hc i n (z + dvec t) = 0 := by
    apply all_parameters_product_zero3 dirMeasure dvec dvec_continuous
    · filter_upwards [tVector_ae c hc i n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht, tVector_ae c hc i n,
        (measurePreserving_add_right volume (dvec t)).quasiMeasurePreserving.ae
          (tVector_ae c hc i n)] with z hne h1 h2
      rw [h1, h2]
      by_cases h : z ∈ tClass c i n
      · have hh : z + dvec t ∉ tClass c i n := fun hh => hne (h.1.trans hh.1.symm)
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro y hy
  obtain ⟨t, rfl⟩ := dvec_surj y hy
  have hi : ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), ∀ i : Fin k, ∀ n : ℕ,
      ((tClass c i n).indicator (fun _ => (1 : ℝ)) z) *
      ((tClass c i n).indicator (fun _ => (1 : ℝ)) (z + dvec t)) = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz i n t, tVector_ae c hc i n,
      (measurePreserving_add_right volume (dvec t)).quasiMeasurePreserving.ae
        (tVector_ae c hc i n)] with z h0 h1 h2
    simpa only [h1, h2] using h0
  filter_upwards [hi] with z hz
  intro he
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖z‖ ‖z + dvec t‖)
  have h1 : z ∈ tClass c (c z) n := ⟨rfl, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have h2 : z + dvec t ∈ tClass c (c z) n := ⟨he.symm, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz (c z) n
  simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2] at h0

end Directions

/-! ### Density points -/

def DensityOne3 (A : Set (ℂ × ℝ)) (x : ℂ × ℝ) : Prop :=
  Tendsto (fun r : ℝ => volume (A ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
    (𝓝[>] 0) (𝓝 (1 : ENNReal))

lemma densityOne3_disjoint {A B : Set (ℂ × ℝ)} (hB : MeasurableSet B)
    (hd : AEDisjoint volume A B) {x : ℂ × ℝ} (hA : DensityOne3 A x) : ¬ DensityOne3 B x := by
  intro hb
  have hh := hA.add hb
  have hle : (1 : ENNReal) + 1 ≤ 1 := le_of_tendsto hh (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← ENNReal.add_div, ← measure_union₀ (hB.inter measurableSet_closedBall).nullMeasurableSet
      (hd.mono inter_subset_left inter_subset_left)]
    apply (ENNReal.div_le_iff (Metric.measure_closedBall_pos volume x hr).ne'
      ((isCompact_closedBall x r).measure_ne_top)).mpr
    simpa only [one_mul] using measure_mono (union_subset inter_subset_right inter_subset_right))
  norm_num at hle

lemma densityOne3_translate {A : Set (ℂ × ℝ)} {x u : ℂ × ℝ} :
    DensityOne3 ((fun z : ℂ × ℝ => z + u) ⁻¹' A) x ↔ DensityOne3 A (x + u) := by
  have he (r : ℝ) : (fun z : ℂ × ℝ => z + u) ⁻¹' (Metric.closedBall (x + u) r) =
      Metric.closedBall x r := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_add_right]
  have h1 (r : ℝ) : volume (((fun z : ℂ × ℝ => z + u) ⁻¹' A) ∩ Metric.closedBall x r) =
      volume (A ∩ Metric.closedBall (x + u) r) := by
    rw [← he, ← Set.preimage_inter, measure_preimage_add_right]
  have h2 (r : ℝ) : volume (Metric.closedBall x r) = volume (Metric.closedBall (x + u) r) := by
    rw [← he, measure_preimage_add_right]
  simp only [DensityOne3, h1, h2]

lemma density_unit_free {k : ℕ} (c : ℂ × ℝ → Fin k) (hc : Measurable c)
    (hall : ∀ y : ℂ × ℝ, usq y = 1 → ∀ᵐ z ∂(volume : Measure (ℂ × ℝ)), c z ≠ c (z + y))
    (i : Fin k) {x y : ℂ × ℝ} (hxy : usq (y - x) = 1) (hx : DensityOne3 {z | c z = i} x) :
    ¬ DensityOne3 {z | c z = i} y := by
  let u := y - x
  have hd : AEDisjoint volume {z | c z = i} ((fun z : ℂ × ℝ => z + u) ⁻¹' {z | c z = i}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hall u hxy] with z hz
    rintro ⟨h1, h2⟩
    exact hz (h1.trans h2.symm)
  have hh := densityOne3_disjoint ((measurableSet_eq_fun hc measurable_const).preimage
    (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOne3_translate] at hh
  simpa only [u, add_sub_cancel] using hh

lemma ae_density_actual3 {k : ℕ} (c : ℂ × ℝ → Fin k) (hc : Measurable c) :
    ∀ᵐ x ∂(volume : Measure (ℂ × ℝ)), DensityOne3 {z | c z = c x} x := by
  have hh : ∀ᵐ x ∂(volume : Measure (ℂ × ℝ)), ∀ i : Fin k,
      Tendsto (fun r : ℝ => volume ({z | c z = i} ∩ Metric.closedBall x r) /
        volume (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (({z | c z = i} : Set (ℂ × ℝ)).indicator (1 : ℂ × ℝ → ENNReal) x)) :=
    ae_all_iff.mpr fun i => Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_eq_fun hc measurable_const)
  filter_upwards [hh] with x hx
  simpa only [DensityOne3, Set.indicator_of_mem (show x ∈ {z | c z = c x} from rfl),
    Pi.one_apply] using hx (c x)

/-! ### Main theorem -/

lemma usq_emb_sub (x y : V) : usq (emb x - emb y) = sq (x - y) := by
  simp [usq, sq, emb]

/-- **Transfer in three dimensions.** Any proper `k`-coloring of `ℝ³ = ℂ × ℝ`, with arbitrary
color classes, yields a partition of a conull set into `k` measurable classes, none of which
contains two points at Euclidean distance one. -/
theorem proper_partition3 {k : ℕ} [NeZero k] (c : ℂ × ℝ → Fin k)
    (hc : ∀ x y : ℂ × ℝ, usq (x - y) = 1 → c x ≠ c y) :
    ∃ A : Fin k → Set (ℂ × ℝ), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      volume (⋃ i, A i)ᶜ = 0 ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, usq (x - y) ≠ 1 := by
  let ω : Space k := ⟨fun a => c (emb a), fun x y h => hc _ _ (by rwa [usq_emb_sub])⟩
  obtain ⟨H, hm, hp, ho⟩ := exists_label_field k ω
  obtain ⟨d, hd, hw⟩ := sample_field (measure k ω) dirMeasure dvec dvec_continuous.measurable
    H hm hp (fun x s => ho x (dvec s) (dvec_unit s))
  have hall := all_directions d hd hw
  let N : Set (ℂ × ℝ) := {x | ¬ DensityOne3 {z | d z = d x} x}
  have hN : volume N = 0 := by
    have := ae_density_actual3 d hd
    rwa [ae_iff] at this
  let N' := toMeasurable volume N
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  refine ⟨fun i => {x | d x = i} \ N', fun i => ?_, ?_, ?_, ?_⟩
  · exact (measurableSet_eq_fun hd measurable_const).diff (measurableSet_toMeasurable _ _)
  · intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
    exact hij (hxi.symm.trans hxj)
  · refine measure_mono_null (fun x hx => ?_) hN'
    by_contra hxN
    exact hx (Set.mem_iUnion.mpr ⟨d x, rfl, hxN⟩)
  · rintro i x ⟨hxi, hxN⟩ y ⟨hyi, hyN⟩ hxy
    have hxD : DensityOne3 {z | d z = i} x := by
      have : x ∉ N := fun h => hxN (subset_toMeasurable _ _ h)
      simp only [N, Set.mem_setOf_eq, not_not] at this
      rwa [hxi] at this
    have hyD : DensityOne3 {z | d z = i} y := by
      have : y ∉ N := fun h => hyN (subset_toMeasurable _ _ h)
      simp only [N, Set.mem_setOf_eq, not_not] at this
      rwa [hyi] at this
    exact density_unit_free d hd hall i hxy hyD hxD

end HN3
end
end OAI
