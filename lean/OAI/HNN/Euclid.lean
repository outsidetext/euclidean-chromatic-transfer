import OAI.HNN.Transport
import OAI.Geometry.PlaneColoring.WeakColoring

/-!
# The transfer theorem on `EuclideanSpace ℝ (Fin n)`

Pulling the label fields back along `toX` and sampling one configuration gives a measurable
colouring of `ℝⁿ` whose monochromatic pairs at each forbidden distance are null. Lebesgue
density points of the colour classes then contain no forbidden distance at all.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace
namespace HNN
open EuclideanFiveColor

variable {n : ℕ}

/-! ### Directions -/

def dirE (e0 : EE n) (s : EE n) : EE n := if s = 0 then e0 else ‖s‖⁻¹ • s

lemma dirE_measurable (e0 : EE n) : Measurable (dirE e0) :=
  Measurable.ite (measurableSet_singleton (0 : EE n)) measurable_const
    (measurable_norm.inv.smul measurable_id)

lemma norm_dirE {e0 : EE n} (he : ‖e0‖ = 1) (s : EE n) : ‖dirE e0 s‖ = 1 := by
  unfold dirE
  split_ifs with h
  · exact he
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma dirE_self {e0 s : EE n} (hs : s ≠ 0) : dirE e0 s = ‖s‖⁻¹ • s := by simp [dirE, hs]

lemma dirE_continuousOn (e0 : EE n) : ContinuousOn (dirE e0) {s | s ≠ 0} := by
  have h : ContinuousOn (fun s : EE n => ‖s‖⁻¹ • s) {s | s ≠ 0} :=
    (continuous_norm.continuousOn.inv₀ (fun s hs => norm_ne_zero_iff.mpr hs)).smul
      continuousOn_id
  exact h.congr fun s hs => dirE_self hs

/-! ### Translations in `L²(ℝⁿ)` -/

abbrev L2E (n : ℕ) := Lp ℝ 2 (volume : Measure (EE n))

def shiftE (z : EE n) (f : L2E n) : L2E n :=
  Lp.compMeasurePreserving (fun x => x + z) (measurePreserving_add_right volume z) f

lemma shiftE_ae (z : EE n) (f : L2E n) : shiftE z f =ᵐ[volume] fun x => f (x + z) :=
  Lp.coeFn_compMeasurePreserving f _

lemma shiftE_continuous (f : L2E n) : Continuous (fun z => shiftE z f) := by
  let g : C(EE n, C(EE n, EE n)) :=
    (ContinuousMap.mk (fun p : EE n × EE n => p.2 + p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous
    (fun z => measurePreserving_add_right volume z) (by simp)

lemma product_zero_of_inner_zeroE (f g : L2E n) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (h : ⟪f, g⟫ = 0) : ∀ᵐ x ∂volume, f x * g x = 0 := by
  have hi : Integrable (fun x : EE n => f x * g x) volume := by
    simpa [RCLike.inner_apply, mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f g)
  have hn : ∀ᵐ x ∂volume, 0 ≤ f x * g x := by
    filter_upwards [hf, hg] with x hx hy
    exact mul_nonneg hx hy
  rw [L2.inner_def] at h
  apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
  simpa [RCLike.inner_apply, mul_comm] using h

/-- A function continuous on an open set and almost everywhere zero vanishes on that set. -/
lemma zero_on_open {Φ : EE n → ℝ} {U : Set (EE n)} (hU : IsOpen U) (hΦ : ContinuousOn Φ U)
    (h : Φ =ᵐ[volume] fun _ => 0) : ∀ t ∈ U, Φ t = 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨t0, ht0, hne⟩ := hc
  have hW : IsOpen (U ∩ Φ ⁻¹' {0}ᶜ) := hΦ.isOpen_inter_preimage hU isOpen_compl_singleton
  have hpos := hW.measure_pos (volume : Measure (EE n)) ⟨t0, ht0, hne⟩
  have hzero : (volume : Measure (EE n)) (U ∩ Φ ⁻¹' {0}ᶜ) = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at h
    exact measure_mono_null (fun t ht => ht.2) h
  exact hpos.ne' hzero

lemma params_product_zero (dv : EE n → EE n) (hdc : ContinuousOn dv {s | s ≠ 0})
    (f : L2E n) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (ho : ∀ᵐ t ∂(volume : Measure (EE n)), ∀ᵐ x ∂(volume : Measure (EE n)), f x * f (x + dv t) = 0) :
    ∀ t : EE n, t ≠ 0 → ∀ᵐ x ∂(volume : Measure (EE n)), f x * f (x + dv t) = 0 := by
  have hc : ContinuousOn (fun t : EE n => ⟪f, shiftE (dv t) f⟫) {s | s ≠ 0} :=
    continuous_const.continuousOn.inner ((shiftE_continuous f).comp_continuousOn hdc)
  have hz : (fun t : EE n => ⟪f, shiftE (dv t) f⟫) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [ho] with t ht
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [shiftE_ae (dv t) f, ht] with x hx hh
    simpa [RCLike.inner_apply, mul_comm, hx] using hh
  have he := zero_on_open isOpen_ne hc hz
  intro t ht
  have hg : ∀ᵐ x ∂volume, 0 ≤ shiftE (dv t) f x := by
    filter_upwards [shiftE_ae (dv t) f,
      (measurePreserving_add_right volume (dv t)).quasiMeasurePreserving.ae hf] with x hx hh
    simpa only [hx] using hh
  have h0 := product_zero_of_inner_zeroE f (shiftE (dv t) f) hf hg (he t ht)
  filter_upwards [h0, shiftE_ae (dv t) f] with x hx hh
  simpa only [hh] using hx

/-! ### From almost every direction to every direction -/

section Directions
variable {k : ℕ} (c : EE n → Fin k) (hc : Measurable c)

def tClass (i : Fin k) (N : ℕ) : Set (EE n) := {z | c z = i} ∩ Metric.closedBall 0 N

include hc in
lemma tClass_measurable (i : Fin k) (N : ℕ) : MeasurableSet (tClass c i N) :=
  (measurableSet_eq_fun hc measurable_const).inter measurableSet_closedBall

lemma tClass_finite (i : Fin k) (N : ℕ) : volume (tClass c i N) ≠ ⊤ :=
  ne_top_of_le_ne_top ((isCompact_closedBall (0 : EE n) (N : ℝ)).measure_ne_top)
    (measure_mono Set.inter_subset_right)

def tVector (i : Fin k) (N : ℕ) : L2E n :=
  (memLp_indicator_const 2 (tClass_measurable c hc i N) (1 : ℝ)
    (Or.inr (tClass_finite c i N))).toLp _

lemma tVector_ae (i : Fin k) (N : ℕ) :
    tVector c hc i N =ᵐ[volume] (tClass c i N).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

include hc in
lemma all_directions (dv : EE n → EE n) (hdm : Measurable dv) (hdc : ContinuousOn dv {s | s ≠ 0})
    (hw : ∀ᵐ p ∂(volume : Measure (EE n)).prod (volume : Measure (EE n)), c p.1 ≠ c (p.1 + dv p.2)) :
    ∀ t : EE n, t ≠ 0 → ∀ᵐ z ∂(volume : Measure (EE n)), c z ≠ c (z + dv t) := by
  have ho : ∀ᵐ t ∂(volume : Measure (EE n)), ∀ᵐ z ∂(volume : Measure (EE n)), c z ≠ c (z + dv t) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hw)
    exact (measurableSet_eq_fun (hc.comp measurable_fst)
      (hc.comp (measurable_fst.add (hdm.comp measurable_snd)))).compl
  have hz (i : Fin k) (N : ℕ) : ∀ t : EE n, t ≠ 0 → ∀ᵐ z ∂(volume : Measure (EE n)),
      tVector c hc i N z * tVector c hc i N (z + dv t) = 0 := by
    apply params_product_zero dv hdc
    · filter_upwards [tVector_ae c hc i N] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht, tVector_ae c hc i N,
        (measurePreserving_add_right volume (dv t)).quasiMeasurePreserving.ae
          (tVector_ae c hc i N)] with z hne h1 h2
      rw [h1, h2]
      by_cases h : z ∈ tClass c i N
      · have hh : z + dv t ∉ tClass c i N := fun hh => hne (h.1.trans hh.1.symm)
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro t ht
  have hi : ∀ᵐ z ∂(volume : Measure (EE n)), ∀ i : Fin k, ∀ N : ℕ,
      ((tClass c i N).indicator (fun _ => (1 : ℝ)) z) *
      ((tClass c i N).indicator (fun _ => (1 : ℝ)) (z + dv t)) = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro N
    filter_upwards [hz i N t ht, tVector_ae c hc i N,
      (measurePreserving_add_right volume (dv t)).quasiMeasurePreserving.ae
        (tVector_ae c hc i N)] with z h0 h1 h2
    simpa only [h1, h2] using h0
  filter_upwards [hi] with z hz
  intro he
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ ‖z + dv t‖)
  have h1 : z ∈ tClass c (c z) N := ⟨rfl, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (lt_of_le_of_lt (le_max_left _ _) hN).le⟩
  have h2 : z + dv t ∈ tClass c (c z) N := ⟨he.symm, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (lt_of_le_of_lt (le_max_right _ _) hN).le⟩
  have h0 := hz (c z) N
  simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2] at h0

end Directions

/-! ### Density points -/

def DensityOneE (A : Set (EE n)) (x : EE n) : Prop :=
  Tendsto (fun r : ℝ => volume (A ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
    (𝓝[>] 0) (𝓝 (1 : ENNReal))

lemma densityOneE_disjoint {A B : Set (EE n)} (hB : MeasurableSet B)
    (hd : AEDisjoint volume A B) {x : EE n} (hA : DensityOneE A x) : ¬ DensityOneE B x := by
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

lemma densityOneE_translate {A : Set (EE n)} {x u : EE n} :
    DensityOneE ((fun z : EE n => z + u) ⁻¹' A) x ↔ DensityOneE A (x + u) := by
  have he (r : ℝ) : (fun z : EE n => z + u) ⁻¹' (Metric.closedBall (x + u) r) =
      Metric.closedBall x r := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_add_right]
  have h1 (r : ℝ) : volume (((fun z : EE n => z + u) ⁻¹' A) ∩ Metric.closedBall x r) =
      volume (A ∩ Metric.closedBall (x + u) r) := by
    rw [← he, ← Set.preimage_inter, measure_preimage_add_right]
  have h2 (r : ℝ) : volume (Metric.closedBall x r) = volume (Metric.closedBall (x + u) r) := by
    rw [← he, measure_preimage_add_right]
  simp only [DensityOneE, h1, h2]

lemma density_free {k : ℕ} (c : EE n → Fin k) (hc : Measurable c) (i : Fin k) {x y : EE n}
    (hall : ∀ᵐ z ∂(volume : Measure (EE n)), c z ≠ c (z + (y - x)))
    (hx : DensityOneE {z | c z = i} x) : ¬ DensityOneE {z | c z = i} y := by
  let u := y - x
  have hd : AEDisjoint volume {z | c z = i} ((fun z : EE n => z + u) ⁻¹' {z | c z = i}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [hall] with z hz
    rintro ⟨h1, h2⟩
    exact hz (h1.trans h2.symm)
  have hh := densityOneE_disjoint ((measurableSet_eq_fun hc measurable_const).preimage
    (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOneE_translate] at hh
  simpa only [u, add_sub_cancel] using hh

lemma ae_densityE {k : ℕ} (c : EE n → Fin k) (hc : Measurable c) :
    ∀ᵐ x ∂(volume : Measure (EE n)), DensityOneE {z | c z = c x} x := by
  have hh : ∀ᵐ x ∂(volume : Measure (EE n)), ∀ i : Fin k,
      Tendsto (fun r : ℝ => volume ({z | c z = i} ∩ Metric.closedBall x r) /
        volume (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (({z | c z = i} : Set (EE n)).indicator (1 : EE n → ENNReal) x)) :=
    ae_all_iff.mpr fun i => Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_eq_fun hc measurable_const)
  filter_upwards [hh] with x hx
  simpa only [DensityOneE, Set.indicator_of_mem (show x ∈ {z | c z = c x} from rfl),
    Pi.one_apply] using hx (c x)

/-- Density points turn "almost no monochromatic pair at each forbidden displacement" into a
genuine partition without forbidden distances. -/
theorem partition_of_hall {D : Set ℝ} {k : ℕ} (c : EE n → Fin k) (hc : Measurable c)
    (hall : ∀ y : EE n, ‖y‖ ∈ D → ∀ᵐ z ∂(volume : Measure (EE n)), c z ≠ c (z + y)) :
    ∃ A : Fin k → Set (EE n), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ volume (⋃ i, A i)ᶜ = 0 ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ∉ D := by
  let N : Set (EE n) := {x | ¬ DensityOneE {z | c z = c x} x}
  have hN : volume N = 0 := by
    have := ae_densityE c hc
    rwa [ae_iff] at this
  let N' := toMeasurable volume N
  have hN' : volume N' = 0 := by rw [measure_toMeasurable]; exact hN
  refine ⟨fun i => {x | c x = i} \ N', fun i => ?_, ?_, ?_, ?_⟩
  · exact (measurableSet_eq_fun hc measurable_const).diff (measurableSet_toMeasurable _ _)
  · intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨hxi, -⟩ ⟨hxj, -⟩
    exact hij (hxi.symm.trans hxj)
  · refine measure_mono_null (fun x hx => ?_) hN'
    by_contra hxN
    exact hx (Set.mem_iUnion.mpr ⟨c x, rfl, hxN⟩)
  · rintro i x ⟨hxi, hxN⟩ y ⟨hyi, hyN⟩ hxy
    have hxD : DensityOneE {z | c z = i} x := by
      have : x ∉ N := fun h => hxN (subset_toMeasurable _ _ h)
      simp only [N, Set.mem_ofPred_eq, not_not] at this
      rwa [hxi] at this
    have hyD : DensityOneE {z | c z = i} y := by
      have : y ∉ N := fun h => hyN (subset_toMeasurable _ _ h)
      simp only [N, Set.mem_ofPred_eq, not_not] at this
      rwa [hyi] at this
    have hl : ‖x - y‖ ∈ D := by rwa [← dist_eq_norm]
    exact density_free c hc i (hall (x - y) hl) hyD hxD

/-! ### Sampling -/

section Sample
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ}
  [NeZero k]

lemma sample_ae (H : Fin k → EE n × Ω → ℝ) (hm : ∀ i, Measurable (H i))
    (hp : ∀ x : EE n, ∀ᵐ ω ∂μ, ∑ i, H i (x, ω) = 1) (dv : EE n → EE n) (hdm : Measurable dv)
    (ho : ∀ x s : EE n, ∀ᵐ ω ∂μ, ∀ i, H i (x, ω) * H i (x + dv s, ω) = 0) :
    ∀ᵐ ω ∂μ, ∀ᵐ p ∂(volume : Measure (EE n)).prod (volume : Measure (EE n)),
      positiveSelect H (p.1, ω) ≠ positiveSelect H (p.1 + dv p.2, ω) := by
  let c : EE n × Ω → Fin k := positiveSelect H
  have hc : Measurable c := positiveSelect_measurable H hm
  have ha (p : EE n × EE n) : ∀ᵐ ω ∂μ, c (p.1, ω) ≠ c (p.1 + dv p.2, ω) := by
    filter_upwards [hp p.1, hp (p.1 + dv p.2), ho p.1 p.2] with ω h1 h2 h3
    intro he
    have hpos1 := positiveSelect_pos H (p.1, ω) h1
    have hpos2 := positiveSelect_pos H (p.1 + dv p.2, ω) h2
    change 0 < H (c (p.1, ω)) (p.1, ω) at hpos1
    change 0 < H (c (p.1 + dv p.2, ω)) (p.1 + dv p.2, ω) at hpos2
    rw [← he] at hpos2
    exact (mul_pos hpos1 hpos2).ne' (h3 _)
  have hm1 : Measurable (fun q : (EE n × EE n) × Ω => c (q.1.1, q.2)) :=
    hc.comp ((measurable_fst.fst).prodMk measurable_snd)
  have hm2 : Measurable (fun q : (EE n × EE n) × Ω => c (q.1.1 + dv q.1.2, q.2)) :=
    hc.comp (((measurable_fst.fst).add (hdm.comp measurable_fst.snd)).prodMk measurable_snd)
  exact (Measure.ae_ae_comm (measurableSet_eq_fun hm1 hm2).compl).mp (.of_forall ha)

end Sample

/-! ### Main theorems -/

lemma exists_unit (hn : 0 < n) : ∃ e0 : EE n, ‖e0‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩

/-- Core transfer: a colouring of `ℝ^(2m+r)` avoiding a countable set of algebraic distances
gives a measurable colouring with almost no monochromatic pair at each forbidden displacement. -/
theorem transfer_hall {m r : ℕ} (hm : 0 < m) (hr : r ≤ 1) {D : Set ℝ} (hDc : D.Countable)
    (hD : ∀ d ∈ D, 0 < d ∧ IsAlgebraic ℚ d) {k : ℕ} [NeZero k] (c : EE (m * 2 + r) → Fin k)
    (hc : ∀ x y, dist x y ∈ D → c x ≠ c y) :
    ∃ col : EE (m * 2 + r) → Fin k, Measurable col ∧
      ∀ y : EE (m * 2 + r), ‖y‖ ∈ D → ∀ᵐ z ∂(volume : Measure (EE (m * 2 + r))),
        col z ≠ col (z + y) := by
  let ω : Space m r D k := ⟨fun a => c (ofX (emb a)), fun x y d hd hsq => hc _ _ (by
    have h2 : dist (ofX (emb x)) (ofX (emb y)) ^ 2 = d ^ 2 := by
      rw [dist_eq_norm, norm_ofX_sub, ← emb_sub, usq_emb, hsq]
    rw [sq_eq_sq₀ dist_nonneg (hD d hd).1.le] at h2
    rw [h2]; exact hd)⟩
  have hC := corrZero hm hr hD ω
  obtain ⟨H, hHm, hHp, hHo⟩ := exists_label_field ω hr hC
  let H' : Fin k → EE (m * 2 + r) × Space m r D k → ℝ := fun i p => H i (toX p.1, p.2)
  have hH'm : ∀ i, Measurable (H' i) := fun i =>
    (hHm i).comp ((toX_continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have hH'p : ∀ x, ∀ᵐ η ∂measure ω, ∑ i, H' i (x, η) = 1 := fun x => hHp (toX x)
  obtain ⟨e0, he0⟩ := exists_unit (n := m * 2 + r) (by omega)
  let dv : ℝ → EE (m * 2 + r) → EE (m * 2 + r) := fun d s => d • dirE e0 s
  have hdvm : ∀ d, Measurable (dv d) := fun d => (dirE_measurable e0).const_smul d
  have hgood : ∀ d ∈ D, ∀ᵐ η ∂measure ω, ∀ᵐ p ∂(volume : Measure (EE (m * 2 + r))).prod
      (volume : Measure (EE (m * 2 + r))),
      positiveSelect H' (p.1, η) ≠ positiveSelect H' (p.1 + dv d p.2, η) := by
    intro d hd
    apply sample_ae (measure ω) H' hH'm hH'p (dv d) (hdvm d)
    intro x s
    have hus : usq (toX (dv d s)) = d ^ 2 := by
      rw [usq_toX, norm_smul, norm_dirE he0, mul_one, Real.norm_eq_abs,
        abs_of_pos (hD d hd).1]
    filter_upwards [hHo (toX x) (toX (dv d s)) d hd hus] with η hη i
    simp only [H', toX_add]
    exact hη i
  have hall := (ae_ball_iff hDc).mpr hgood
  obtain ⟨η, hη⟩ := hall.exists
  let col : EE (m * 2 + r) → Fin k := fun y => positiveSelect H' (y, η)
  have hcol : Measurable col :=
    (positiveSelect_measurable H' hH'm).comp (measurable_id.prodMk measurable_const)
  refine ⟨col, hcol, fun y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy; exact (lt_irrefl _ (hD 0 hy).1)
  have hdir := all_directions col hcol (dv ‖y‖) (hdvm _)
    ((dirE_continuousOn e0).const_smul ‖y‖) (hη ‖y‖ hy) y hy0
  have hdy : dv ‖y‖ y = y := by
    simp only [dv, dirE_self hy0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_smul]
  rwa [hdy] at hdir

/-- **Transfer for a countable set of algebraic distances, in every dimension `n ≥ 2`.** -/
theorem euclidean_transfer_set (hn : 2 ≤ n) {D : Set ℝ} (hDc : D.Countable)
    (hD : ∀ d ∈ D, 0 < d ∧ IsAlgebraic ℚ d) {k : ℕ} [NeZero k] (c : EE n → Fin k)
    (hc : ∀ x y, dist x y ∈ D → c x ≠ c y) :
    ∃ A : Fin k → Set (EE n), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ volume (⋃ i, A i)ᶜ = 0 ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ∉ D := by
  obtain ⟨m, r, hr, hm, rfl⟩ : ∃ m r, r ≤ 1 ∧ 0 < m ∧ n = m * 2 + r :=
    ⟨n / 2, n % 2, by omega, by omega, by omega⟩
  obtain ⟨col, hcol, hall⟩ := transfer_hall hm hr hDc hD c hc
  exact partition_of_hall col hcol hall

/-- **Transfer in every dimension `n ≥ 2`.** Any proper `k`-colouring of the unit-distance graph
of `ℝⁿ`, with arbitrary colour classes, yields `k` measurable, pairwise disjoint sets covering
`ℝⁿ` up to a null set, none containing two points at distance one. -/
theorem euclidean_transfer {n : ℕ} (hn : 2 ≤ n) {k : ℕ} [NeZero k]
    (c : EuclideanSpace ℝ (Fin n) → Fin k) (hc : ∀ x y, dist x y = 1 → c x ≠ c y) :
    ∃ A : Fin k → Set (EuclideanSpace ℝ (Fin n)), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧ volume (⋃ i, A i)ᶜ = 0 ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ≠ 1 := by
  obtain ⟨A, h1, h2, h3, h4⟩ := euclidean_transfer_set hn (D := {1}) (countable_singleton 1)
    (fun d hd => by rw [mem_singleton_iff.mp hd]; exact ⟨one_pos, isAlgebraic_one⟩) c
    (fun x y h => hc x y (mem_singleton_iff.mp h))
  exact ⟨A, h1, h2, h3, fun i x hx y hy h => h4 i x hx y hy (mem_singleton_iff.mpr h)⟩

end HNN
end
end OAI
