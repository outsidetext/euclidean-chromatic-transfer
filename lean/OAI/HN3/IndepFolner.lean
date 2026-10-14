import OAI.HN3.IndepDensity

/-!
# Finite unit-distance graphs in `ℝ³` attain the measurable density

If every finite set of points of `ℝ³` contains an independent subset of more than a `c`-fraction
of its points, then there is a random independent set of the algebraic points `V` covering every
vertex with probability at least `c`:

* a finite window `W ⊆ V` lies in a lattice `⊕ ℤ e_i` with `ℤ`-independent `e_i`
  (the `ℤ`-span of `W` is free);
* the boxes `{∑ n_i e_i : 0 ≤ n_i < N}` are Følner sets, so a uniformly random translate of a
  large independent subset of a box covers each vertex of `W` with probability `≥ c - o(1)`;
* an ultrafilter limit of these finite averages is a state `L` on `C(ISpace, ℝ)` with
  `L (ev a) ≥ c` for all `a`.

`density_le` then gives `c ≤ δ` for any density bound `δ`: finite unit-distance graphs in `ℝ³`
have independence ratios arbitrarily close to `m₁(ℝ³)` (from above).
-/

set_option linter.unusedSectionVars false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal
namespace HN3
namespace Indep
open PlaneFiveColor.InvariantMean

/-! ### Lattices through finite windows -/

lemma exists_lattice (W : Finset V) : ∃ (s : ℕ) (e : Fin s → V),
    Function.Injective (fun n : Fin s → ℤ => ∑ i, n i • e i) ∧
    ∀ w ∈ W, ∃ k : Fin s → ℤ, w = ∑ i, k i • e i := by
  let M := Submodule.span ℤ (W : Set V)
  obtain ⟨s, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  refine ⟨s, fun i => (b i : V), ?_, ?_⟩
  · intro n m h
    have h' : b.equivFun.symm n = b.equivFun.symm m := by
      apply Subtype.ext
      simp only [Module.Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul]
      exact h
    exact b.equivFun.symm.injective h'
  · intro w hw
    refine ⟨b.repr ⟨w, Submodule.subset_span hw⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨w, Submodule.subset_span hw⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm

/-! ### Boxes and the Følner estimate -/

section Box
variable {s : ℕ} (e : Fin s → V)

def phi (n : Fin s → ℕ) : V := ∑ i, ((n i : ℤ)) • e i

def box (N : ℕ) : Finset V := (Fintype.piFinset fun _ : Fin s => range N).image (phi e)

lemma box_card (he : Function.Injective (fun n : Fin s → ℤ => ∑ i, n i • e i)) (N : ℕ) :
    (box e N).card = N ^ s := by
  rw [box, card_image_of_injective, Fintype.card_piFinset]
  · simp
  · intro n m h
    have h2 := he (a₁ := fun i => (n i : ℤ)) (a₂ := fun i => (m i : ℤ)) h
    funext i
    exact_mod_cast congrFun h2 i

lemma bad_card_1d (N : ℕ) (k : ℤ) :
    ((range N).filter (fun x : ℕ => ¬ ((0 : ℤ) ≤ x + k ∧ (x : ℤ) + k < N))).card ≤
      2 * k.natAbs := by
  calc _ ≤ (range k.natAbs ∪ Ico (N - k.natAbs) N).card := by
        apply card_le_card
        intro x hx
        simp only [mem_filter, mem_range] at hx
        simp only [mem_union, mem_range, mem_Ico]
        omega
    _ ≤ (range k.natAbs).card + (Ico (N - k.natAbs) N).card := card_union_le _ _
    _ ≤ 2 * k.natAbs := by simp only [card_range, Nat.card_Ico]; omega

lemma bad_card (N : ℕ) (k : Fin s → ℤ) :
    ((Fintype.piFinset fun _ : Fin s => range N).filter
      (fun n => ∃ i, ¬ ((0 : ℤ) ≤ n i + k i ∧ (n i : ℤ) + k i < N))).card ≤
      ∑ i, 2 * (k i).natAbs * N ^ (s - 1) := by
  classical
  calc _ ≤ (univ.biUnion fun i => ((range N).filter
            (fun x : ℕ => ¬ ((0 : ℤ) ≤ x + k i ∧ (x : ℤ) + k i < N))).biUnion
            fun x => (Fintype.piFinset fun _ : Fin s => range N).filter (fun n => n i = x)).card := by
        apply card_le_card
        intro n hn
        simp only [mem_filter] at hn
        obtain ⟨hnP, i, hi⟩ := hn
        simp only [mem_biUnion, mem_univ, true_and, mem_filter]
        exact ⟨i, n i, ⟨Fintype.mem_piFinset.mp hnP i, hi⟩, hnP, rfl⟩
    _ ≤ ∑ i, (((range N).filter
            (fun x : ℕ => ¬ ((0 : ℤ) ≤ x + k i ∧ (x : ℤ) + k i < N))).biUnion
            fun x => (Fintype.piFinset fun _ : Fin s => range N).filter (fun n => n i = x)).card :=
        card_biUnion_le
    _ ≤ ∑ i, 2 * (k i).natAbs * N ^ (s - 1) := by
        apply sum_le_sum
        intro i _
        calc _ ≤ ∑ x ∈ (range N).filter
                (fun x : ℕ => ¬ ((0 : ℤ) ≤ x + k i ∧ (x : ℤ) + k i < N)),
                ((Fintype.piFinset fun _ : Fin s => range N).filter (fun n => n i = x)).card :=
              card_biUnion_le
          _ = ∑ x ∈ (range N).filter
                (fun x : ℕ => ¬ ((0 : ℤ) ≤ x + k i ∧ (x : ℤ) + k i < N)), N ^ (s - 1) := by
              apply sum_congr rfl
              intro x hx
              rw [Fintype.card_filter_piFinset_const_eq_of_mem _ _ (mem_filter.mp hx).1,
                card_range, Fintype.card_fin]
          _ ≤ _ := by
              rw [sum_const, smul_eq_mul]
              exact Nat.mul_le_mul_right _ (bad_card_1d N (k i))

lemma box_shift_bad (N : ℕ) (k : Fin s → ℤ) :
    ((box e N).filter (fun g => g + ∑ i, k i • e i ∉ box e N)).card ≤
      ∑ i, 2 * (k i).natAbs * N ^ (s - 1) := by
  classical
  refine le_trans ?_ (bad_card N k)
  calc _ ≤ (((Fintype.piFinset fun _ : Fin s => range N).filter
            (fun n => ∃ i, ¬ ((0 : ℤ) ≤ n i + k i ∧ (n i : ℤ) + k i < N))).image (phi e)).card := by
        apply card_le_card
        intro g hg
        simp only [mem_filter, box, mem_image] at hg
        obtain ⟨⟨n, hn, rfl⟩, hout⟩ := hg
        refine mem_image.mpr ⟨n, mem_filter.mpr ⟨hn, ?_⟩, rfl⟩
        by_contra hall
        push Not at hall
        apply hout
        refine ⟨fun i => (n i + k i).toNat, Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
        · have := hall i
          simp only [mem_range]
          omega
        · simp only [phi]
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro i _
          rw [← add_smul]
          congr 1
          have := hall i
          omega
    _ ≤ _ := card_image_le

end Box

/-- Translates of a subset of a finite set: either the translate stays inside, or the point is a
boundary point. -/
lemma count_shift (F J : Finset V) (hJ : J ⊆ F) (a : V) :
    J.card ≤ (F.filter (fun g => a + g ∈ J)).card + (F.filter (fun g => g + -a ∉ F)).card := by
  classical
  calc J.card ≤ ((F.filter (fun g => a + g ∈ J)).image (fun g => a + g) ∪
        F.filter (fun g => g + -a ∉ F)).card := by
        apply card_le_card
        intro j hj
        by_cases h : j + -a ∈ F
        · refine mem_union_left _ (mem_image.mpr ⟨j + -a, mem_filter.mpr ⟨h, ?_⟩, ?_⟩)
          · rwa [add_comm, neg_add_cancel_right]
          · abel
        · exact mem_union_right _ (mem_filter.mpr ⟨hJ hj, h⟩)
    _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add_right card_image_le _)

lemma emb_injective : Function.Injective emb := by
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-! ### Finite windows -/

/-- Contrapositive hypothesis: every nonempty finite set of points has a large independent
subset. -/
def LargeIndep (c : ℝ) : Prop :=
  ∀ S : Finset (ℂ × ℝ), S.Nonempty →
    ∃ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, usq (x - y) ≠ 1) ∧ c * S.card < I.card

theorem exists_window_state {c : ℝ} (hc : LargeIndep c) (W : Finset V) (n : ℕ) :
    ∃ L : State ISpace, ∀ a ∈ W, c - 2 * (1 / ((n : ℝ) + 1)) ≤ L.toFun (ev a) := by
  classical
  obtain ⟨s, e, he, hk⟩ := exists_lattice W
  choose! k hk using hk
  set K : ℕ := 1 + ∑ w ∈ W, ∑ i, (k w i).natAbs with hK
  set N : ℕ := (n + 1) * K with hNdef
  have hKpos : 0 < K := by omega
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos n) hKpos
  set F := box e N with hFdef
  have hFcard : F.card = N ^ s := box_card e he N
  have hFne : F.Nonempty :=
    ⟨phi e 0, mem_image.mpr ⟨0, Fintype.mem_piFinset.mpr fun _ => mem_range.mpr hN, rfl⟩⟩
  have hFpos : (0 : ℝ) < (F.card : ℝ) := by exact_mod_cast hFne.card_pos
  obtain ⟨I, hIF, hIind, hIcard⟩ := hc (F.map ⟨emb, emb_injective⟩) (hFne.map)
  set J := F.filter (fun g => emb g ∈ I) with hJdef
  have hJF : J ⊆ F := filter_subset _ _
  have hJI : J.card = I.card := by
    have : J.map ⟨emb, emb_injective⟩ = I := by
      ext y
      simp only [Finset.mem_map, mem_filter, J, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨g, ⟨_, hg⟩, rfl⟩
        exact hg
      · intro hy
        obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp (hIF hy)
        exact ⟨g, ⟨hg, hy⟩, rfl⟩
    rw [← this, card_map]
  have hJind : ∀ g ∈ J, ∀ h ∈ J, sq (g - h) ≠ 1 := by
    intro g hg h hh
    rw [← usq_emb_sub]
    exact hIind _ (mem_filter.mp hg).2 _ (mem_filter.mp hh).2
  -- translated configurations
  let om : V → ISpace := fun g => ⟨fun x => if x + g ∈ J then 1 else 0, by
    intro x y hxy hb
    obtain ⟨h1, h2⟩ := hb
    have hx : x + g ∈ J := by
      by_contra h
      simp [h] at h1
    have hy : y + g ∈ J := by
      by_contra h
      simp [h] at h2
    exact hJind _ hx _ hy (by rwa [add_sub_add_right_eq_sub])⟩
  let Lw : State ISpace :=
    { toFun := fun f => (F.card : ℝ)⁻¹ * ∑ g ∈ F, f (om g)
      map_add := by
        intro f h
        simp only [ContinuousMap.add_apply, sum_add_distrib, mul_add]
      map_smul := by
        intro r f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sum]
        ring
      nonneg := fun f hf => mul_nonneg (inv_nonneg.mpr hFpos.le) (sum_nonneg fun g _ => hf _)
      map_one := by
        simp only [ContinuousMap.one_apply, sum_const, nsmul_eq_mul, mul_one]
        exact inv_mul_cancel₀ hFpos.ne' }
  refine ⟨Lw, fun a ha => ?_⟩
  have hev : Lw.toFun (ev a) = (F.card : ℝ)⁻¹ * ((F.filter (fun g => a + g ∈ J)).card : ℝ) := by
    change (F.card : ℝ)⁻¹ * ∑ g ∈ F, ev a (om g) = _
    congr 1
    rw [← sum_boole]
    apply sum_congr rfl
    intro g _
    by_cases h : a + g ∈ J <;> simp [ev_apply, om, h]
  -- the boundary is small
  have hka := hk a ha
  have hneg : -a = ∑ i, (-k a i) • e i := by
    conv_lhs => rw [hka]
    rw [← sum_neg_distrib]
    simp only [neg_smul]
  set B : ℕ := ∑ i, 2 * (k a i).natAbs * N ^ (s - 1) with hB
  have hbad : (F.filter (fun g => g + -a ∉ F)).card ≤ B := by
    have := box_shift_bad e N (fun i => -k a i)
    simp only [Int.natAbs_neg] at this
    rw [hneg]
    exact this
  have hcount := count_shift F J hJF a
  have hBN : B * N ≤ 2 * K * N ^ s := by
    have h1 : B * N = 2 * (∑ i, (k a i).natAbs) * N ^ s := by
      rw [hB, sum_mul, mul_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      have hs : s - 1 + 1 = s := Nat.sub_add_cancel i.pos
      calc 2 * (k a i).natAbs * N ^ (s - 1) * N = 2 * (k a i).natAbs * N ^ (s - 1 + 1) := by
            rw [pow_succ]; ring
        _ = _ := by rw [hs]
    have h2 : ∑ i, (k a i).natAbs ≤ K := by
      have := single_le_sum (f := fun w => ∑ i, (k w i).natAbs) (fun _ _ => Nat.zero_le _) ha
      omega
    rw [h1]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
  have hBn : (B : ℝ) * ((n : ℝ) + 1) ≤ 2 * (F.card : ℝ) := by
    have h3 : B * (n + 1) ≤ 2 * N ^ s := by
      have : B * (n + 1) * K ≤ 2 * N ^ s * K := by
        calc B * (n + 1) * K = B * N := by rw [hNdef]; ring
          _ ≤ 2 * K * N ^ s := hBN
          _ = 2 * N ^ s * K := by ring
      exact Nat.le_of_mul_le_mul_right this hKpos
    rw [hFcard]
    exact_mod_cast h3
  -- conclude
  rw [hev, ← div_eq_inv_mul, le_div_iff₀ hFpos]
  have h1 : ((J.card : ℕ) : ℝ) ≤ ((F.filter (fun g => a + g ∈ J)).card : ℝ) + B := by
    exact_mod_cast hcount.trans (Nat.add_le_add_left hbad _)
  have h2 : c * (F.card : ℝ) < J.card := by
    rw [hJI]
    simpa [card_map] using hIcard
  have h4 : (B : ℝ) ≤ 2 * (1 / ((n : ℝ) + 1)) * F.card := by
    rw [mul_comm 2, mul_assoc, one_div, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  nlinarith

/-! ### The limit state -/

theorem exists_state {c : ℝ} (hc : LargeIndep c) :
    ∃ L : State ISpace, ∀ a, c ≤ L.toFun (ev a) := by
  choose Lw hLw using exists_window_state hc
  let U := averagingUF V
  let seq : C(ISpace, ℝ) → (Finset V × ℕ) → ℝ := fun f i => (Lw i.1 i.2).toFun f
  have hlim : ∀ f, ∃ r, Tendsto (seq f) (U : Filter _) (𝓝 r) := by
    intro f
    have hb : (Ultrafilter.map (seq f) U : Filter ℝ) ≤ 𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
      rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
      apply Filter.Eventually.of_forall
      intro i
      exact abs_le.mp ((Lw i.1 i.2).abs_le f)
    obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds (Ultrafilter.map (seq f) U) hb
    exact ⟨r, hr⟩
  let Lf : C(ISpace, ℝ) → ℝ := fun f => (U : Filter _).limUnder (seq f)
  have ht : ∀ f, Tendsto (seq f) (U : Filter _) (𝓝 (Lf f)) :=
    fun f => tendsto_nhds_limUnder (hlim f)
  refine ⟨⟨Lf, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f g
    apply Tendsto.limUnder_eq
    convert (ht f).add (ht g) using 1
    funext i
    exact (Lw i.1 i.2).map_add f g
  · intro r f
    apply Tendsto.limUnder_eq
    convert (ht f).const_mul r using 1
    funext i
    exact (Lw i.1 i.2).map_smul r f
  · intro f hf
    exact ge_of_tendsto (ht f) (Filter.Eventually.of_forall fun i => (Lw i.1 i.2).nonneg f hf)
  · apply Tendsto.limUnder_eq
    convert (tendsto_const_nhds : Tendsto (fun _ : Finset V × ℕ => (1 : ℝ)) (U : Filter _) (𝓝 1))
      using 1
    funext i
    exact (Lw i.1 i.2).map_one
  · intro a
    have h2 : Tendsto (fun i : Finset V × ℕ => c - 2 * (1 / ((i.2 : ℝ) + 1))) (U : Filter _)
        (𝓝 c) := by
      have h : Tendsto (fun n : ℕ => c - 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 c) := by
        simpa using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))
      exact h.comp (tendsto_index (G := V))
    apply le_of_tendsto_of_tendsto h2 (ht (ev a))
    filter_upwards [eventually_mem (G := V) a] with i hi
    exact hLw i.1 i.2 a hi

/-! ### Main theorems -/

/-- Any density bound is nonnegative: a small ball is unit-distance-free and has positive
measure in every large cube. -/
lemma densityBound_nonneg {δ : ℝ} (hδ : DensityBound δ) : 0 ≤ δ := by
  by_contra hneg
  push Not at hneg
  let S : Set (ℂ × ℝ) := Metric.ball 0 (1 / 4)
  have hSu : ∀ x ∈ S, ∀ y ∈ S, usq (x - y) ≠ 1 := by
    intro x hx y hy h
    simp only [S, Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff,
      Real.norm_eq_abs] at hx hy
    have h1 : ‖x.1 - y.1‖ < 1 / 2 := by
      have := norm_sub_le x.1 y.1
      linarith [hx.1, hy.1]
    have h2 : |x.2 - y.2| < 1 / 2 := by
      have := abs_sub x.2 y.2
      linarith [hx.2, hy.2]
    have h3 : ‖x.1 - y.1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (x.1 - y.1)]
    have h4 : (x.2 - y.2) ^ 2 < 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (x.2 - y.2)]
    have : usq (x - y) < 1 := by
      simp only [usq, Prod.fst_sub, Prod.snd_sub]
      linarith
    linarith
  have hb := hδ S measurableSet_ball hSu (-δ) (by linarith)
  obtain ⟨T, hT, hT1⟩ := (hb.and (eventually_ge_atTop (1 : ℝ))).exists
  rw [add_neg_cancel, ENNReal.ofReal_zero, zero_mul, nonpos_iff_eq_zero] at hT
  have hsub : S ⊆ cube T := by
    intro x hx
    simp only [S, Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff,
      Real.norm_eq_abs] at hx
    refine ⟨?_, ?_, ?_⟩
    · linarith [Complex.abs_re_le_norm x.1]
    · linarith [Complex.abs_im_le_norm x.1]
    · linarith
  rw [Set.inter_eq_left.mpr hsub] at hT
  exact (Metric.measure_ball_pos volume (0 : ℂ × ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).ne' hT

/-- **Finite unit-distance graphs in `ℝ³` attain the measurable density.** If `δ` bounds the
upper density of every measurable unit-distance-free subset of `ℝ³`, then for every `ε > 0` some
finite point set has independence ratio at most `δ + ε`. -/
theorem finite_ratio_of_density {δ : ℝ} (hδ : DensityBound δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset (ℂ × ℝ), S.Nonempty ∧ ∀ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, usq (x - y) ≠ 1) →
      (I.card : ℝ) ≤ (δ + ε) * S.card := by
  by_contra hne
  have hc : LargeIndep (δ + ε) := by
    intro S hS
    by_contra hI
    apply hne
    refine ⟨S, hS, fun I hIS hind => ?_⟩
    by_contra hlt
    exact hI ⟨I, hIS, hind, lt_of_not_ge hlt⟩
  obtain ⟨L, hL⟩ := exists_state hc
  have := density_le hδ L hL
  rw [max_eq_left (densityBound_nonneg hδ)] at this
  linarith

/-- With the DeCorte–Oliveira–Vallentin bound `m₁(ℝ³) ≤ 0.1532996`: some finite unit-distance
graph in `ℝ³` has independence ratio below `0.1533`. -/
theorem exists_finite_ratio_lt (hDOV : DensityBound 0.1532996) :
    ∃ S : Finset (ℂ × ℝ), S.Nonempty ∧ ∀ I ⊆ S, (∀ x ∈ I, ∀ y ∈ I, usq (x - y) ≠ 1) →
      (I.card : ℝ) < 0.1533 * S.card := by
  obtain ⟨S, hS, h⟩ := finite_ratio_of_density hDOV (ε := 0.0000002) (by norm_num)
  refine ⟨S, hS, fun I hIS hind => (h I hIS hind).trans_lt ?_⟩
  have : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  nlinarith

/-! ### The two constants -/

open Classical in
/-- The unit-distance-free subsets of a finite point set. -/
def indepSets (S : Finset (ℂ × ℝ)) : Finset (Finset (ℂ × ℝ)) :=
  S.powerset.filter fun I => ∀ x ∈ I, ∀ y ∈ I, usq (x - y) ≠ 1

lemma mem_indepSets {S I : Finset (ℂ × ℝ)} :
    I ∈ indepSets S ↔ I ⊆ S ∧ ∀ x ∈ I, ∀ y ∈ I, usq (x - y) ≠ 1 := by
  unfold indepSets
  rw [Finset.mem_filter, Finset.mem_powerset]

/-- Independence number of the unit-distance graph on a finite point set. -/
def indepNum (S : Finset (ℂ × ℝ)) : ℕ := (indepSets S).sup Finset.card

/-- `α₁(ℝ³)`: the infimum of the independence ratios of finite unit-distance graphs in `ℝ³`. -/
def alpha1 : ℝ := sInf ((fun S : Finset (ℂ × ℝ) => (indepNum S : ℝ) / S.card) '' {S | S.Nonempty})

/-- `m₁(ℝ³)`: the least `δ` bounding the upper (centered-cube) density of every measurable
unit-distance-free subset of `ℝ³`. -/
def m1 : ℝ := sInf {δ : ℝ | DensityBound δ}

lemma densityBound_one : DensityBound 1 := by
  intro S _ _ ε hε
  refine Filter.Eventually.of_forall fun T => ?_
  calc volume (S ∩ cube T) ≤ volume (cube T) := measure_mono Set.inter_subset_right
    _ = 1 * volume (cube T) := (one_mul _).symm
    _ ≤ ENNReal.ofReal (1 + ε) * volume (cube T) := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **`α₁(ℝ³) ≤ m₁(ℝ³)`.** (With the easy averaging inequality `m₁ ≤ α₁`, not formalized here,
this is `α₁(ℝ³) = m₁(ℝ³)`.) -/
theorem alpha1_le_m1 : alpha1 ≤ m1 := by
  classical
  apply le_csInf ⟨1, densityBound_one⟩
  intro δ hδ
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨S, hS, hI⟩ := finite_ratio_of_density hδ hε
  have hne : (indepSets S).Nonempty :=
    ⟨∅, mem_indepSets.mpr ⟨Finset.empty_subset S, by simp⟩⟩
  obtain ⟨I, hImem, hIeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hIS, hind⟩ := mem_indepSets.mp hImem
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hratio : (indepNum S : ℝ) / S.card ≤ δ + ε := by
    rw [div_le_iff₀ hpos]
    rw [indepNum, hIeq]
    exact hI I hIS hind
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨S, hS, rfl⟩) hratio
  rintro _ ⟨T, _, rfl⟩
  positivity

/-- With the DeCorte–Oliveira–Vallentin bound: `α₁(ℝ³) ≤ 0.1532996`. -/
theorem alpha1_le_of_DOV (hDOV : DensityBound 0.1532996) : alpha1 ≤ 0.1532996 :=
  alpha1_le_m1.trans (csInf_le ⟨0, fun _ h => densityBound_nonneg h⟩ hDOV)

end Indep
end HN3
end
end OAI
