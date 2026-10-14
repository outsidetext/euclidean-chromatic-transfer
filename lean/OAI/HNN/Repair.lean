import OAI.HNN.Euclid

/-!
# Ordinary and Lebesgue-measurable chromatic numbers coincide

A conull, pointwise proper partition into measurable classes extends to a proper colouring of
**all** of `ℝⁿ` that agrees with it almost everywhere.  Proof: anchor every Lebesgue density
point of its own class, colour any finite configuration by a small common translate (which
lands every vertex in the conull set and every anchor in its own class), and apply
de Bruijn–Erdős compactness with `k` palette vertices encoding the anchors.

Combined with `euclidean_transfer_set`, every proper colouring of `ℝⁿ` (`n ≥ 2`) avoiding a
countable set of algebraic distances yields a proper colouring by the same number of
**Lebesgue measurable** classes.  Hence `χ(ℝⁿ, D) = χ_m(ℝⁿ, D)`; for `D = {1}` and `n = 2, 3`
this is the equality of the ordinary and measurable chromatic numbers of the plane and of
three-space (Székely asked whether they can differ; Davies proved equality for `n ≥ 4`).
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set Metric
namespace HNN

variable {n : ℕ}

/-- `x` is a point of Lebesgue density one of `A`, phrased via the complement. -/
def Thin (A : Set (EE n)) (x : EE n) : Prop :=
  Tendsto (fun r : ℝ => volume (Aᶜ ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0) (𝓝 0)

lemma ae_thin {A : Set (EE n)} (hA : MeasurableSet A) : ∀ᵐ x ∂(volume : Measure (EE n)),
    x ∈ A → Thin A x := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hA.compl]
    with x hx hxA
  have h0 : (Aᶜ).indicator (1 : EE n → ENNReal) x = 0 :=
    indicator_of_notMem (by simpa using hxA) _
  simpa only [Thin, h0] using hx

section Finite

variable {k : ℕ} (A : Fin k → Set (EE n))

/-- **Finite step.** For a finite configuration `V`, some translation vector `t` sends every
vertex into the conull set `⋃ i, A i` and every density point of `A i` in `V` into `A i`. -/
lemma exists_good_translate (hnull : volume (⋃ i, A i)ᶜ = 0)
    (V : Finset (EE n)) : ∃ t : EE n, (∀ v ∈ V, v + t ∈ ⋃ i, A i) ∧
      ∀ v ∈ V, ∀ i, v ∈ A i → Thin (A i) v → v + t ∈ A i := by
  classical
  let S : Finset (EE n × Fin k) :=
    (V ×ˢ Finset.univ).filter (fun p => p.1 ∈ A p.2 ∧ Thin (A p.2) p.1)
  let ε : ENNReal := (S.card : ENNReal)⁻¹
  have hε : 0 < ε := ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p ∈ S,
      volume ((A p.2)ᶜ ∩ closedBall p.1 r) / volume (closedBall p.1 r) < ε := by
    rw [eventually_all_finset]
    intro p hp
    exact ((Finset.mem_filter.mp hp).2.2).eventually (gt_mem_nhds hε)
  obtain ⟨r, hr, hr0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hr0 : (0 : ℝ) < r := hr0
  let B : Set (EE n) := closedBall 0 r
  have hBpos : 0 < volume B := measure_closedBall_pos volume 0 hr0
  have hBfin : volume B ≠ ⊤ := (isCompact_closedBall 0 r).measure_ne_top
  have hball : ∀ v : EE n, volume (closedBall v r) = volume B := fun v =>
    Measure.addHaar_closedBall_center volume v r
  have hpre : ∀ v : EE n, (fun t => v + t) ⁻¹' closedBall v r = B := by
    intro v; ext t; simp [B, dist_eq_norm]
  let bad1 : Set (EE n) := ⋃ v ∈ V, (fun t => v + t) ⁻¹' (⋃ i, A i)ᶜ
  let bad : EE n × Fin k → Set (EE n) := fun p =>
    (fun t => p.1 + t) ⁻¹' ((A p.2)ᶜ ∩ closedBall p.1 r)
  let bad2 : Set (EE n) := ⋃ p ∈ S, bad p
  have h1 : volume bad1 = 0 := by
    apply (measure_biUnion_null_iff V.countable_toSet).mpr
    intro v _
    rw [measure_preimage_add]; exact hnull
  have hbad : ∀ p ∈ S, volume (bad p) < ε * volume B := by
    intro p hp
    have h := hr p hp
    rw [ENNReal.div_lt_iff (Or.inl (measure_closedBall_pos volume p.1 hr0).ne')
      (Or.inl (isCompact_closedBall p.1 r).measure_ne_top), hball] at h
    simpa only [bad, measure_preimage_add] using h
  have h2 : volume bad2 < volume B := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · simp only [bad2, hS, Finset.notMem_empty, iUnion_of_empty, iUnion_empty, measure_empty]
      exact hBpos
    · calc volume bad2 ≤ ∑ p ∈ S, volume (bad p) := measure_biUnion_finset_le S bad
        _ < ∑ _p ∈ S, ε * volume B := ENNReal.sum_lt_sum_of_nonempty hS hbad
        _ = volume B := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel
            (by exact_mod_cast hS.card_pos.ne') (ENNReal.natCast_ne_top _), one_mul]
  have h12 : volume (bad1 ∪ bad2) < volume B :=
    lt_of_le_of_lt (measure_union_le _ _) (by rw [h1, zero_add]; exact h2)
  obtain ⟨t, htB, htg⟩ : (B \ (bad1 ∪ bad2)).Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at hE
    exact (measure_mono hE).not_gt h12
  refine ⟨t, fun v hv => ?_, fun v hv i hvi hth => ?_⟩
  · by_contra h
    exact htg (Or.inl (mem_biUnion hv (show v + t ∈ (⋃ i, A i)ᶜ from h)))
  · by_contra h
    have hp : (v, i) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩,
      hvi, hth⟩
    have hvt : v + t ∈ closedBall v r := by rw [← hpre v] at htB; exact htB
    exact htg (Or.inr (mem_biUnion hp (show v + t ∈ (A i)ᶜ ∩ closedBall v r from ⟨h, hvt⟩)))

end Finite

/-- **Measurable repair.** A conull partition of `ℝⁿ` into measurable classes containing no
distance from `D` extends to a proper colouring of all of `ℝⁿ` that equals `i` on every
density point of `A i` lying in `A i` (hence on almost all of `A i`). -/
theorem proper_of_conull_partition {k : ℕ} [NeZero k] {D : Set ℝ} (A : Fin k → Set (EE n))
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hnull : volume (⋃ i, A i)ᶜ = 0) (hfree : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ∉ D) :
    ∃ C : EE n → Fin k, (∀ x y, x ≠ y → dist x y ∈ D → C x ≠ C y) ∧
      ∀ i x, x ∈ A i → Thin (A i) x → C x = i := by
  classical
  let lab : EE n → Fin k := fun x => if h : ∃ i, x ∈ A i then h.choose else 0
  have hlab : ∀ i x, x ∈ A i → lab x = i := by
    intro i x hx
    have h : ∃ i, x ∈ A i := ⟨i, hx⟩
    simp only [lab, dif_pos h]
    by_contra hne
    exact (hdisj hne).ne_of_mem h.choose_spec hx rfl
  let Anc : Fin k → EE n → Prop := fun i x => x ∈ A i ∧ Thin (A i) x
  let R : EE n ⊕ Fin k → EE n ⊕ Fin k → Prop
    | .inl x, .inl y => dist x y ∈ D
    | .inr _, .inr _ => True
    | .inl x, .inr j => ∃ i, i ≠ j ∧ Anc i x
    | .inr _, .inl _ => False
  let G : SimpleGraph (EE n ⊕ Fin k) := SimpleGraph.fromRel R
  have hom : Nonempty (G →g (⊤ : SimpleGraph (Fin k))) := by
    apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
    intro G' hG'
    let V : Finset (EE n) := hG'.toFinset.preimage Sum.inl Sum.inl_injective.injOn
    have hex := exists_good_translate A hnull V
    let t := hex.choose
    have htV := hex.choose_spec.1
    have htA := hex.choose_spec.2
    have memV : ∀ x, Sum.inl x ∈ G'.verts → x ∈ V := fun x hx =>
      Finset.mem_preimage.mpr (hG'.mem_toFinset.mpr hx)
    have edge : ∀ x y, x ∈ V → y ∈ V → dist x y ∈ D → lab (x + t) ≠ lab (y + t) := by
      intro x y hx hy hd heq
      obtain ⟨i, hi⟩ := mem_iUnion.mp (htV x hx)
      obtain ⟨j, hj⟩ := mem_iUnion.mp (htV y hy)
      rw [hlab i _ hi, hlab j _ hj] at heq
      subst heq
      exact hfree i _ hi _ hj (by rwa [dist_add_right])
    refine ⟨fun w => Sum.elim (fun x => lab (x + t)) id w.1, ?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hG := G'.adj_sub hab
    simp only [G, SimpleGraph.fromRel_adj] at hG
    obtain ⟨hne, hR⟩ := hG
    rw [SimpleGraph.top_adj]
    rcases a with x | i <;> rcases b with y | j
    · rcases hR with h | h
      · exact edge x y (memV x ha) (memV y hb) h
      · exact (edge y x (memV y hb) (memV x ha) h).symm
    · rcases hR with ⟨i, hij, hA', hth⟩ | h
      · show lab (x + t) ≠ j
        rw [hlab i _ (htA x (memV x ha) i hA' hth)]; exact hij
      · exact h.elim
    · rcases hR with h | ⟨j, hji, hA', hth⟩
      · exact h.elim
      · show i ≠ lab (y + t)
        rw [hlab j _ (htA y (memV y hb) j hA' hth)]; exact hji.symm
    · simpa using fun h => hne (congrArg Sum.inr h)
  obtain ⟨f⟩ := hom
  have hadj : ∀ a b, G.Adj a b → f a ≠ f b := fun a b h =>
    (SimpleGraph.top_adj _ _).mp (f.map_rel h)
  have hσ : Function.Bijective (fun i : Fin k => f (Sum.inr i)) := by
    refine Finite.injective_iff_bijective.mp fun i j hij => ?_
    by_contra hne
    exact hadj _ _ (by simp [G, SimpleGraph.fromRel_adj, R, hne]) hij
  let σ := Equiv.ofBijective _ hσ
  refine ⟨fun x => σ.symm (f (Sum.inl x)), fun x y hxy hd => ?_, fun i x hx hth => ?_⟩
  · intro h
    exact hadj (Sum.inl x) (Sum.inl y) (by simp [G, SimpleGraph.fromRel_adj, R, hxy, hd])
      (σ.symm.injective h)
  · apply σ.injective
    simp only [Equiv.apply_symm_apply]
    obtain ⟨j, hj⟩ := hσ.2 (f (Sum.inl x))
    by_contra hne
    have hji : j ≠ i := fun h => hne (by rw [← hj, h]; rfl)
    exact hadj (Sum.inl x) (Sum.inr j)
      (by simp only [G, SimpleGraph.fromRel_adj, R]; exact ⟨by simp, Or.inl ⟨i, hji.symm, hx, hth⟩⟩)
      (by rw [← hj])

/-- **Every conull measurable `D`-avoiding partition is a.e. equal to a genuinely proper
Lebesgue-measurable colouring of `ℝⁿ`.** -/
theorem measurable_proper_of_conull_partition {k : ℕ} [NeZero k] {D : Set ℝ}
    (A : Fin k → Set (EE n)) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (hnull : volume (⋃ i, A i)ᶜ = 0)
    (hfree : ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, dist x y ∉ D) :
    ∃ C : EE n → Fin k, (∀ x y, dist x y ∈ D → C x ≠ C y) ∧
      ∀ i, {x | C x = i} =ᵐ[volume] A i := by
  obtain ⟨C, hC, hanc⟩ := proper_of_conull_partition A hA hdisj hnull hfree
  have hae : ∀ᵐ x ∂(volume : Measure (EE n)), ∃ i, x ∈ A i ∧ Thin (A i) x := by
    have hall := ae_all_iff.mpr fun i => ae_thin (hA i)
    have hcov : ∀ᵐ x ∂(volume : Measure (EE n)), x ∈ ⋃ i, A i := measure_eq_zero_iff_ae_notMem.mp
      (by simpa using hnull) |>.mono fun x hx => by simpa using hx
    filter_upwards [hall, hcov] with x hx hxc
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxc
    exact ⟨i, hi, hx i hi⟩
  refine ⟨C, fun x y hd => ?_, fun i => ?_⟩
  · by_cases hxy : x = y
    · exfalso
      subst hxy
      obtain ⟨z, i, hz, -⟩ := hae.exists
      exact hfree i z hz z hz (by simpa using hd)
    · exact hC x y hxy hd
  · filter_upwards [hae] with x ⟨j, hj, hth⟩
    have hCx := hanc j x hj hth
    change (C x = i) = (x ∈ A i)
    apply propext
    constructor
    · intro h; rw [← h, hCx]; exact hj
    · intro h
      by_contra hne
      exact (hdisj (show j ≠ i from fun e => hne (by rw [hCx, e]))).ne_of_mem hj h rfl

/-- **`χ(ℝⁿ, D) = χ_m(ℝⁿ, D)`** for every `n ≥ 2` and every countable set `D` of positive
algebraic distances: a proper `k`-colouring exists iff one with Lebesgue measurable classes does. -/
theorem chromatic_eq_measurable_chromatic_set (hn : 2 ≤ n) {D : Set ℝ} (hDc : D.Countable)
    (hD : ∀ d ∈ D, 0 < d ∧ IsAlgebraic ℚ d) {k : ℕ} [NeZero k] :
    (∃ c : EE n → Fin k, ∀ x y, dist x y ∈ D → c x ≠ c y) ↔
      ∃ c : EE n → Fin k, (∀ i, NullMeasurableSet {x | c x = i} volume) ∧
        ∀ x y, dist x y ∈ D → c x ≠ c y := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨A, hA, hdisj, hnull, hfree⟩ := euclidean_transfer_set hn hDc hD c hc
    obtain ⟨C, hC, heq⟩ := measurable_proper_of_conull_partition A hA hdisj hnull hfree
    exact ⟨C, fun i => (hA i).nullMeasurableSet.congr (heq i).symm, hC⟩
  · rintro ⟨c, -, hc⟩
    exact ⟨c, hc⟩

/-- **The chromatic number of `ℝⁿ` equals its Lebesgue-measurable chromatic number**
(`n ≥ 2`; in particular for the plane and three-space). -/
theorem chromatic_eq_measurable_chromatic (hn : 2 ≤ n) {k : ℕ} [NeZero k] :
    (∃ c : EE n → Fin k, ∀ x y, dist x y = 1 → c x ≠ c y) ↔
      ∃ c : EE n → Fin k, (∀ i, NullMeasurableSet {x | c x = i} volume) ∧
        ∀ x y, dist x y = 1 → c x ≠ c y := by
  have h := chromatic_eq_measurable_chromatic_set hn (D := {1}) (countable_singleton 1)
    (fun d hd => by rw [mem_singleton_iff.mp hd]; exact ⟨one_pos, isAlgebraic_one⟩) (k := k)
  simpa only [mem_singleton_iff] using h

end HNN
end
end OAI
