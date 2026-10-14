import OAI.Soifer.FKW

/-!
# Monochromatic distances `2ⁿ` and `n!` (Soifer, Kahle)

For every finite colouring of the plane and every unbounded set `S` of positive real algebraic
numbers, some `s ∈ S` is a monochromatic distance. Hence all sufficiently large powers of two,
and all sufficiently large factorials, are monochromatic distances. The same holds in `ℝⁿ`,
`n ≥ 2`, by restricting the colouring to a plane.

Proof: if every `s ∈ S` is avoided, `euclidean_transfer_set` (with `D = S`, countable since
algebraic) gives measurable `S`-avoiding classes covering a conull set; one class has density
`≥ 1/k` in arbitrarily large squares, contradicting `fkw`.
-/

namespace OAI.Soifer

noncomputable section
open MeasureTheory Filter Topology Set
open OAI.HNN

/-- Some colour class has density `≥ 1/k` in arbitrarily large squares. -/
lemma exists_dense_class {k : ℕ} [NeZero k] {A : Fin k → Set (EuclideanSpace ℝ (Fin 2))}
    (hAm : ∀ i, MeasurableSet (A i)) (hAd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hAn : volume (⋃ i, A i)ᶜ = 0) :
    ∃ i, ∃ᶠ T in atTop, ENNReal.ofReal (1 / k) * volume (cube 2 T) ≤ volume (A i ∩ cube 2 T) := by
  by_contra hno
  push Not at hno
  have hev : ∀ᶠ T in atTop, ∀ i, volume (A i ∩ cube 2 T) <
      ENNReal.ofReal (1 / k) * volume (cube 2 T) :=
    eventually_all.mpr hno
  obtain ⟨T, hT, hT1⟩ := (hev.and (eventually_gt_atTop 0)).exists
  have hsum : volume (cube 2 T) = ∑ i, volume (A i ∩ cube 2 T) := by
    have h1 : volume (cube 2 T) = volume ((⋃ i, A i) ∩ cube 2 T) := by
      apply le_antisymm _ (measure_mono inter_subset_right)
      calc volume (cube 2 T) ≤ volume (((⋃ i, A i) ∩ cube 2 T) ∪ (⋃ i, A i)ᶜ) :=
            measure_mono (fun x hx => by
              by_cases h : x ∈ ⋃ i, A i
              · exact Or.inl ⟨h, hx⟩
              · exact Or.inr h)
        _ ≤ volume ((⋃ i, A i) ∩ cube 2 T) + volume (⋃ i, A i)ᶜ := measure_union_le _ _
        _ = volume ((⋃ i, A i) ∩ cube 2 T) := by rw [hAn, add_zero]
    rw [h1, iUnion_inter, measure_iUnion]
    · rw [tsum_fintype]
    · intro i j hij
      exact (hAd hij).mono inter_subset_left inter_subset_left
    · exact fun i => (hAm i).inter (cube_measurable T)
  have hlt : ∑ i, volume (A i ∩ cube 2 T) <
      ∑ _i : Fin k, ENNReal.ofReal (1 / k) * volume (cube 2 T) :=
    ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hT i
  have hk : (k : ENNReal) * ENNReal.ofReal (1 / k) = 1 := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [mul_one_div_cancel hk0.ne', ENNReal.ofReal_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, hk,
    one_mul, ← hsum] at hlt
  exact lt_irrefl _ hlt

/-- **Monochromatic distances from any unbounded set of positive algebraic reals.** -/
theorem mono_distance_of_unbounded {k : ℕ} [NeZero k] (c : EuclideanSpace ℝ (Fin 2) → Fin k)
    {S : Set ℝ} (hS : ∀ s ∈ S, 0 < s ∧ IsAlgebraic ℚ s) (hunb : ¬ BddAbove S) :
    ∃ s ∈ S, ∃ x y, dist x y = s ∧ c x = c y := by
  by_contra h
  push Not at h
  have hDc : S.Countable := (Algebraic.countable ℚ ℝ).mono fun s hs => (hS s hs).2
  obtain ⟨A, hAm, hAd, hAn, hAu⟩ :=
    euclidean_transfer_set le_rfl hDc hS c (fun x y hxy => h _ hxy x y rfl)
  obtain ⟨i, hi⟩ := exists_dense_class hAm hAd hAn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨s, hs, x, hx, y, hy, hxy⟩ :=
    fkw (hAm i) (one_div_pos.mpr hk0) hi (fun s hs => (hS s hs).1) hunb
  exact hAu i x hx y hy (hxy ▸ hs)

/-- All but finitely many terms of a sequence of positive algebraic reals tending to infinity
are monochromatic distances. -/
theorem mono_distance_eventually {k : ℕ} [NeZero k] (c : EuclideanSpace ℝ (Fin 2) → Fin k)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ IsAlgebraic ℚ (a n)) (htend : Tendsto a atTop atTop) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ x y, dist x y = a n ∧ c x = c y := by
  by_contra h
  push Not at h
  set S := {s | ∃ n, s = a n ∧ ∀ x y, dist x y = a n → c x ≠ c y} with hS_def
  have hS : ∀ s ∈ S, 0 < s ∧ IsAlgebraic ℚ s := by
    rintro s ⟨n, rfl, -⟩; exact ha n
  have hSunb : ¬ BddAbove S := by
    rw [not_bddAbove_iff]
    intro M
    obtain ⟨N0, hN0⟩ := eventually_atTop.mp (htend.eventually_gt_atTop M)
    obtain ⟨n, hn, hbad⟩ := h N0
    exact ⟨a n, ⟨n, rfl, hbad⟩, hN0 n hn⟩
  obtain ⟨s, ⟨n, rfl, hbad⟩, x, y, hxy, hc⟩ := mono_distance_of_unbounded c hS hSunb
  exact hbad x y hxy hc

/-- **Soifer's question.** Every finite colouring of the plane has two points of the same colour
at distance `2ⁿ`, for all sufficiently large `n`. -/
theorem soifer {k : ℕ} [NeZero k] (c : EuclideanSpace ℝ (Fin 2) → Fin k) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ x y, dist x y = (2 : ℝ) ^ n ∧ c x = c y :=
  mono_distance_eventually c (fun n => (2 : ℝ) ^ n)
    (fun n => ⟨by positivity, by
      have := isAlgebraic_natCast (R := ℚ) (A := ℝ) (2 ^ n)
      simpa using this⟩)
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- **Kahle's question.** Every finite colouring of the plane has two points of the same colour
at distance `n!`, for all sufficiently large `n`. -/
theorem kahle {k : ℕ} [NeZero k] (c : EuclideanSpace ℝ (Fin 2) → Fin k) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ x y, dist x y = (n.factorial : ℝ) ∧ c x = c y :=
  mono_distance_eventually c (fun n => (n.factorial : ℝ))
    (fun n => ⟨by exact_mod_cast Nat.factorial_pos n, isAlgebraic_natCast _⟩)
    (tendsto_atTop_mono (fun n => by exact_mod_cast Nat.self_le_factorial n)
      tendsto_natCast_atTop_atTop)

/-! ### Higher dimensions, by restriction to a plane -/

/-- The coordinate plane in `ℝ^(2+m)`. -/
def planeEmb (m : ℕ) (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin (2 + m)) :=
  WithLp.toLp 2 (Fin.append x.ofLp (0 : Fin m → ℝ))

lemma dist_planeEmb (m : ℕ) (x y : EuclideanSpace ℝ (Fin 2)) :
    dist (planeEmb m x) (planeEmb m y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_add]
  simp [planeEmb, Fin.append_left, Fin.append_right]

/-- `mono_distance_of_unbounded` in `ℝⁿ`, `n ≥ 2`. -/
theorem mono_distance_of_unbounded_euclid {n : ℕ} (hn : 2 ≤ n) {k : ℕ} [NeZero k]
    (c : EuclideanSpace ℝ (Fin n) → Fin k)
    {S : Set ℝ} (hS : ∀ s ∈ S, 0 < s ∧ IsAlgebraic ℚ s) (hunb : ¬ BddAbove S) :
    ∃ s ∈ S, ∃ x y, dist x y = s ∧ c x = c y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  obtain ⟨s, hs, x, y, hxy, hc⟩ := mono_distance_of_unbounded (c ∘ planeEmb m) hS hunb
  exact ⟨s, hs, _, _, (dist_planeEmb m x y).trans hxy, hc⟩

theorem soifer_euclid {n : ℕ} (hn : 2 ≤ n) {k : ℕ} [NeZero k]
    (c : EuclideanSpace ℝ (Fin n) → Fin k) :
    ∃ N : ℕ, ∀ j ≥ N, ∃ x y, dist x y = (2 : ℝ) ^ j ∧ c x = c y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  obtain ⟨N, hN⟩ := soifer (c ∘ planeEmb m)
  exact ⟨N, fun j hj => by
    obtain ⟨x, y, hxy, hc⟩ := hN j hj
    exact ⟨_, _, (dist_planeEmb m x y).trans hxy, hc⟩⟩

theorem kahle_euclid {n : ℕ} (hn : 2 ≤ n) {k : ℕ} [NeZero k]
    (c : EuclideanSpace ℝ (Fin n) → Fin k) :
    ∃ N : ℕ, ∀ j ≥ N, ∃ x y, dist x y = (j.factorial : ℝ) ∧ c x = c y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  obtain ⟨N, hN⟩ := kahle (c ∘ planeEmb m)
  exact ⟨N, fun j hj => by
    obtain ⟨x, y, hxy, hc⟩ := hN j hj
    exact ⟨_, _, (dist_planeEmb m x y).trans hxy, hc⟩⟩

end
end OAI.Soifer
