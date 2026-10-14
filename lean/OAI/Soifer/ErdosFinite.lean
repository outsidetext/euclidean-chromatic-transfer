import OAI.Soifer.Erdos706
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

/-!
# Erdős #706 for finite point sets

`L(r)` is defined through finite point sets `P ⊂ ℝ²`. Compactness (de Bruijn–Erdős,
`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`) applied to the distance-in-`D` graph
turns `lacunary_no_coloring` into a finite point set with no `⌊C·K^e⌋`-colouring.
-/

namespace OAI.Soifer

noncomputable section

/-- The graph on `ℝ²` with edges at distances in `D` (`D` of positive reals). -/
def distGraph (D : Finset ℝ) : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := dist x y ∈ D ∧ x ≠ y
  symm := ⟨fun x y h => by
    change dist x y ∈ D ∧ x ≠ y at h
    exact ⟨by rw [dist_comm]; exact h.1, h.2.symm⟩⟩
  loopless := ⟨fun x h => h.2 rfl⟩

/-- Compactness: if every finite point set has a `D`-avoiding `k`-colouring, so does `ℝ²`. -/
theorem coloring_of_finite_dist {D : Finset ℝ} (hD : ∀ d ∈ D, 0 < d) {k : ℕ}
    (h : ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
      ∃ c : S → Fin k, ∀ x y : S, dist x.1 y.1 ∈ D → c x ≠ c y) :
    ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, ∀ x y, dist x y ∈ D → c x ≠ c y := by
  have hom : Nonempty (distGraph D →g (⊤ : SimpleGraph (Fin k))) := by
    apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
    intro G' hG'
    let c := Classical.choose (h hG'.toFinset)
    have hc := Classical.choose_spec (h hG'.toFinset)
    refine ⟨fun v => c ⟨v.1, hG'.mem_toFinset.mpr v.2⟩, ?_⟩
    intro a b hab
    exact (SimpleGraph.top_adj _ _).mpr (hc _ _ (G'.adj_sub hab).1)
  obtain ⟨f⟩ := hom
  refine ⟨f, fun x y hxy => ?_⟩
  have hne : x ≠ y := by
    rintro rfl
    have := hD _ hxy
    rw [dist_self] at this
    exact lt_irrefl _ this
  exact (SimpleGraph.top_adj _ _).mp (f.map_rel (show (distGraph D).Adj x y from ⟨hxy, hne⟩))

lemma exists_K_exp_gt (C : ℝ) (e : ℕ) : ∃ K : ℕ, C * (K : ℝ) ^ e < 4 / 9 * (3 / 2 : ℝ) ^ K := by
  have hC : 0 < |C| + 1 := by positivity
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 3 / 2)
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < 4 / (9 * (|C| + 1))))).exists
  refine ⟨K, ?_⟩
  have hpow : (0 : ℝ) < (3 / 2) ^ K := by positivity
  have hKe : (0 : ℝ) ≤ (K : ℝ) ^ e := by positivity
  rw [div_lt_div_iff₀ hpow (by positivity)] at hK
  have h1 : C * (K : ℝ) ^ e ≤ (|C| + 1) * (K : ℝ) ^ e :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hKe
  nlinarith

/-- **Erdős #706, finite form.** For every `C` and `e` there are `K`, a `K`-element set `D` of
positive algebraic reals and a finite `P ⊂ ℝ²` such that the distance-in-`D` graph on `P` has
no proper colouring with at most `C·K^e` colours. -/
theorem erdos706_finite (C : ℝ) (e : ℕ) :
    ∃ K : ℕ, ∃ D : Finset ℝ, D.card = K ∧ (∀ d ∈ D, 0 < d ∧ IsAlgebraic ℚ d) ∧
      ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), ∀ k : ℕ, (k : ℝ) ≤ C * (K : ℝ) ^ e →
        ¬ ∃ c : P → Fin k, ∀ x y : P, dist x.1 y.1 ∈ D → c x ≠ c y := by
  obtain ⟨K, hK⟩ := exists_K_exp_gt C e
  set k0 : ℕ := ⌊C * (K : ℝ) ^ e⌋₊ with hk0
  have hk0lt : (k0 : ℝ) < 4 / 9 * (3 / 2 : ℝ) ^ K := by
    rcases le_or_gt 0 (C * (K : ℝ) ^ e) with h | h
    · exact lt_of_le_of_lt (Nat.floor_le h) hK
    · rw [hk0, Nat.floor_eq_zero.mpr (by linarith)]
      push_cast
      positivity
  have hfin : ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      ¬ ∃ c : P → Fin k0, ∀ x y : P, dist x.1 y.1 ∈ lacD K → c x ≠ c y := by
    by_contra hne
    push Not at hne
    exact lacunary_no_coloring K k0 hk0lt
      (coloring_of_finite_dist (fun d hd => (lacD_pos_alg K d hd).1) hne)
  obtain ⟨P, hP⟩ := hfin
  refine ⟨K, lacD K, lacD_card K, lacD_pos_alg K, P, fun k hk => ?_⟩
  rintro ⟨c, hc⟩
  have hkk : k ≤ k0 := Nat.le_floor hk
  exact hP ⟨fun x => Fin.castLE hkk (c x), fun x y hxy h =>
    hc x y hxy (Fin.castLE_injective hkk h)⟩

end
end OAI.Soifer
