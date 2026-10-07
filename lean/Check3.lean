import OAI.HN3.Corollary
open MeasureTheory

/-- Restated self-contained: any proper k-coloring of ℝ³ (modelled as ℂ × ℝ with the Euclidean
norm √(‖z‖² + t²)), with arbitrary color classes, gives k measurable, pairwise disjoint,
unit-distance-free sets covering ℝ³ up to a Lebesgue-null set. -/
theorem three_space_transfer {k : ℕ} [NeZero k] (c : ℂ × ℝ → Fin k)
    (hc : ∀ x y : ℂ × ℝ, ‖x.1 - y.1‖ ^ 2 + (x.2 - y.2) ^ 2 = 1 → c x ≠ c y) :
    ∃ A : Fin k → Set (ℂ × ℝ), (∀ i, MeasurableSet (A i)) ∧
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      volume (⋃ i, A i)ᶜ = 0 ∧
      ∀ i, ∀ x ∈ A i, ∀ y ∈ A i, ‖x.1 - y.1‖ ^ 2 + (x.2 - y.2) ^ 2 ≠ 1 :=
  OAI.HN3.proper_partition3 c hc

#print axioms three_space_transfer

open OAI.HN3 in
#check @no_six_coloring_of_density
open OAI.HN3 in
#print axioms no_six_coloring_of_density
