import OAI.HNN.Repair
open MeasureTheory OAI.HNN

#check @proper_of_conull_partition
#print axioms proper_of_conull_partition
#check @measurable_proper_of_conull_partition
#print axioms measurable_proper_of_conull_partition
#check @chromatic_eq_measurable_chromatic_set
#print axioms chromatic_eq_measurable_chromatic_set
#check @chromatic_eq_measurable_chromatic
#print axioms chromatic_eq_measurable_chromatic

/-- The plane: `χ(ℝ²) = χ_m(ℝ²)`. -/
example {k : ℕ} [NeZero k] :
    (∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, ∀ x y, dist x y = 1 → c x ≠ c y) ↔
      ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, (∀ i, NullMeasurableSet {x | c x = i} volume) ∧
        ∀ x y, dist x y = 1 → c x ≠ c y :=
  chromatic_eq_measurable_chromatic (le_refl 2)
