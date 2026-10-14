import OAI.HN3.Corollary
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

/-!
# A finite unit-distance graph in three-space that is not six-colorable

Compactness (de Bruijn–Erdős, `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`) turns
`no_six_coloring_of_density` into the existence of a finite set of points of `ℝ³` whose
unit-distance graph has no proper six-coloring.
-/

namespace OAI

noncomputable section
namespace HN3

lemma usq_neg (y : ℂ × ℝ) : usq (-y) = usq y := by simp [usq]

/-- The unit-distance graph of `ℂ × ℝ ≅ ℝ³`. -/
def unitGraph : SimpleGraph (ℂ × ℝ) where
  Adj x y := usq (x - y) = 1
  symm := ⟨fun x y h => by
    change usq (x - y) = 1 at h
    rwa [← neg_sub, usq_neg]⟩
  loopless := ⟨fun x h => by simp [usq] at h⟩

/-- Compactness: if every finite set of points has a proper `k`-coloring, so does all of `ℝ³`. -/
theorem coloring_of_finite {k : ℕ}
    (h : ∀ S : Finset (ℂ × ℝ), ∃ c : S → Fin k, ∀ x y : S, usq (x.1 - y.1) = 1 → c x ≠ c y) :
    ∃ c : ℂ × ℝ → Fin k, ∀ x y : ℂ × ℝ, usq (x - y) = 1 → c x ≠ c y := by
  have hom : Nonempty (unitGraph →g (⊤ : SimpleGraph (Fin k))) := by
    apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
    intro G' hG'
    let c := Classical.choose (h hG'.toFinset)
    have hc := Classical.choose_spec (h hG'.toFinset)
    refine ⟨fun v => c ⟨v.1, hG'.mem_toFinset.mpr v.2⟩, ?_⟩
    intro a b hab
    exact (SimpleGraph.top_adj _ _).mpr (hc _ _ (show usq (a.1 - b.1) = 1 from G'.adj_sub hab))
  obtain ⟨f⟩ := hom
  exact ⟨f, fun x y hxy => ((SimpleGraph.top_adj _ _).mp (f.map_rel (show unitGraph.Adj x y from hxy)))⟩

/-- **A finite 7-chromatic unit-distance graph exists in `ℝ³`** (non-constructively), given the
DeCorte–Oliveira–Vallentin density bound: some finite point set has no proper six-coloring. -/
theorem exists_finite_not_six_colorable (hDOV : DensityBound 0.1532996) :
    ∃ S : Finset (ℂ × ℝ), ¬ ∃ c : S → Fin 6, ∀ x y : S, usq (x.1 - y.1) = 1 → c x ≠ c y := by
  by_contra hne
  push Not at hne
  exact no_six_coloring_of_density hDOV (coloring_of_finite hne)

end HN3
end
end OAI
