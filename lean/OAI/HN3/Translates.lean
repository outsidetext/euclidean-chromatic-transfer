import OAI.HN3.IndepFolner

/-!
# Monochromatic translates from density bounds

If `δ` bounds the density of measurable unit-distance-free subsets of `ℝ³` and `|X| δ < 1`,
then for *any* (not necessarily measurable) unit-distance-free set `red`, some translate of `X`
avoids `red`. Proof: take a finite `S` with independence ratio at most `δ + ε`
(`finite_ratio_of_density`); for each `x ∈ X` the set `{s ∈ S : s + x ∈ red}` is
unit-distance-free, so a union bound over `x ∈ X` leaves some `s ∈ S` with `s + X ∩ red = ∅`.

Corollaries with the DeCorte–Oliveira–Vallentin bound `DensityBound 0.1532996`
(`6 · 0.1532996 < 1`):

* `erdos188_R3`: in every red/blue colouring of `ℝ³` with no two red points at distance one,
  every unit vector `u` admits a blue progression `x, x + u, …, x + 5u`;
* `erdos214_R3`: in every red/blue colouring with no two blue points at distance one, every
  6-point set has an entirely red translate.
-/

namespace OAI

noncomputable section
open Finset

namespace HN3
namespace Indep

/-- **Translates avoiding a unit-distance-free set.** -/
theorem blue_translate_of_density {δ : ℝ} (hδ : DensityBound δ) (X : Finset (ℂ × ℝ))
    (hX : (X.card : ℝ) * δ < 1) (red : Set (ℂ × ℝ))
    (hred : ∀ x ∈ red, ∀ y ∈ red, usq (x - y) ≠ 1) :
    ∃ v : ℂ × ℝ, ∀ x ∈ X, v + x ∉ red := by
  classical
  set n : ℝ := (X.card : ℝ) with hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  set ε : ℝ := (1 - n * δ) / (2 * (n + 1)) with hε
  have hεpos : 0 < ε := by
    rw [hε]; apply div_pos <;> linarith
  have hnε : n * (δ + ε) < 1 := by
    have h1 : ε * (2 * (n + 1)) = 1 - n * δ := by
      rw [hε]; field_simp
    nlinarith
  obtain ⟨S, hS, hSI⟩ := finite_ratio_of_density hδ hεpos
  -- the bad set for each `x`
  have hbad : ∀ x ∈ X, ((S.filter fun s => s + x ∈ red).card : ℝ) ≤ (δ + ε) * S.card := by
    intro x _
    refine hSI _ (filter_subset _ _) ?_
    intro a ha b hb
    simp only [mem_filter] at ha hb
    have := hred _ ha.2 _ hb.2
    simpa [add_sub_add_right_eq_sub] using this
  set B := X.biUnion fun x => S.filter fun s => s + x ∈ red with hB
  have hBcard : (B.card : ℝ) < S.card := by
    have h1 : (B.card : ℝ) ≤ ∑ x ∈ X, ((S.filter fun s => s + x ∈ red).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    have h2 : ∑ x ∈ X, ((S.filter fun s => s + x ∈ red).card : ℝ) ≤
        ∑ _x ∈ X, (δ + ε) * S.card := sum_le_sum hbad
    rw [sum_const, nsmul_eq_mul] at h2
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have : n * ((δ + ε) * S.card) < S.card := by
      rw [← mul_assoc]; nlinarith
    linarith
  have hBS : B ⊆ S := by
    intro s hs
    simp only [hB, mem_biUnion, mem_filter] at hs
    obtain ⟨_, _, h, _⟩ := hs
    exact h
  have hne : B ≠ S := by
    intro h; rw [h] at hBcard; exact lt_irrefl _ hBcard
  obtain ⟨s, hsS, hsB⟩ := exists_of_ssubset (hBS.ssubset_of_ne hne)
  refine ⟨s, fun x hx hsx => hsB ?_⟩
  simp only [hB, mem_biUnion, mem_filter]
  exact ⟨x, hx, hsS, hsx⟩

/-- **Erdős problem 188 in `ℝ³` (6-term case).** In every red/blue colouring of `ℝ³` in which no
two red points are at distance one, every unit vector `u` admits a blue unit-step progression
`x, x + u, …, x + 5 u`. -/
theorem erdos188_R3 (hDOV : DensityBound 0.1532996) (red : Set (ℂ × ℝ))
    (hred : ∀ x ∈ red, ∀ y ∈ red, usq (x - y) ≠ 1) (u : ℂ × ℝ) (_hu : usq u = 1) :
    ∃ x : ℂ × ℝ, ∀ j ∈ range 6, x + j • u ∈ redᶜ := by
  classical
  have hX : (((range 6).image fun j : ℕ => j • u).card : ℝ) * 0.1532996 < 1 := by
    have : ((range 6).image fun j : ℕ => j • u).card ≤ 6 :=
      card_image_le.trans (by simp)
    have : (((range 6).image fun j : ℕ => j • u).card : ℝ) ≤ 6 := by exact_mod_cast this
    nlinarith
  obtain ⟨v, hv⟩ := blue_translate_of_density hDOV _ hX red hred
  exact ⟨v, fun j hj => hv _ (mem_image_of_mem _ hj)⟩

/-- **Erdős problem 214 in `ℝ³` (6-point case).** In every red/blue colouring of `ℝ³` in which no
two blue points are at distance one, every set of at most 6 points has an entirely red
translate. -/
theorem erdos214_R3 (hDOV : DensityBound 0.1532996) (red : Set (ℂ × ℝ))
    (hblue : ∀ x ∈ redᶜ, ∀ y ∈ redᶜ, usq (x - y) ≠ 1) (X : Finset (ℂ × ℝ))
    (hX : X.card ≤ 6) :
    ∃ v : ℂ × ℝ, ∀ x ∈ X, v + x ∈ red := by
  have hX' : (X.card : ℝ) * 0.1532996 < 1 := by
    have : (X.card : ℝ) ≤ 6 := by exact_mod_cast hX
    nlinarith
  obtain ⟨v, hv⟩ := blue_translate_of_density hDOV X hX' redᶜ hblue
  exact ⟨v, fun x hx => not_not.mp (hv x hx)⟩

end Indep
end HN3
end
end OAI
