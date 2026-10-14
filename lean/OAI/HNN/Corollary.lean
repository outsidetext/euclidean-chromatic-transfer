import OAI.HNN.Euclid
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

/-!
# Chromatic number of `ℝⁿ` from density bounds

`DensityBoundE n δ`: every measurable subset of `ℝⁿ` without two points at distance one has
upper density at most `δ` along the cubes `[-T,T]ⁿ`. With the transfer theorem, a proper
`k`-colouring forces `1 ≤ k δ`. The DeCorte–Oliveira–Vallentin bounds (Math. Program. 2022,
Table 2) then give lower bounds for `χ(ℝⁿ)`, `3 ≤ n ≤ 8`, and compactness (de Bruijn–Erdős)
gives finite unit-distance graphs attaining them.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace HNN

variable {n : ℕ}

/-- The cube `[-T,T]ⁿ`. -/
def cube (n : ℕ) (T : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, |x i| ≤ T}

lemma cube_measurable (T : ℝ) : MeasurableSet (cube n T) := by
  apply IsClosed.measurableSet
  have : cube n T = ⋂ i, {x : EuclideanSpace ℝ (Fin n) | |x i| ≤ T} := by
    ext x; simp [cube]
  rw [this]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  exact continuous_abs.comp ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _))

lemma cube_finite (T : ℝ) : volume (cube n T) ≠ ⊤ := by
  have hK : IsCompact (WithLp.toLp 2 '' (Set.pi univ fun _ : Fin n => Icc (-T) T)) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).image (PiLp.continuous_toLp 2 _)
  refine ne_top_of_le_ne_top hK.measure_ne_top (measure_mono fun x hx => ?_)
  exact ⟨x.ofLp, fun i _ => abs_le.mp (hx i), by simp⟩

lemma cube_pos {T : ℝ} (hT : 0 < T) : volume (cube n T) ≠ 0 := by
  apply (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hT).ne' ∘
    measure_mono_null ?_
  intro x hx i
  rw [Metric.mem_ball, dist_zero_right] at hx
  have := PiLp.norm_apply_le x i
  rw [Real.norm_eq_abs] at this
  exact (this.trans hx.le)

/-- Every measurable unit-distance-free set has upper cube density at most `δ`. -/
def DensityBoundE (n : ℕ) (δ : ℝ) : Prop :=
  ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S → (∀ x ∈ S, ∀ y ∈ S, dist x y ≠ 1) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop,
      volume (S ∩ cube n T) ≤ ENNReal.ofReal (δ + ε) * volume (cube n T)

/-- A density bound bounds the number of colours of any proper colouring of `ℝⁿ`. -/
theorem colors_ge_of_densityE {n : ℕ} (hn : 2 ≤ n) {δ : ℝ} (h : DensityBoundE n δ) {k : ℕ}
    [NeZero k] (c : EuclideanSpace ℝ (Fin n) → Fin k) (hc : ∀ x y, dist x y = 1 → c x ≠ c y) :
    1 ≤ (k : ℝ) * δ := by
  obtain ⟨A, hAm, hAd, hAn, hAu⟩ := euclidean_transfer hn c hc
  by_contra hlt
  push Not at hlt
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  set ε := (1 - k * δ) / (2 * k) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  have hkε : (k : ℝ) * (δ + ε) < 1 := by
    have : (k : ℝ) * ε = (1 - k * δ) / 2 := by
      rw [hε]; field_simp
    rw [mul_add, this]
    linarith
  have hev : ∀ᶠ T in atTop, ∀ i, volume (A i ∩ cube n T) ≤
      ENNReal.ofReal (δ + ε) * volume (cube n T) :=
    eventually_all.mpr fun i => h (A i) (hAm i) (hAu i) ε hεpos
  obtain ⟨T, hT, hT1⟩ := (hev.and (eventually_gt_atTop 0)).exists
  have hsum : volume (cube n T) = ∑ i, volume (A i ∩ cube n T) := by
    have h1 : volume (cube n T) = volume ((⋃ i, A i) ∩ cube n T) := by
      apply le_antisymm _ (measure_mono inter_subset_right)
      calc volume (cube n T) ≤ volume (((⋃ i, A i) ∩ cube n T) ∪ (⋃ i, A i)ᶜ) :=
            measure_mono (fun x hx => by
              by_cases h : x ∈ ⋃ i, A i
              · exact Or.inl ⟨h, hx⟩
              · exact Or.inr h)
        _ ≤ volume ((⋃ i, A i) ∩ cube n T) + volume (⋃ i, A i)ᶜ := measure_union_le _ _
        _ = volume ((⋃ i, A i) ∩ cube n T) := by rw [hAn, add_zero]
    rw [h1, iUnion_inter, measure_iUnion]
    · rw [tsum_fintype]
    · intro i j hij
      exact (hAd hij).mono inter_subset_left inter_subset_left
    · exact fun i => (hAm i).inter (cube_measurable T)
  have hle : volume (cube n T) ≤ (k : ENNReal) * (ENNReal.ofReal (δ + ε) * volume (cube n T)) := by
    calc volume (cube n T) = ∑ i, volume (A i ∩ cube n T) := hsum
      _ ≤ ∑ _i : Fin k, ENNReal.ofReal (δ + ε) * volume (cube n T) :=
          Finset.sum_le_sum fun i _ => hT i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfin := cube_finite (n := n) T
  have hpos := cube_pos (n := n) hT1
  rw [← mul_assoc] at hle
  have hc1 : (k : ENNReal) * ENNReal.ofReal (δ + ε) < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact (ENNReal.ofReal_lt_one).mpr hkε
  have h' := ENNReal.mul_lt_mul_right hpos hfin hc1
  rw [mul_one, mul_comm] at h'
  exact absurd hle (not_le.mpr h')

/-- No proper `k`-colouring of `ℝⁿ` when `k δ < 1`. -/
theorem no_coloring_of_densityE (hn : 2 ≤ n) {δ : ℝ} (h : DensityBoundE n δ) (k : ℕ) [NeZero k]
    (hk : (k : ℝ) * δ < 1) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin n) → Fin k, ∀ x y, dist x y = 1 → c x ≠ c y := by
  rintro ⟨c, hc⟩
  exact absurd (colors_ge_of_densityE hn h c hc) (not_le.mpr hk)

/-! ### DeCorte–Oliveira–Vallentin bounds (conditional on the published density bounds) -/

theorem no_6_coloring_R3 (h : DensityBoundE 3 0.1532996) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 3) → Fin 6, ∀ x y, dist x y = 1 → c x ≠ c y :=
  no_coloring_of_densityE (by norm_num) h 6 (by norm_num)

theorem no_10_coloring_R4 (h : DensityBoundE 4 0.0985701) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 4) → Fin 10, ∀ x y, dist x y = 1 → c x ≠ c y :=
  no_coloring_of_densityE (by norm_num) h 10 (by norm_num)

theorem no_16_coloring_R5 (h : DensityBoundE 5 0.0624485) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 5) → Fin 16, ∀ x y, dist x y = 1 → c x ≠ c y :=
  no_coloring_of_densityE (by norm_num) h 16 (by norm_num)

theorem no_22_coloring_R6 (h : DensityBoundE 6 0.0450325) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 6) → Fin 22, ∀ x y, dist x y = 1 → c x ≠ c y :=
  no_coloring_of_densityE (by norm_num) h 22 (by norm_num)

theorem no_38_coloring_R7 (h : DensityBoundE 7 0.0260782) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 7) → Fin 38, ∀ x y, dist x y = 1 → c x ≠ c y :=
  no_coloring_of_densityE (by norm_num) h 38 (by norm_num)

theorem no_52_coloring_R8 (h : DensityBoundE 8 0.0190945) :
    ¬ ∃ c : EuclideanSpace ℝ (Fin 8) → Fin 52, ∀ x y, dist x y = 1 → c x ≠ c y :=
  no_coloring_of_densityE (by norm_num) h 52 (by norm_num)

/-! ### Finite unit-distance graphs (de Bruijn–Erdős) -/

/-- The unit-distance graph of `ℝⁿ`. -/
def unitGraphE (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := dist x y = 1
  symm := ⟨fun x y h => by
    change dist x y = 1 at h
    rwa [dist_comm]⟩
  loopless := ⟨fun x h => by simp at h⟩

/-- Compactness: if every finite point set has a proper `k`-colouring, so does `ℝⁿ`. -/
theorem coloring_of_finiteE {k : ℕ}
    (h : ∀ S : Finset (EuclideanSpace ℝ (Fin n)),
      ∃ c : S → Fin k, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y) :
    ∃ c : EuclideanSpace ℝ (Fin n) → Fin k, ∀ x y, dist x y = 1 → c x ≠ c y := by
  have hom : Nonempty (unitGraphE n →g (⊤ : SimpleGraph (Fin k))) := by
    apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
    intro G' hG'
    let c := Classical.choose (h hG'.toFinset)
    have hc := Classical.choose_spec (h hG'.toFinset)
    refine ⟨fun v => c ⟨v.1, hG'.mem_toFinset.mpr v.2⟩, ?_⟩
    intro a b hab
    exact (SimpleGraph.top_adj _ _).mpr (hc _ _ (show dist a.1 b.1 = 1 from G'.adj_sub hab))
  obtain ⟨f⟩ := hom
  exact ⟨f, fun x y hxy =>
    ((SimpleGraph.top_adj _ _).mp (f.map_rel (show (unitGraphE n).Adj x y from hxy)))⟩

/-- A density bound with `k δ < 1` gives a finite unit-distance graph in `ℝⁿ` that is not
`k`-colourable. -/
theorem exists_finite_not_colorableE (hn : 2 ≤ n) {δ : ℝ} (h : DensityBoundE n δ) (k : ℕ)
    [NeZero k] (hk : (k : ℝ) * δ < 1) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin n)),
      ¬ ∃ c : S → Fin k, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y := by
  by_contra hne
  push Not at hne
  exact no_coloring_of_densityE hn h k hk (coloring_of_finiteE hne)

theorem exists_finite_R3 (h : DensityBoundE 3 0.1532996) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 3)),
      ¬ ∃ c : S → Fin 6, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y :=
  exists_finite_not_colorableE (by norm_num) h 6 (by norm_num)

theorem exists_finite_R4 (h : DensityBoundE 4 0.0985701) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 4)),
      ¬ ∃ c : S → Fin 10, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y :=
  exists_finite_not_colorableE (by norm_num) h 10 (by norm_num)

theorem exists_finite_R5 (h : DensityBoundE 5 0.0624485) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 5)),
      ¬ ∃ c : S → Fin 16, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y :=
  exists_finite_not_colorableE (by norm_num) h 16 (by norm_num)

theorem exists_finite_R6 (h : DensityBoundE 6 0.0450325) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 6)),
      ¬ ∃ c : S → Fin 22, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y :=
  exists_finite_not_colorableE (by norm_num) h 22 (by norm_num)

theorem exists_finite_R7 (h : DensityBoundE 7 0.0260782) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 7)),
      ¬ ∃ c : S → Fin 38, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y :=
  exists_finite_not_colorableE (by norm_num) h 38 (by norm_num)

theorem exists_finite_R8 (h : DensityBoundE 8 0.0190945) :
    ∃ S : Finset (EuclideanSpace ℝ (Fin 8)),
      ¬ ∃ c : S → Fin 52, ∀ x y : S, dist x.1 y.1 = 1 → c x ≠ c y :=
  exists_finite_not_colorableE (by norm_num) h 52 (by norm_num)

end HNN
end
end OAI
