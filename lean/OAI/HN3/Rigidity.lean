import OAI.HN3.Model

/-!
# Twisted rigidity and the plane step in three dimensions

`twisted_residual` upgrades OpenAI's `residual_fourier` by a commuting unitary through
polarization. In the three-dimensional label model it shows that projecting the color
indicators onto plane-continuous vectors preserves all correlations at algebraic unit vectors
whose horizontal component is nonzero.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HN3
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

section Abstract
variable {A H : Type*} [AddCommGroup A] [TopologicalSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))

/-- A bounded operator commuting with the representation preserves its continuous vectors. -/
lemma comm_mem_space (Y : H →L[ℂ] H) (hY : ∀ a w, Y (op U a w) = op U a (Y w))
    {v : H} (hv : v ∈ space U) : Y v ∈ space U := by
  have ht := (Y.continuous.tendsto v).comp hv
  change Tendsto (fun a => op U a (Y v)) (𝓝 0) (𝓝 (Y v))
  simpa only [Function.comp_def, hY] using ht

lemma star_apply_self (Y : unitary (H →L[ℂ] H)) (x : H) :
    ((star Y : unitary _) : H →L[ℂ] H) ((Y : H →L[ℂ] H) x) = x := by
  have := congrArg (fun A : unitary (H →L[ℂ] H) => (A : H →L[ℂ] H) x) (Unitary.star_mul_self Y)
  exact this

lemma apply_star_self (Y : unitary (H →L[ℂ] H)) (x : H) :
    (Y : H →L[ℂ] H) (((star Y : unitary _) : H →L[ℂ] H) x) = x := by
  have := congrArg (fun A : unitary (H →L[ℂ] H) => (A : H →L[ℂ] H) x) (Unitary.mul_star_self Y)
  exact this

/-- A unitary commuting with the representation preserves the orthogonal complement. -/
lemma comm_mem_orthogonal (Y : unitary (H →L[ℂ] H))
    (hY : ∀ a w, (Y : H →L[ℂ] H) (op U a w) = op U a ((Y : H →L[ℂ] H) w))
    {v : H} (hv : v ∈ (space U)ᗮ) : (Y : H →L[ℂ] H) v ∈ (space U)ᗮ := by
  have hYs : ∀ a w, ((star Y : unitary _) : H →L[ℂ] H) (op U a w) =
      op U a (((star Y : unitary _) : H →L[ℂ] H) w) := by
    intro a w
    have hinj : Function.Injective (Y : H →L[ℂ] H) := by
      intro x y hxy
      have := congrArg ((star Y : unitary _) : H →L[ℂ] H) hxy
      rwa [star_apply_self, star_apply_self] at this
    apply hinj
    rw [hY, apply_star_self, apply_star_self]
  rw [Submodule.mem_orthogonal'] at hv ⊢
  intro w hw
  have hh := hv _ (comm_mem_space U _ hYs hw)
  have he := Unitary.inner_map_map Y v (((star Y : unitary _) : H →L[ℂ] H) w)
  rw [apply_star_self] at he
  exact he.trans hh

end Abstract

section Twisted
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (W : K → unitary (H →L[ℂ] H))
  (hcov : ∀ k z w, (W k : H →L[ℂ] H) (ContinuousVectors.op U z w) =
    ContinuousVectors.op U ((kCoeff k) * z) ((W k : H →L[ℂ] H) w))
include hcov

/-- Rigidity survives composition with a unitary commuting with translations and rotations. -/
lemma twisted_residual (Y : unitary (H →L[ℂ] H))
    (hYU : ∀ z w, (Y : H →L[ℂ] H) (op U z w) = op U z ((Y : H →L[ℂ] H) w))
    (hYW : ∀ k w, (Y : H →L[ℂ] H) ((W k : H →L[ℂ] H) w) = (W k : H →L[ℂ] H) ((Y : H →L[ℂ] H) w))
    (v : H) (hv : v ∈ (ContinuousVectors.space U)ᗮ)
    (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) (z : E) (hz : z ≠ 0) :
    ⟪v, op U z ((Y : H →L[ℂ] H) v)⟫_ℂ = 0 := by
  set y := (Y : H →L[ℂ] H) v with hy
  have hyo : y ∈ (ContinuousVectors.space U)ᗮ := comm_mem_orthogonal U Y hYU hv
  have hyf : ∀ k, (W k : H →L[ℂ] H) y = y := fun k => by rw [hy, ← hYW, hfix]
  have key : ∀ s : ℂ, ⟪v + s • y, op U z (v + s • y)⟫_ℂ = 0 := fun s =>
    residual_fourier U W hcov (v + s • y)
      (Submodule.add_mem _ hv (Submodule.smul_mem _ s hyo))
      (fun k => by rw [map_add, map_smul, hfix, hyf]) z hz
  have h0 := residual_fourier U W hcov v hv hfix z hz
  have h1 := residual_fourier U W hcov y hyo hyf z hz
  have expand : ∀ s : ℂ, ⟪v + s • y, op U z (v + s • y)⟫_ℂ =
      ⟪v, op U z v⟫_ℂ + s * ⟪v, op U z y⟫_ℂ + conj s * ⟪y, op U z v⟫_ℂ
        + conj s * s * ⟪y, op U z y⟫_ℂ := by
    intro s
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right]
    ring
  have e1 := key 1
  have e2 := key Complex.I
  rw [expand, h0, h1] at e1 e2
  simp only [map_one, one_mul, zero_add, mul_zero, add_zero, Complex.conj_I] at e1 e2
  have : ⟪v, op U z y⟫_ℂ = 0 := by
    have hb : ⟪y, op U z v⟫_ℂ = -⟪v, op U z y⟫_ℂ := by linear_combination e1
    rw [hb] at e2
    have : (2 * Complex.I) * ⟪v, op U z y⟫_ℂ = 0 := by linear_combination e2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by simp [Complex.I_ne_zero])
    · exact h
  exact this

end Twisted

/-! ## The plane step in the three-dimensional model -/

variable (k : ℕ) (ω : Space k)

def colorValue (i : Fin k) (η : Space k) : ℂ := if η.val 0 = i then 1 else 0

lemma color_memLp (i : Fin k) : MemLp (colorValue k i) 2 (measure k ω) := by
  refine MemLp.of_bound ?_ 1 ?_
  · apply Measurable.aestronglyMeasurable
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton i).preimage (show Measurable (fun η : Space k => η.val 0) from
      ((continuous_apply (0 : V)).comp continuous_subtype_val).measurable)
  · exact .of_forall fun η => by dsimp [colorValue]; split_ifs <;> simp

abbrev colorVector (i : Fin k) : Hilbert k ω := (color_memLp k ω i).toLp (colorValue k i)

lemma color_ae (i : Fin k) : colorVector k ω i =ᵐ[measure k ω] colorValue k i :=
  (color_memLp k ω i).coeFn_toLp

lemma rmap_zero (b : K) : rmap b 0 = 0 := by simp [rmap]

lemma color_rotation_fixed (i : Fin k) (b : K) : R k ω b (colorVector k ω i) = colorVector k ω i := by
  change Lp.compMeasurePreserving (rotate k b) (rotate_preserving k ω b) _ = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (colorVector k ω i) (rotate_preserving k ω b),
    (rotate_preserving k ω b).quasiMeasurePreserving.ae (color_ae k ω i), color_ae k ω i]
    with η h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, colorValue, rotate_apply, rmap_zero]

lemma sq_neg (x : V) : sq (-x) = sq x := by simp [sq]

/-- Properness: zero correlation of each color at every algebraic unit vector. -/
lemma color_unit_correlation (i : Fin k) (x : V) (hx : sq x = 1) :
    ⟪colorVector k ω i, T k ω x (colorVector k ω i)⟫_ℂ = 0 := by
  rw [translation_apply, L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [color_ae k ω i,
    Lp.coeFn_compMeasurePreserving (colorVector k ω i) (trans_preserving k ω x),
    (trans_preserving k ω x).quasiMeasurePreserving.ae (color_ae k ω i)] with η h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, colorValue, trans_apply, zero_add]
  have hp : η.val 0 ≠ η.val x := η.property 0 x (by rw [zero_sub, sq_neg, hx])
  by_cases hi : η.val 0 = i
  · have hj : η.val x ≠ i := fun h => hp (hi.trans h.symm)
    simp [hi, hj]
  · simp [hi]

instance plane_complete : CompleteSpace (space (A := E) (planeRep k ω)) :=
  (isClosed_space (A := E) (planeRep k ω)).completeSpace_coe

/-- Projection onto vectors continuous under horizontal translations. -/
abbrev PE : Hilbert k ω →L[ℂ] Hilbert k ω := (space (A := E) (planeRep k ω)).starProjection

lemma T_comm_plane (x : V) (z : E) (w : Hilbert k ω) :
    T k ω x (op (planeRep k ω) z w) = op (planeRep k ω) z (T k ω x w) := by
  rw [planeRep_op, planeRep_op, T_comm]

lemma PE_rotation_fixed (v : Hilbert k ω) (b : K) (hv : R k ω b v = v) :
    R k ω b (PE k ω v) = PE k ω v :=
  projection_covariance_fixed (planeRep k ω) (rotation k ω b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (plane_covariance k ω b) v hv

/-- Plane step: the horizontally continuous projection of a color indicator keeps zero
correlation at every algebraic unit vector with nonzero horizontal component. -/
theorem plane_projection_unit_correlation (i : Fin k) (x : V) (hx : sq x = 1) (hz : x.1 ≠ 0) :
    ⟪PE k ω (colorVector k ω i), T k ω x (PE k ω (colorVector k ω i))⟫_ℂ = 0 := by
  set f := colorVector k ω i
  set g := PE k ω f
  set b := f - g
  have hg : g ∈ space (A := E) (planeRep k ω) := (space (A := E) (planeRep k ω)).starProjection_apply_mem f
  have hb : b ∈ (space (A := E) (planeRep k ω))ᗮ :=
    (space (A := E) (planeRep k ω)).sub_starProjection_mem_orthogonal f
  have hbfix : ∀ c, R k ω c b = b := fun c => by
    simp only [b, map_sub, color_rotation_fixed, g, PE_rotation_fixed k ω f c (color_rotation_fixed k ω i c), f]
  -- the vertical translation commutes with plane translations and rotations
  let Y := translation k ω (0, x.2)
  have hYU : ∀ z w, (Y : Hilbert k ω →L[ℂ] Hilbert k ω) (op (planeRep k ω) z w) =
      op (planeRep k ω) z ((Y : Hilbert k ω →L[ℂ] Hilbert k ω) w) := fun z w => T_comm_plane k ω _ z w
  have hYW : ∀ c w, (Y : Hilbert k ω →L[ℂ] Hilbert k ω) (R k ω c w) =
      R k ω c ((Y : Hilbert k ω →L[ℂ] Hilbert k ω) w) := fun c w => (R_line k ω c x.2 w).symm
  have hsplit : ∀ w, T k ω x w = op (planeRep k ω) x.1 ((Y : Hilbert k ω →L[ℂ] Hilbert k ω) w) := by
    intro w
    rw [planeRep_op]
    change T k ω x w = T k ω (x.1, 0) (T k ω (0, x.2) w)
    rw [← T_add]
    simp
  have hbb : ⟪b, T k ω x b⟫_ℂ = 0 := by
    rw [hsplit]
    exact twisted_residual (planeRep k ω) (rotation k ω) (plane_covariance k ω) Y hYU hYW b hb
      hbfix x.1 hz
  have hTx : ∀ a w, T k ω x (op (planeRep k ω) a w) = op (planeRep k ω) a (T k ω x w) :=
    fun a w => T_comm_plane k ω x a w
  have h1 : ⟪g, T k ω x b⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp (comm_mem_orthogonal (planeRep k ω) (translation k ω x) hTx hb) g hg
  have h2 : ⟪b, T k ω x g⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).mp hb _ (comm_mem_space (planeRep k ω) _ hTx hg)
  have hf : f = g + b := by simp [b]
  have h0 : ⟪f, T k ω x f⟫_ℂ = 0 := color_unit_correlation k ω i x hx
  rw [hf, map_add, inner_add_left, inner_add_right, inner_add_right, h1, h2, hbb] at h0
  simpa using h0

end HN3
end
end OAI
