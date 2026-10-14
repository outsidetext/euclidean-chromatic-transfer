import OAI.HNN.Ext

/-!
# Generic algebraic points are dense in spheres of algebraic radius

For an algebraic radius `d > 0`, the vectors `u ∈ E^m` with all components nonzero and
`∑ ‖u_j‖² = d²` are dense in the sphere of radius `d` of `ℂ^m`: approximate by any point of
`(E \ {0})^m` and rescale; the rescaling factor is algebraic since square roots of real
algebraic numbers are algebraic.
-/

namespace OAI

noncomputable section
open Filter Topology Set
namespace HNN
open PlaneFiveColor.Spectral

variable {m : ℕ}

/-- Squared Euclidean norm on `ℂ^m`. -/
def nsq (z : Fin m → ℂ) : ℝ := ∑ j, ‖z j‖ ^ 2

lemma nsq_nonneg (z : Fin m → ℂ) : 0 ≤ nsq z := Finset.sum_nonneg fun _ _ => by positivity

lemma nsq_continuous : Continuous (nsq (m := m)) := by unfold nsq; fun_prop

lemma nsq_smul (c : ℂ) (z : Fin m → ℂ) : nsq (c • z) = ‖c‖ ^ 2 * nsq z := by
  simp [nsq, mul_pow, Finset.mul_sum]

lemma alg_complex {x : ℝ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (x : ℂ) := by
  have := h.algHom (Complex.ofRealAm.restrictScalars ℚ)
  simpa using this

lemma nsq_mem (u : Fin m → E) : ((nsq (embP u) : ℝ) : ℂ) ∈ E := by
  unfold nsq embP
  push_cast
  exact sum_mem fun j _ => pow_mem (mem_algebraicClosure_iff.mpr (algebraic_norm (u j))) 2

lemma sqrt_mem {x : ℝ} (hx : 0 ≤ x) (h : (x : ℂ) ∈ E) : ((Real.sqrt x : ℝ) : ℂ) ∈ E := by
  apply mem_algebraicClosure_iff.mpr
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  rw [← Complex.ofReal_pow, Real.sq_sqrt hx]
  exact mem_algebraicClosure_iff.mp h

/-- Rescaling to the sphere of radius `d`. -/
def nrm (d : ℝ) (y : Fin m → ℂ) : Fin m → ℂ := ((d / Real.sqrt (nsq y) : ℝ) : ℂ) • y

lemma nrm_nsq {d : ℝ} {y : Fin m → ℂ} (hy : nsq y ≠ 0) : nsq (nrm d y) = d ^ 2 := by
  have hp : 0 < nsq y := lt_of_le_of_ne (nsq_nonneg y) (Ne.symm hy)
  rw [nrm, nsq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt hp.le]
  field_simp

theorem sphere_closure {d : ℝ} (hdA : IsAlgebraic ℚ d) (hd0 : 0 < d) {z : Fin m → ℂ}
    (hz : nsq z = d ^ 2) :
    z ∈ closure {y | ∃ u : Fin m → E, (∀ j, u j ≠ 0) ∧ nsq (embP u) = d ^ 2 ∧ embP u = y} := by
  have hz0 : nsq z ≠ 0 := by rw [hz]; positivity
  have hsq : Real.sqrt (nsq z) ≠ 0 := by
    rw [hz, Real.sqrt_sq hd0.le]; exact hd0.ne'
  have hN : ContinuousAt (nrm d) z := by
    unfold nrm
    have h1 : ContinuousAt (fun y : Fin m → ℂ => ((d / Real.sqrt (nsq y) : ℝ) : ℂ)) z :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div (Real.continuous_sqrt.comp nsq_continuous).continuousAt hsq)
    exact h1.smul continuousAt_id
  have hNz : nrm d z = z := by
    rw [nrm, hz, Real.sqrt_sq hd0.le, div_self hd0.ne', Complex.ofReal_one, one_smul]
  have hS0 : Dense (pi univ fun _ : Fin m => ((E : Set ℂ) \ {0})) :=
    dense_pi _ fun _ _ => dense_E.sdiff_singleton 0
  rw [mem_closure_iff_nhds]
  intro W hW
  have hW' : nrm d ⁻¹' W ∈ 𝓝 z := hN.preimage_mem_nhds (by rwa [hNz])
  obtain ⟨y, hyW, hy⟩ := hS0.inter_open_nonempty _ (interior_mem_nhds.mpr hW' |> fun h =>
    isOpen_interior) ⟨z, mem_interior_iff_mem_nhds.mpr hW'⟩
  have hyW : nrm d y ∈ W := (interior_subset hyW : y ∈ nrm d ⁻¹' W)
  simp only [Set.mem_pi, mem_univ, Set.mem_sdiff, SetLike.mem_coe, mem_singleton_iff, true_implies] at hy
  let u : Fin m → E := fun j => ⟨y j, (hy j).1⟩
  have hyu : embP u = y := rfl
  have hu0 : ∀ j, u j ≠ 0 := fun j h => (hy j).2 (congrArg Subtype.val h)
  have hny : nsq y ≠ 0 := by
    intro h0
    obtain ⟨j⟩ : Nonempty (Fin m) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      exact hz0 (by simp [nsq])
    have : ‖y j‖ ^ 2 = 0 := by
      have hle := Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ j)
      have := sq_nonneg ‖y j‖
      unfold nsq at h0
      linarith
    exact (hy j).2 (by simpa using this)
  have hc : ((d / Real.sqrt (nsq y) : ℝ) : ℂ) ∈ E := by
    push_cast
    apply div_mem (mem_algebraicClosure_iff.mpr (alg_complex hdA))
    rw [← hyu]
    exact sqrt_mem (nsq_nonneg _) (nsq_mem u)
  have hc0 : (d / Real.sqrt (nsq y) : ℝ) ≠ 0 := by
    have hp : 0 < nsq y := lt_of_le_of_ne (nsq_nonneg y) (Ne.symm hny)
    exact div_ne_zero hd0.ne' (Real.sqrt_pos.mpr hp).ne'
  let u' : Fin m → E := fun j => ⟨((d / Real.sqrt (nsq y) : ℝ) : ℂ) * y j,
    mul_mem hc (hy j).1⟩
  have hu' : embP u' = nrm d y := by
    funext j; simp [embP, u', nrm]
  refine ⟨nrm d y, hyW, u', fun j h => ?_, by rw [hu']; exact nrm_nsq hny, hu'⟩
  have := congrArg Subtype.val h
  simp only [u', ZeroMemClass.coe_zero, mul_eq_zero, Complex.ofReal_eq_zero] at this
  rcases this with h1 | h1
  · exact hc0 h1
  · exact (hy j).2 h1

end HNN
end
end OAI
