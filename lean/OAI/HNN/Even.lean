import OAI.HNN.Sphere

/-!
# Even dimension: zero correlation at every real vector of forbidden length

For `r = 0` the axis representation is trivial, so `pv = gv`, which has zero correlation at
every generic algebraic vector of forbidden length. Continuity of the extended orbit and density
of generic algebraic points in spheres (`sphere_closure`) give zero correlation at every real
vector of forbidden length.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate
namespace HNN
open PlaneFiveColor.Spectral EuclideanFiveColor EuclideanFiveColor.ContinuousVectors

variable {m r : ℕ}

/-- Squared Euclidean norm on the real model. -/
def usq (y : X m r) : ℝ := nsq y.1 + ∑ i, (y.2 i) ^ 2

lemma usq_emb (a : V m r) : usq (emb a) = sq a := by
  simp [usq, sq, nsq, emb, embP, embL]

lemma usq_neg (y : X m r) : usq (-y) = usq y := by simp [usq, nsq]

lemma emb_sub (a b : V m r) : emb (a - b) = emb a - emb b := by
  have := emb_add (a - b) b
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

variable {D : Set ℝ} {k : ℕ}

section Even
variable (ω : Space m 0 D k)

lemma line_trivial (v : Hilbert ω) : v ∈ space (A := AF) (lineRep ω) := by
  change Tendsto (fun a : AF => op (lineRep ω) a v) (𝓝 0) (𝓝 v)
  have he : ∀ a : AF, op (lineRep ω) a v = v := by
    intro a
    rw [lineRep_op, show ((0 : Fin m → E), (fun _ => a : Fin 0 → AF)) = (0 : V m 0) from
      Prod.ext rfl (funext fun i => i.elim0), T_zero]
  simp only [he]
  exact tendsto_const_nhds

lemma pv_eq_gv (i : Fin k) : pv ω i = gv ω i :=
  Submodule.starProjection_eq_self_iff.mpr (line_trivial ω _)

theorem pv_corr_even (i : Fin k) {d : ℝ} (hd : d ∈ D) (hdA : IsAlgebraic ℚ d) (hd0 : 0 < d)
    (y : X m 0) (hy : usq y = d ^ 2) :
    ⟪pv ω i, Ext ω (pv ω i) y⟫_ℂ = 0 := by
  have hr : (0 : ℕ) ≤ 1 := zero_le_one
  have hc := Ext_continuous ω hr (pv_plane ω i) (pv_line ω i)
  have hy2 : y = (y.1, 0) := Prod.ext rfl (funext fun i => i.elim0)
  have hy1 : nsq y.1 = d ^ 2 := by simpa [usq] using hy
  have hcl : IsClosed {z : Fin m → ℂ | ⟪pv ω i, Ext ω (pv ω i) (z, 0)⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner (hc.comp (continuous_id.prodMk continuous_const)))
      continuous_const
  have hsub : {y | ∃ u : Fin m → E, (∀ j, u j ≠ 0) ∧ nsq (embP u) = d ^ 2 ∧ embP u = y} ⊆
      {z : Fin m → ℂ | ⟪pv ω i, Ext ω (pv ω i) (z, 0)⟫_ℂ = 0} := by
    rintro _ ⟨u, hu0, hun, rfl⟩
    let a : V m 0 := (u, 0)
    have hea : emb a = (embP u, 0) := Prod.ext rfl (funext fun i => i.elim0)
    have hsq : sq a = d ^ 2 := by rw [← usq_emb, hea]; simpa [usq] using hun
    change ⟪pv ω i, Ext ω (pv ω i) (embP u, 0)⟫_ℂ = 0
    rw [← hea, Ext_eq ω hr (pv_plane ω i) (pv_line ω i), pv_eq_gv]
    exact gv_correlation ω i a hu0 hd hsq
  have := closure_minimal hsub hcl (sphere_closure hdA hd0 hy1)
  rw [hy2]
  exact this

end Even

end HNN
end
end OAI
