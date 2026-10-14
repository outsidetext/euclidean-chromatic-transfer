import OAI.HNN.Field

/-!
# Coordinates: `EuclideanSpace ℝ (Fin (2m+r))` versus the real model

`toX` reads coordinates `(y_{2j}, y_{2j+1})` as the `j`-th complex block and the last `r`
coordinates as the axes; `ofX` is its inverse. `toX` is additive, continuous, and turns the
squared Euclidean norm into `usq`.
-/

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace HNN

abbrev EE (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {m r : ℕ}

def idx (j : Fin m) (b : Fin 2) : Fin (m * 2 + r) := Fin.castAdd r (finProdFinEquiv (j, b))
def lidx (i : Fin r) : Fin (m * 2 + r) := Fin.natAdd (m * 2) i

/-- Real-model coordinates of a point of Euclidean space. -/
def toX (y : EE (m * 2 + r)) : X m r :=
  (fun j => (y (idx j 0) : ℂ) + (y (idx j 1) : ℂ) * Complex.I, fun i => y (lidx i))

/-- The inverse of `toX`. -/
def ofX (x : X m r) : EE (m * 2 + r) :=
  WithLp.toLp 2 (Fin.addCases (motive := fun _ => ℝ)
    (fun p => if (finProdFinEquiv.symm p).2 = 0 then (x.1 (finProdFinEquiv.symm p).1).re
      else (x.1 (finProdFinEquiv.symm p).1).im) (fun i => x.2 i))

lemma toX_add (y z : EE (m * 2 + r)) : toX (y + z) = toX y + toX z := by
  refine Prod.ext ?_ ?_
  · funext j
    simp only [toX, Prod.fst_add, Pi.add_apply, PiLp.add_apply, Complex.ofReal_add]
    ring
  · funext i
    simp [toX]

lemma toX_sub (y z : EE (m * 2 + r)) : toX (y - z) = toX y - toX z := by
  have := toX_add (y - z) z
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

lemma toX_continuous : Continuous (toX (m := m) (r := r)) := by
  have hc : ∀ q : Fin (m * 2 + r), Continuous fun y : EE (m * 2 + r) => y q := fun q =>
    (continuous_apply q).comp (PiLp.continuous_ofLp 2 _)
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun i => hc _)
  exact (Complex.continuous_ofReal.comp (hc _)).add
    ((Complex.continuous_ofReal.comp (hc _)).mul continuous_const)

lemma usq_toX (y : EE (m * 2 + r)) : usq (toX y) = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add,
    ← (finProdFinEquiv (m := m) (n := 2)).sum_comp, Fintype.sum_prod_type]
  simp only [usq, nsq, toX, Complex.sq_norm, Complex.normSq_add_mul_I, Fin.sum_univ_two]
  rfl

lemma fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

lemma toX_ofX (x : X m r) : toX (ofX x) = x := by
  refine Prod.ext ?_ ?_
  · funext j
    simp only [toX, ofX, idx, PiLp.toLp_apply, Fin.addCases_left, Equiv.symm_apply_apply,
      ite_eq_right fin2_one_ne_zero]
    exact Complex.re_add_im _
  · funext i
    simp [toX, ofX, lidx]

lemma norm_ofX_sub (x x' : X m r) : ‖ofX x - ofX x'‖ ^ 2 = usq (x - x') := by
  rw [← usq_toX, toX_sub, toX_ofX, toX_ofX]

end HNN
end
end OAI
