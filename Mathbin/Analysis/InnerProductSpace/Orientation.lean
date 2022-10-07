/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathbin.Analysis.InnerProductSpace.PiL2
import Mathbin.LinearAlgebra.Orientation

/-!
# Orientations of real inner product spaces.

This file provides definitions and proves lemmas about orientations of real inner product spaces.

## Main definitions

* `orientation.fin_orthonormal_basis` is an orthonormal basis, indexed by `fin n`, with the given
orientation.

-/


noncomputable section

variable {E : Type _} [InnerProductSpace ℝ E]

open FiniteDimensional

section AdjustToOrientation

variable {ι : Type _} [Fintypeₓ ι] [DecidableEq ι] [Nonempty ι] (e : OrthonormalBasis ι ℝ E) (x : Orientation ℝ E ι)

/-- `orthonormal_basis.adjust_to_orientation`, applied to an orthonormal basis, produces an
orthonormal basis. -/
theorem OrthonormalBasis.orthonormal_adjust_to_orientation : Orthonormal ℝ (e.toBasis.adjustToOrientation x) := by
  apply e.orthonormal.orthonormal_of_forall_eq_or_eq_neg
  simpa using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x

/-- Given an orthonormal basis and an orientation, return an orthonormal basis giving that
orientation: either the original basis, or one constructed by negating a single (arbitrary) basis
vector. -/
def OrthonormalBasis.adjustToOrientation : OrthonormalBasis ι ℝ E :=
  (e.toBasis.adjustToOrientation x).toOrthonormalBasis (e.orthonormal_adjust_to_orientation x)

theorem OrthonormalBasis.to_basis_adjust_to_orientation :
    (e.adjustToOrientation x).toBasis = e.toBasis.adjustToOrientation x :=
  (e.toBasis.adjustToOrientation x).to_basis_to_orthonormal_basis _

/-- `adjust_to_orientation` gives an orthonormal basis with the required orientation. -/
@[simp]
theorem OrthonormalBasis.orientation_adjust_to_orientation : (e.adjustToOrientation x).toBasis.Orientation = x := by
  rw [e.to_basis_adjust_to_orientation]
  exact e.to_basis.orientation_adjust_to_orientation x

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
theorem OrthonormalBasis.adjust_to_orientation_apply_eq_or_eq_neg (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  simpa [← e.to_basis_adjust_to_orientation] using e.to_basis.adjust_to_orientation_apply_eq_or_eq_neg x i

end AdjustToOrientation

/-- An orthonormal basis, indexed by `fin n`, with the given orientation. -/
protected def Orientation.finOrthonormalBasis {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Finₓ n)) : OrthonormalBasis (Finₓ n) ℝ E := by
  haveI := Finₓ.pos_iff_nonempty.1 hn
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E)
  exact ((stdOrthonormalBasis _ _).reindex <| finCongr h).adjustToOrientation x

/-- `orientation.fin_orthonormal_basis` gives a basis with the required orientation. -/
@[simp]
theorem Orientation.fin_orthonormal_basis_orientation {n : ℕ} (hn : 0 < n) (h : finrank ℝ E = n)
    (x : Orientation ℝ E (Finₓ n)) : (x.finOrthonormalBasis hn h).toBasis.Orientation = x := by
  haveI := Finₓ.pos_iff_nonempty.1 hn
  haveI := finite_dimensional_of_finrank (h.symm ▸ hn : 0 < finrank ℝ E)
  exact ((stdOrthonormalBasis _ _).reindex <| finCongr h).orientation_adjust_to_orientation x

