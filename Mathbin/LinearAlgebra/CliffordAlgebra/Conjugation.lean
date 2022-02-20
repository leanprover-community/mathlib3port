/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.LinearAlgebra.CliffordAlgebra.Basic
import Mathbin.Algebra.Module.Opposites

/-!
# Conjugations

This file defines the grade reversal and grade involution functions on multivectors, `reverse` and
`involute`.
Together, these operations compose to form the "Clifford conjugate", hence the name of this file.

https://en.wikipedia.org/wiki/Clifford_algebra#Antiautomorphisms

## Main definitions

* `clifford_algebra.involute`: the grade involution, negating each basis vector
* `clifford_algebra.reverse`: the grade reversion, reversing the order of a product of vectors

## Main statements

* `clifford_algebra.involute_involutive`
* `clifford_algebra.reverse_involutive`
* `clifford_algebra.reverse_involute_commute`
-/


variable {R : Type _} [CommRingₓ R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

section Involute

/-- Grade involution, inverting the sign of each basis vector. -/
def involute : CliffordAlgebra Q →ₐ[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift Q
    ⟨-ι Q, fun m => by
      simp ⟩

@[simp]
theorem involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  lift_ι_apply _ _ m

@[simp]
theorem involute_comp_involute : involute.comp involute = AlgHom.id R (CliffordAlgebra Q) := by
  ext
  simp

theorem involute_involutive : Function.Involutive (involute : _ → CliffordAlgebra Q) :=
  AlgHom.congr_fun involute_comp_involute

@[simp]
theorem involute_involute : ∀ a : CliffordAlgebra Q, involute (involute a) = a :=
  involute_involutive

end Involute

section Reverse

open MulOpposite

/-- Grade reversion, inverting the multiplication order of basis vectors.
Also called *transpose* in some literature. -/
def reverse : CliffordAlgebra Q →ₗ[R] CliffordAlgebra Q :=
  (opLinearEquiv R).symm.toLinearMap.comp
    (CliffordAlgebra.lift Q
        ⟨(MulOpposite.opLinearEquiv R).toLinearMap.comp (ι Q), fun m =>
          unop_injective <| by
            simp ⟩).toLinearMap

@[simp]
theorem reverse_ι (m : M) : reverse (ι Q m) = ι Q m := by
  simp [reverse]

@[simp]
theorem reverse.commutes (r : R) : reverse (algebraMap R (CliffordAlgebra Q) r) = algebraMap R _ r := by
  simp [reverse]

@[simp]
theorem reverse.map_one : reverse (1 : CliffordAlgebra Q) = 1 := by
  convert reverse.commutes (1 : R) <;> simp

@[simp]
theorem reverse.map_mul (a b : CliffordAlgebra Q) : reverse (a * b) = reverse b * reverse a := by
  simp [reverse]

@[simp]
theorem reverse_comp_reverse : reverse.comp reverse = (LinearMap.id : _ →ₗ[R] CliffordAlgebra Q) := by
  ext m
  simp only [LinearMap.id_apply, LinearMap.comp_apply]
  induction m using CliffordAlgebra.induction
  -- simp can close these goals, but is slow
  case h_grade0 =>
    rw [reverse.commutes, reverse.commutes]
  case h_grade1 =>
    rw [reverse_ι, reverse_ι]
  case h_mul a b ha hb =>
    rw [reverse.map_mul, reverse.map_mul, ha, hb]
  case h_add a b ha hb =>
    rw [reverse.map_add, reverse.map_add, ha, hb]

@[simp]
theorem reverse_involutive : Function.Involutive (reverse : _ → CliffordAlgebra Q) :=
  LinearMap.congr_fun reverse_comp_reverse

@[simp]
theorem reverse_reverse : ∀ a : CliffordAlgebra Q, reverse (reverse a) = a :=
  reverse_involutive

theorem reverse_comp_involute :
    reverse.comp involute.toLinearMap = (involute.toLinearMap.comp reverse : _ →ₗ[R] CliffordAlgebra Q) := by
  ext
  simp only [LinearMap.comp_apply, AlgHom.to_linear_map_apply]
  induction x using CliffordAlgebra.induction
  case h_grade0 =>
    simp
  case h_grade1 =>
    simp
  case h_mul a b ha hb =>
    simp only [ha, hb, reverse.map_mul, AlgHom.map_mul]
  case h_add a b ha hb =>
    simp only [ha, hb, reverse.map_add, AlgHom.map_add]

/-- `clifford_algebra.reverse` and `clifford_algebra.inverse` commute. Note that the composition
is sometimes referred to as the "clifford conjugate". -/
theorem reverse_involute_commute : Function.Commute (reverse : _ → CliffordAlgebra Q) involute :=
  LinearMap.congr_fun reverse_comp_involute

theorem reverse_involute : ∀ a : CliffordAlgebra Q, reverse (involute a) = involute (reverse a) :=
  reverse_involute_commute

end Reverse

/-!
### Statements about conjugations of products of lists
-/


section List

/-- Taking the reverse of the product a list of $n$ vectors lifted via `ι` is equivalent to
taking the product of the reverse of that list. -/
theorem reverse_prod_map_ι : ∀ l : List M, reverse (l.map <| ι Q).Prod = (l.map <| ι Q).reverse.Prod
  | [] => by
    simp
  | x :: xs => by
    simp [reverse_prod_map_ι xs]

/-- Taking the involute of the product a list of $n$ vectors lifted via `ι` is equivalent to
premultiplying by ${-1}^n$. -/
theorem involute_prod_map_ι : ∀ l : List M, involute (l.map <| ι Q).Prod = (-1 : R) ^ l.length • (l.map <| ι Q).Prod
  | [] => by
    simp
  | x :: xs => by
    simp [pow_addₓ, involute_prod_map_ι xs]

end List

end CliffordAlgebra

