/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu

! This file was ported from Lean 3 source module data.mv_polynomial.cardinal
! leanprover-community/mathlib commit 3cd7b577c6acf365f59a6376c5867533124eff6b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Fintype
import Mathbin.Data.MvPolynomial.Equiv
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `mv_polynomial.cardinal_mk_le_max`, which says that
the cardinality of `mv_polynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/


universe u v

open Cardinal

open Cardinal

namespace MvPolynomial

section TwoUniverses

variable {σ : Type u} {R : Type v} [CommSemiring R]

/- warning: mv_polynomial.cardinal_mk_eq_max_lift -> MvPolynomial.cardinal_mk_eq_max_lift is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nonempty.{succ u1} σ] [_inst_3 : Nontrivial.{u2} R], Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1)) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.canonicallyLinearOrderedAddMonoid.{max u1 u2}) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.canonicallyLinearOrderedAddMonoid.{max u1 u2}) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} R)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} σ))) Cardinal.aleph0.{max u1 u2})
but is expected to have type
  forall {σ : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] [_inst_2 : Nonempty.{succ u1} σ] [_inst_3 : Nontrivial.{u2} R], Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.mk.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_1)) (Max.max.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Max.max.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} R)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} σ))) Cardinal.aleph0.{max u1 u2})
Case conversion may be inaccurate. Consider using '#align mv_polynomial.cardinal_mk_eq_max_lift MvPolynomial.cardinal_mk_eq_max_liftₓ'. -/
@[simp]
theorem cardinal_mk_eq_max_lift [Nonempty σ] [Nontrivial R] :
    (#MvPolynomial σ R) = max (max (Cardinal.lift.{u} <| (#R)) <| Cardinal.lift.{v} <| (#σ)) ℵ₀ :=
  (mk_finsupp_lift_of_infinite _ R).trans <| by
    rw [mk_finsupp_nat, max_assoc, lift_max, lift_aleph_0, max_comm]
#align mv_polynomial.cardinal_mk_eq_max_lift MvPolynomial.cardinal_mk_eq_max_lift

#print MvPolynomial.cardinal_mk_eq_lift /-
@[simp]
theorem cardinal_mk_eq_lift [IsEmpty σ] : (#MvPolynomial σ R) = Cardinal.lift.{u} (#R) :=
  ((isEmptyRingEquiv R σ).toEquiv.trans Equiv.ulift.{u}.symm).cardinal_eq
#align mv_polynomial.cardinal_mk_eq_lift MvPolynomial.cardinal_mk_eq_lift
-/

/- warning: mv_polynomial.cardinal_lift_mk_le_max -> MvPolynomial.cardinal_lift_mk_le_max is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R], LE.le.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasLe.{max u1 u2} (Cardinal.mk.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_2)) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.canonicallyLinearOrderedAddMonoid.{max u1 u2}) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.canonicallyLinearOrderedAddMonoid.{max u1 u2}) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} R)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} σ))) Cardinal.aleph0.{max u1 u2})
but is expected to have type
  forall {σ : Type.{u1}} {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R], LE.le.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instLECardinal.{max u1 u2} (Cardinal.mk.{max u2 u1} (MvPolynomial.{u1, u2} σ R _inst_2)) (Max.max.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Max.max.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} R)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} σ))) Cardinal.aleph0.{max u1 u2})
Case conversion may be inaccurate. Consider using '#align mv_polynomial.cardinal_lift_mk_le_max MvPolynomial.cardinal_lift_mk_le_maxₓ'. -/
theorem cardinal_lift_mk_le_max {σ : Type u} {R : Type v} [CommSemiring R] :
    (#MvPolynomial σ R) ≤ max (max (Cardinal.lift.{u} <| (#R)) <| Cardinal.lift.{v} <| (#σ)) ℵ₀ :=
  by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0)
  cases isEmpty_or_nonempty σ
  · exact cardinal_mk_eq_lift.trans_le (le_max_of_le_left <| le_max_left _ _)
  · exact cardinal_mk_eq_max_lift.le
#align mv_polynomial.cardinal_lift_mk_le_max MvPolynomial.cardinal_lift_mk_le_max

end TwoUniverses

variable {σ R : Type u} [CommSemiring R]

/- warning: mv_polynomial.cardinal_mk_eq_max -> MvPolynomial.cardinal_mk_eq_max is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nonempty.{succ u1} σ] [_inst_3 : Nontrivial.{u1} R], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (MvPolynomial.{u1, u1} σ R _inst_1)) (LinearOrder.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ u1} Cardinal.{u1} Cardinal.canonicallyLinearOrderedAddMonoid.{u1}) (LinearOrder.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ u1} Cardinal.{u1} Cardinal.canonicallyLinearOrderedAddMonoid.{u1}) (Cardinal.mk.{u1} R) (Cardinal.mk.{u1} σ)) Cardinal.aleph0.{u1})
but is expected to have type
  forall {σ : Type.{u1}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Nonempty.{succ u1} σ] [_inst_3 : Nontrivial.{u1} R], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (MvPolynomial.{u1, u1} σ R _inst_1)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} R) (Cardinal.mk.{u1} σ)) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align mv_polynomial.cardinal_mk_eq_max MvPolynomial.cardinal_mk_eq_maxₓ'. -/
theorem cardinal_mk_eq_max [Nonempty σ] [Nontrivial R] :
    (#MvPolynomial σ R) = max (max (#R) (#σ)) ℵ₀ := by simp
#align mv_polynomial.cardinal_mk_eq_max MvPolynomial.cardinal_mk_eq_max

/- warning: mv_polynomial.cardinal_mk_le_max -> MvPolynomial.cardinal_mk_le_max is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R], LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (MvPolynomial.{u1, u1} σ R _inst_1)) (LinearOrder.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ u1} Cardinal.{u1} Cardinal.canonicallyLinearOrderedAddMonoid.{u1}) (LinearOrder.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{succ u1} Cardinal.{u1} Cardinal.canonicallyLinearOrderedAddMonoid.{u1}) (Cardinal.mk.{u1} R) (Cardinal.mk.{u1} σ)) Cardinal.aleph0.{u1})
but is expected to have type
  forall {σ : Type.{u1}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R], LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (MvPolynomial.{u1, u1} σ R _inst_1)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} R) (Cardinal.mk.{u1} σ)) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align mv_polynomial.cardinal_mk_le_max MvPolynomial.cardinal_mk_le_maxₓ'. -/
/-- The cardinality of the multivariate polynomial ring, `mv_polynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
theorem cardinal_mk_le_max : (#MvPolynomial σ R) ≤ max (max (#R) (#σ)) ℵ₀ :=
  cardinal_lift_mk_le_max.trans <| by rw [lift_id, lift_id]
#align mv_polynomial.cardinal_mk_le_max MvPolynomial.cardinal_mk_le_max

end MvPolynomial

