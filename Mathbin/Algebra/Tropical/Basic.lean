/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module algebra.tropical.basic
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Algebra.SmulWithZero
import Mathbin.Algebra.Order.Monoid.MinMax

/-!

# Tropical algebraic structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[linear_order R]`, then addition on `R` is via `min`.
* `semiring (tropical R)`: A `linear_ordered_add_comm_monoid_with_top R`
    induces a `semiring (tropical R)`. If one solely has `[linear_ordered_add_comm_monoid R]`,
    then the "tropicalization of `R`" would be `tropical (with_top R)`.

## Implementation notes

The tropical structure relies on `has_top` and `min`. For the max-tropical numbers, use
`order_dual R`.

Inspiration was drawn from the implementation of `additive`/`multiplicative`/`opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `semiring (tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/


universe u v

variable (R : Type u)

#print Tropical /-
/-- The tropicalization of a type `R`. -/
def Tropical : Type u :=
  R
#align tropical Tropical
-/

variable {R}

namespace Tropical

#print Tropical.trop /-
/-- Reinterpret `x : R` as an element of `tropical R`.
See `tropical.trop_equiv` for the equivalence.
-/
@[pp_nodot]
def trop : R → Tropical R :=
  id
#align tropical.trop Tropical.trop
-/

#print Tropical.untrop /-
/-- Reinterpret `x : tropical R` as an element of `R`.
See `tropical.trop_equiv` for the equivalence. -/
@[pp_nodot]
def untrop : Tropical R → R :=
  id
#align tropical.untrop Tropical.untrop
-/

#print Tropical.trop_injective /-
theorem trop_injective : Function.Injective (trop : R → Tropical R) := fun _ _ => id
#align tropical.trop_injective Tropical.trop_injective
-/

#print Tropical.untrop_injective /-
theorem untrop_injective : Function.Injective (untrop : Tropical R → R) := fun _ _ => id
#align tropical.untrop_injective Tropical.untrop_injective
-/

#print Tropical.trop_inj_iff /-
@[simp]
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl
#align tropical.trop_inj_iff Tropical.trop_inj_iff
-/

#print Tropical.untrop_inj_iff /-
@[simp]
theorem untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl
#align tropical.untrop_inj_iff Tropical.untrop_inj_iff
-/

#print Tropical.trop_untrop /-
@[simp]
theorem trop_untrop (x : Tropical R) : trop (untrop x) = x :=
  rfl
#align tropical.trop_untrop Tropical.trop_untrop
-/

#print Tropical.untrop_trop /-
@[simp]
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl
#align tropical.untrop_trop Tropical.untrop_trop
-/

#print Tropical.leftInverse_trop /-
theorem leftInverse_trop : Function.LeftInverse (trop : R → Tropical R) untrop :=
  trop_untrop
#align tropical.left_inverse_trop Tropical.leftInverse_trop
-/

#print Tropical.rightInverse_trop /-
theorem rightInverse_trop : Function.RightInverse (trop : R → Tropical R) untrop :=
  trop_untrop
#align tropical.right_inverse_trop Tropical.rightInverse_trop
-/

#print Tropical.tropEquiv /-
/-- Reinterpret `x : R` as an element of `tropical R`.
See `tropical.trop_order_iso` for the order-preserving equivalence. -/
def tropEquiv : R ≃ Tropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop
#align tropical.trop_equiv Tropical.tropEquiv
-/

#print Tropical.tropEquiv_coe_fn /-
@[simp]
theorem tropEquiv_coe_fn : (tropEquiv : R → Tropical R) = trop :=
  rfl
#align tropical.trop_equiv_coe_fn Tropical.tropEquiv_coe_fn
-/

#print Tropical.tropEquiv_symm_coe_fn /-
@[simp]
theorem tropEquiv_symm_coe_fn : (tropEquiv.symm : Tropical R → R) = untrop :=
  rfl
#align tropical.trop_equiv_symm_coe_fn Tropical.tropEquiv_symm_coe_fn
-/

#print Tropical.trop_eq_iff_eq_untrop /-
theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.apply_eq_iff_eq_symm_apply
#align tropical.trop_eq_iff_eq_untrop Tropical.trop_eq_iff_eq_untrop
-/

#print Tropical.untrop_eq_iff_eq_trop /-
theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.apply_eq_iff_eq_symm_apply
#align tropical.untrop_eq_iff_eq_trop Tropical.untrop_eq_iff_eq_trop
-/

#print Tropical.injective_trop /-
theorem injective_trop : Function.Injective (trop : R → Tropical R) :=
  tropEquiv.Injective
#align tropical.injective_trop Tropical.injective_trop
-/

#print Tropical.injective_untrop /-
theorem injective_untrop : Function.Injective (untrop : Tropical R → R) :=
  tropEquiv.symm.Injective
#align tropical.injective_untrop Tropical.injective_untrop
-/

#print Tropical.surjective_trop /-
theorem surjective_trop : Function.Surjective (trop : R → Tropical R) :=
  tropEquiv.Surjective
#align tropical.surjective_trop Tropical.surjective_trop
-/

#print Tropical.surjective_untrop /-
theorem surjective_untrop : Function.Surjective (untrop : Tropical R → R) :=
  tropEquiv.symm.Surjective
#align tropical.surjective_untrop Tropical.surjective_untrop
-/

instance [Inhabited R] : Inhabited (Tropical R) :=
  ⟨trop default⟩

#print Tropical.tropRec /-
/-- Recursing on a `x' : tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `tropical R` via `trop x`. -/
@[simp]
def tropRec {F : ∀ X : Tropical R, Sort v} (h : ∀ X, F (trop X)) : ∀ X, F X := fun X => h (untrop X)
#align tropical.trop_rec Tropical.tropRec
-/

instance [DecidableEq R] : DecidableEq (Tropical R) := fun x y =>
  decidable_of_iff _ injective_untrop.eq_iff

section Order

instance [LE R] : LE (Tropical R) where le x y := untrop x ≤ untrop y

#print Tropical.untrop_le_iff /-
@[simp]
theorem untrop_le_iff [LE R] {x y : Tropical R} : untrop x ≤ untrop y ↔ x ≤ y :=
  Iff.rfl
#align tropical.untrop_le_iff Tropical.untrop_le_iff
-/

#print Tropical.decidableLE /-
instance decidableLE [LE R] [DecidableRel ((· ≤ ·) : R → R → Prop)] :
    DecidableRel ((· ≤ ·) : Tropical R → Tropical R → Prop) := fun x y =>
  ‹DecidableRel (· ≤ ·)› (untrop x) (untrop y)
#align tropical.decidable_le Tropical.decidableLE
-/

instance [LT R] : LT (Tropical R) where lt x y := untrop x < untrop y

#print Tropical.untrop_lt_iff /-
@[simp]
theorem untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl
#align tropical.untrop_lt_iff Tropical.untrop_lt_iff
-/

#print Tropical.decidableLT /-
instance decidableLT [LT R] [DecidableRel ((· < ·) : R → R → Prop)] :
    DecidableRel ((· < ·) : Tropical R → Tropical R → Prop) := fun x y =>
  ‹DecidableRel (· < ·)› (untrop x) (untrop y)
#align tropical.decidable_lt Tropical.decidableLT
-/

instance [Preorder R] : Preorder (Tropical R) :=
  { Tropical.hasLe, Tropical.hasLt with
    le_refl := fun _ => le_rfl
    le_trans := fun _ _ _ h h' => le_trans h h'
    lt_iff_le_not_le := fun _ _ => lt_iff_le_not_le }

#print Tropical.tropOrderIso /-
/-- Reinterpret `x : R` as an element of `tropical R`, preserving the order. -/
def tropOrderIso [Preorder R] : R ≃o Tropical R :=
  { tropEquiv with map_rel_iff' := fun _ _ => untrop_le_iff }
#align tropical.trop_order_iso Tropical.tropOrderIso
-/

/- warning: tropical.trop_order_iso_coe_fn -> Tropical.tropOrderIso_coe_fn is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Eq.{succ u1} ((fun (_x : RelIso.{u1, u1} R (Tropical.{u1} R) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1)) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1)))) => R -> (Tropical.{u1} R)) (Tropical.tropOrderIso.{u1} R _inst_1)) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} R (Tropical.{u1} R) (Preorder.toLE.{u1} R _inst_1) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1))) (fun (_x : RelIso.{u1, u1} R (Tropical.{u1} R) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1)) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1)))) => R -> (Tropical.{u1} R)) (RelIso.hasCoeToFun.{u1, u1} R (Tropical.{u1} R) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1)) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1)))) (Tropical.tropOrderIso.{u1} R _inst_1)) (Tropical.trop.{u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Eq.{succ u1} (forall (a : R), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => Tropical.{u1} R) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} R (Tropical.{u1} R)) R (fun (_x : R) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => Tropical.{u1} R) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} R (Tropical.{u1} R)) R (Tropical.{u1} R) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} R (Tropical.{u1} R))) (RelEmbedding.toEmbedding.{u1, u1} R (Tropical.{u1} R) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : R) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Tropical.{u1} R) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Tropical.{u1} R) => LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u1} R (Tropical.{u1} R) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : R) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Tropical.{u1} R) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Tropical.{u1} R) => LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (Tropical.tropOrderIso.{u1} R _inst_1)))) (Tropical.trop.{u1} R)
Case conversion may be inaccurate. Consider using '#align tropical.trop_order_iso_coe_fn Tropical.tropOrderIso_coe_fnₓ'. -/
@[simp]
theorem tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R → Tropical R) = trop :=
  rfl
#align tropical.trop_order_iso_coe_fn Tropical.tropOrderIso_coe_fn

/- warning: tropical.trop_order_iso_symm_coe_fn -> Tropical.tropOrderIso_symm_coe_fn is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Eq.{succ u1} ((fun (_x : RelIso.{u1, u1} (Tropical.{u1} R) R (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1))) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1))) => (Tropical.{u1} R) -> R) (OrderIso.symm.{u1, u1} R (Tropical.{u1} R) (Preorder.toLE.{u1} R _inst_1) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1)) (Tropical.tropOrderIso.{u1} R _inst_1))) (coeFn.{succ u1, succ u1} (OrderIso.{u1, u1} (Tropical.{u1} R) R (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1)) (Preorder.toLE.{u1} R _inst_1)) (fun (_x : RelIso.{u1, u1} (Tropical.{u1} R) R (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1))) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1))) => (Tropical.{u1} R) -> R) (RelIso.hasCoeToFun.{u1, u1} (Tropical.{u1} R) R (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1))) (LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1))) (OrderIso.symm.{u1, u1} R (Tropical.{u1} R) (Preorder.toLE.{u1} R _inst_1) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R _inst_1)) (Tropical.tropOrderIso.{u1} R _inst_1))) (Tropical.untrop.{u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Eq.{succ u1} (forall (a : Tropical.{u1} R), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Tropical.{u1} R) => R) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Tropical.{u1} R) R) (Tropical.{u1} R) (fun (_x : Tropical.{u1} R) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Tropical.{u1} R) => R) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Tropical.{u1} R) R) (Tropical.{u1} R) R (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Tropical.{u1} R) R)) (RelEmbedding.toEmbedding.{u1, u1} (Tropical.{u1} R) R (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Tropical.{u1} R) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Tropical.{u1} R) => LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : R) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{u1, u1} (Tropical.{u1} R) R (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Tropical.{u1} R) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Tropical.{u1} R) => LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R _inst_1)) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : R) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (OrderIso.symm.{u1, u1} R (Tropical.{u1} R) (Preorder.toLE.{u1} R _inst_1) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R _inst_1)) (Tropical.tropOrderIso.{u1} R _inst_1))))) (Tropical.untrop.{u1} R)
Case conversion may be inaccurate. Consider using '#align tropical.trop_order_iso_symm_coe_fn Tropical.tropOrderIso_symm_coe_fnₓ'. -/
@[simp]
theorem tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : Tropical R → R) = untrop :=
  rfl
#align tropical.trop_order_iso_symm_coe_fn Tropical.tropOrderIso_symm_coe_fn

/- warning: tropical.trop_monotone -> Tropical.trop_monotone is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Monotone.{u1, u1} R (Tropical.{u1} R) _inst_1 (Tropical.preorder.{u1} R _inst_1) (Tropical.trop.{u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Monotone.{u1, u1} R (Tropical.{u1} R) _inst_1 (Tropical.instPreorderTropical.{u1} R _inst_1) (Tropical.trop.{u1} R)
Case conversion may be inaccurate. Consider using '#align tropical.trop_monotone Tropical.trop_monotoneₓ'. -/
theorem trop_monotone [Preorder R] : Monotone (trop : R → Tropical R) := fun _ _ => id
#align tropical.trop_monotone Tropical.trop_monotone

/- warning: tropical.untrop_monotone -> Tropical.untrop_monotone is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Monotone.{u1, u1} (Tropical.{u1} R) R (Tropical.preorder.{u1} R _inst_1) _inst_1 (Tropical.untrop.{u1} R)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Preorder.{u1} R], Monotone.{u1, u1} (Tropical.{u1} R) R (Tropical.instPreorderTropical.{u1} R _inst_1) _inst_1 (Tropical.untrop.{u1} R)
Case conversion may be inaccurate. Consider using '#align tropical.untrop_monotone Tropical.untrop_monotoneₓ'. -/
theorem untrop_monotone [Preorder R] : Monotone (untrop : Tropical R → R) := fun _ _ => id
#align tropical.untrop_monotone Tropical.untrop_monotone

instance [PartialOrder R] : PartialOrder (Tropical R) :=
  { Tropical.preorder with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }

instance [Top R] : Zero (Tropical R) :=
  ⟨trop ⊤⟩

instance [Top R] : Top (Tropical R) :=
  ⟨0⟩

#print Tropical.untrop_zero /-
@[simp]
theorem untrop_zero [Top R] : untrop (0 : Tropical R) = ⊤ :=
  rfl
#align tropical.untrop_zero Tropical.untrop_zero
-/

#print Tropical.trop_top /-
@[simp]
theorem trop_top [Top R] : trop (⊤ : R) = 0 :=
  rfl
#align tropical.trop_top Tropical.trop_top
-/

#print Tropical.trop_coe_ne_zero /-
@[simp]
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) ≠ 0 :=
  fun.
#align tropical.trop_coe_ne_zero Tropical.trop_coe_ne_zero
-/

#print Tropical.zero_ne_trop_coe /-
@[simp]
theorem zero_ne_trop_coe (x : R) : (0 : Tropical (WithTop R)) ≠ trop x :=
  fun.
#align tropical.zero_ne_trop_coe Tropical.zero_ne_trop_coe
-/

/- warning: tropical.le_zero -> Tropical.le_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LE.{u1} R] [_inst_2 : OrderTop.{u1} R _inst_1] (x : Tropical.{u1} R), LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R _inst_1) x (OfNat.ofNat.{u1} (Tropical.{u1} R) 0 (OfNat.mk.{u1} (Tropical.{u1} R) 0 (Zero.zero.{u1} (Tropical.{u1} R) (Tropical.hasZero.{u1} R (OrderTop.toHasTop.{u1} R _inst_1 _inst_2)))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LE.{u1} R] [_inst_2 : OrderTop.{u1} R _inst_1] (x : Tropical.{u1} R), LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R _inst_1) x (OfNat.ofNat.{u1} (Tropical.{u1} R) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} R) (Tropical.instZeroTropical.{u1} R (OrderTop.toTop.{u1} R _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align tropical.le_zero Tropical.le_zeroₓ'. -/
@[simp]
theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x ≤ 0 :=
  le_top
#align tropical.le_zero Tropical.le_zero

instance [LE R] [OrderTop R] : OrderTop (Tropical R) :=
  { Tropical.hasTop with le_top := fun _ => le_top }

variable [LinearOrder R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
instance : Add (Tropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩

instance : AddCommSemigroup (Tropical R)
    where
  add := (· + ·)
  add_assoc _ _ _ := untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

/- warning: tropical.untrop_add -> Tropical.untrop_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} R (Tropical.untrop.{u1} R (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y)) (LinearOrder.min.{u1} R _inst_1 (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} R (Tropical.untrop.{u1} R (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y)) (Min.min.{u1} R (LinearOrder.toMin.{u1} R _inst_1) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y))
Case conversion may be inaccurate. Consider using '#align tropical.untrop_add Tropical.untrop_addₓ'. -/
@[simp]
theorem untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl
#align tropical.untrop_add Tropical.untrop_add

/- warning: tropical.trop_min -> Tropical.trop_min is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : R) (y : R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (LinearOrder.min.{u1} R _inst_1 x y)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) (Tropical.trop.{u1} R x) (Tropical.trop.{u1} R y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : R) (y : R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Min.min.{u1} R (LinearOrder.toMin.{u1} R _inst_1) x y)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) (Tropical.trop.{u1} R x) (Tropical.trop.{u1} R y))
Case conversion may be inaccurate. Consider using '#align tropical.trop_min Tropical.trop_minₓ'. -/
@[simp]
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl
#align tropical.trop_min Tropical.trop_min

/- warning: tropical.trop_inf -> Tropical.trop_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : R) (y : R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (HasInf.inf.{u1} R (SemilatticeInf.toHasInf.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1))) x y)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) (Tropical.trop.{u1} R x) (Tropical.trop.{u1} R y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : R) (y : R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (HasInf.inf.{u1} R (Lattice.toHasInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))) x y)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) (Tropical.trop.{u1} R x) (Tropical.trop.{u1} R y))
Case conversion may be inaccurate. Consider using '#align tropical.trop_inf Tropical.trop_infₓ'. -/
@[simp]
theorem trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  rfl
#align tropical.trop_inf Tropical.trop_inf

/- warning: tropical.trop_add_def -> Tropical.trop_add_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) (Tropical.trop.{u1} R (LinearOrder.min.{u1} R _inst_1 (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) (Tropical.trop.{u1} R (Min.min.{u1} R (LinearOrder.toMin.{u1} R _inst_1) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y)))
Case conversion may be inaccurate. Consider using '#align tropical.trop_add_def Tropical.trop_add_defₓ'. -/
theorem trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl
#align tropical.trop_add_def Tropical.trop_add_def

instance : LinearOrder (Tropical R) :=
  {
    Tropical.partialOrder with
    le_total := fun a b => le_total (untrop a) (untrop b)
    decidableLe := Tropical.decidableLE
    decidableLt := Tropical.decidableLT
    DecidableEq := Tropical.decidableEq
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := by
      ext (x y)
      rw [maxDefault, max_def, apply_ite trop, trop_untrop, trop_untrop,
        if_congr untrop_le_iff rfl rfl]
    min := (· + ·)
    min_def := by
      ext (x y)
      rw [trop_add_def, minDefault, min_def, apply_ite trop, trop_untrop, trop_untrop,
        if_congr untrop_le_iff rfl rfl] }

/- warning: tropical.untrop_sup -> Tropical.untrop_sup is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} R (Tropical.untrop.{u1} R (HasSup.sup.{u1} (Tropical.{u1} R) (SemilatticeSup.toHasSup.{u1} (Tropical.{u1} R) (Lattice.toSemilatticeSup.{u1} (Tropical.{u1} R) (LinearOrder.toLattice.{u1} (Tropical.{u1} R) (Tropical.linearOrder.{u1} R _inst_1)))) x y)) (HasSup.sup.{u1} R (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (LinearOrder.toLattice.{u1} R _inst_1))) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} R (Tropical.untrop.{u1} R (HasSup.sup.{u1} (Tropical.{u1} R) (SemilatticeSup.toHasSup.{u1} (Tropical.{u1} R) (Lattice.toSemilatticeSup.{u1} (Tropical.{u1} R) (DistribLattice.toLattice.{u1} (Tropical.{u1} R) (instDistribLattice.{u1} (Tropical.{u1} R) (Tropical.instLinearOrderTropical.{u1} R _inst_1))))) x y)) (HasSup.sup.{u1} R (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1)))) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y))
Case conversion may be inaccurate. Consider using '#align tropical.untrop_sup Tropical.untrop_supₓ'. -/
@[simp]
theorem untrop_sup (x y : Tropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  rfl
#align tropical.untrop_sup Tropical.untrop_sup

/- warning: tropical.untrop_max -> Tropical.untrop_max is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} R (Tropical.untrop.{u1} R (LinearOrder.max.{u1} (Tropical.{u1} R) (Tropical.linearOrder.{u1} R _inst_1) x y)) (LinearOrder.max.{u1} R _inst_1 (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} R (Tropical.untrop.{u1} R (Max.max.{u1} (Tropical.{u1} R) (LinearOrder.toMax.{u1} (Tropical.{u1} R) (Tropical.instLinearOrderTropical.{u1} R _inst_1)) x y)) (Max.max.{u1} R (LinearOrder.toMax.{u1} R _inst_1) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y))
Case conversion may be inaccurate. Consider using '#align tropical.untrop_max Tropical.untrop_maxₓ'. -/
@[simp]
theorem untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl
#align tropical.untrop_max Tropical.untrop_max

/- warning: tropical.min_eq_add -> Tropical.min_eq_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R], Eq.{succ u1} ((Tropical.{u1} R) -> (Tropical.{u1} R) -> (Tropical.{u1} R)) (LinearOrder.min.{u1} (Tropical.{u1} R) (Tropical.linearOrder.{u1} R _inst_1)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R], Eq.{succ u1} ((Tropical.{u1} R) -> (Tropical.{u1} R) -> (Tropical.{u1} R)) (Min.min.{u1} (Tropical.{u1} R) (LinearOrder.toMin.{u1} (Tropical.{u1} R) (Tropical.instLinearOrderTropical.{u1} R _inst_1))) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.1478 : Tropical.{u1} R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.1480 : Tropical.{u1} R) => HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x._@.Mathlib.Algebra.Tropical.Basic._hyg.1478 x._@.Mathlib.Algebra.Tropical.Basic._hyg.1480)
Case conversion may be inaccurate. Consider using '#align tropical.min_eq_add Tropical.min_eq_addₓ'. -/
@[simp]
theorem min_eq_add : (min : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl
#align tropical.min_eq_add Tropical.min_eq_add

/- warning: tropical.inf_eq_add -> Tropical.inf_eq_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R], Eq.{succ u1} ((Tropical.{u1} R) -> (Tropical.{u1} R) -> (Tropical.{u1} R)) (HasInf.inf.{u1} (Tropical.{u1} R) (SemilatticeInf.toHasInf.{u1} (Tropical.{u1} R) (Lattice.toSemilatticeInf.{u1} (Tropical.{u1} R) (LinearOrder.toLattice.{u1} (Tropical.{u1} R) (Tropical.linearOrder.{u1} R _inst_1))))) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R], Eq.{succ u1} ((Tropical.{u1} R) -> (Tropical.{u1} R) -> (Tropical.{u1} R)) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.1514 : Tropical.{u1} R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.1516 : Tropical.{u1} R) => HasInf.inf.{u1} (Tropical.{u1} R) (Lattice.toHasInf.{u1} (Tropical.{u1} R) (DistribLattice.toLattice.{u1} (Tropical.{u1} R) (instDistribLattice.{u1} (Tropical.{u1} R) (Tropical.instLinearOrderTropical.{u1} R _inst_1)))) x._@.Mathlib.Algebra.Tropical.Basic._hyg.1514 x._@.Mathlib.Algebra.Tropical.Basic._hyg.1516) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.1529 : Tropical.{u1} R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.1531 : Tropical.{u1} R) => HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x._@.Mathlib.Algebra.Tropical.Basic._hyg.1529 x._@.Mathlib.Algebra.Tropical.Basic._hyg.1531)
Case conversion may be inaccurate. Consider using '#align tropical.inf_eq_add Tropical.inf_eq_addₓ'. -/
@[simp]
theorem inf_eq_add : ((· ⊓ ·) : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl
#align tropical.inf_eq_add Tropical.inf_eq_add

/- warning: tropical.trop_max_def -> Tropical.trop_max_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (LinearOrder.max.{u1} (Tropical.{u1} R) (Tropical.linearOrder.{u1} R _inst_1) x y) (Tropical.trop.{u1} R (LinearOrder.max.{u1} R _inst_1 (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Max.max.{u1} (Tropical.{u1} R) (LinearOrder.toMax.{u1} (Tropical.{u1} R) (Tropical.instLinearOrderTropical.{u1} R _inst_1)) x y) (Tropical.trop.{u1} R (Max.max.{u1} R (LinearOrder.toMax.{u1} R _inst_1) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y)))
Case conversion may be inaccurate. Consider using '#align tropical.trop_max_def Tropical.trop_max_defₓ'. -/
theorem trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl
#align tropical.trop_max_def Tropical.trop_max_def

/- warning: tropical.trop_sup_def -> Tropical.trop_sup_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (HasSup.sup.{u1} (Tropical.{u1} R) (SemilatticeSup.toHasSup.{u1} (Tropical.{u1} R) (Lattice.toSemilatticeSup.{u1} (Tropical.{u1} R) (LinearOrder.toLattice.{u1} (Tropical.{u1} R) (Tropical.linearOrder.{u1} R _inst_1)))) x y) (Tropical.trop.{u1} R (HasSup.sup.{u1} R (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (LinearOrder.toLattice.{u1} R _inst_1))) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R) (y : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (HasSup.sup.{u1} (Tropical.{u1} R) (SemilatticeSup.toHasSup.{u1} (Tropical.{u1} R) (Lattice.toSemilatticeSup.{u1} (Tropical.{u1} R) (DistribLattice.toLattice.{u1} (Tropical.{u1} R) (instDistribLattice.{u1} (Tropical.{u1} R) (Tropical.instLinearOrderTropical.{u1} R _inst_1))))) x y) (Tropical.trop.{u1} R (HasSup.sup.{u1} R (SemilatticeSup.toHasSup.{u1} R (Lattice.toSemilatticeSup.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1)))) (Tropical.untrop.{u1} R x) (Tropical.untrop.{u1} R y)))
Case conversion may be inaccurate. Consider using '#align tropical.trop_sup_def Tropical.trop_sup_defₓ'. -/
theorem trop_sup_def (x y : Tropical R) : x ⊔ y = trop (untrop x ⊔ untrop y) :=
  rfl
#align tropical.trop_sup_def Tropical.trop_sup_def

/- warning: tropical.add_eq_left -> Tropical.add_eq_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {{x : Tropical.{u1} R}} {{y : Tropical.{u1} R}}, (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))) x y) -> (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {{x : Tropical.{u1} R}} {{y : Tropical.{u1} R}}, (LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) x y) -> (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) x)
Case conversion may be inaccurate. Consider using '#align tropical.add_eq_left Tropical.add_eq_leftₓ'. -/
@[simp]
theorem add_eq_left ⦃x y : Tropical R⦄ (h : x ≤ y) : x + y = x :=
  untrop_injective (by simpa using h)
#align tropical.add_eq_left Tropical.add_eq_left

/- warning: tropical.add_eq_right -> Tropical.add_eq_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {{x : Tropical.{u1} R}} {{y : Tropical.{u1} R}}, (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))) y x) -> (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {{x : Tropical.{u1} R}} {{y : Tropical.{u1} R}}, (LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) y x) -> (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) y)
Case conversion may be inaccurate. Consider using '#align tropical.add_eq_right Tropical.add_eq_rightₓ'. -/
@[simp]
theorem add_eq_right ⦃x y : Tropical R⦄ (h : y ≤ x) : x + y = y :=
  untrop_injective (by simpa using h)
#align tropical.add_eq_right Tropical.add_eq_right

/- warning: tropical.add_eq_left_iff -> Tropical.add_eq_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {x : Tropical.{u1} R} {y : Tropical.{u1} R}, Iff (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) x) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))) x y)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {x : Tropical.{u1} R} {y : Tropical.{u1} R}, Iff (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) x) (LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) x y)
Case conversion may be inaccurate. Consider using '#align tropical.add_eq_left_iff Tropical.add_eq_left_iffₓ'. -/
theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x ≤ y := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_left_iff]
#align tropical.add_eq_left_iff Tropical.add_eq_left_iff

/- warning: tropical.add_eq_right_iff -> Tropical.add_eq_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {x : Tropical.{u1} R} {y : Tropical.{u1} R}, Iff (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) y) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))) y x)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {x : Tropical.{u1} R} {y : Tropical.{u1} R}, Iff (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) y) (LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) y x)
Case conversion may be inaccurate. Consider using '#align tropical.add_eq_right_iff Tropical.add_eq_right_iffₓ'. -/
theorem add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_right_iff]
#align tropical.add_eq_right_iff Tropical.add_eq_right_iff

/- warning: tropical.add_self -> Tropical.add_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x x) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x x) x
Case conversion may be inaccurate. Consider using '#align tropical.add_self Tropical.add_selfₓ'. -/
@[simp]
theorem add_self (x : Tropical R) : x + x = x :=
  untrop_injective (min_eq_right le_rfl)
#align tropical.add_self Tropical.add_self

/- warning: tropical.bit0 -> Tropical.bit0 is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (bit0.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1) x) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] (x : Tropical.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (bit0.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1) x) x
Case conversion may be inaccurate. Consider using '#align tropical.bit0 Tropical.bit0ₓ'. -/
@[simp]
theorem bit0 (x : Tropical R) : bit0 x = x :=
  add_self x
#align tropical.bit0 Tropical.bit0

/- warning: tropical.add_eq_iff -> Tropical.add_eq_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {x : Tropical.{u1} R} {y : Tropical.{u1} R} {z : Tropical.{u1} R}, Iff (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) z) (Or (And (Eq.{succ u1} (Tropical.{u1} R) x z) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))) x y)) (And (Eq.{succ u1} (Tropical.{u1} R) y z) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))) y x)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {x : Tropical.{u1} R} {y : Tropical.{u1} R} {z : Tropical.{u1} R}, Iff (Eq.{succ u1} (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) z) (Or (And (Eq.{succ u1} (Tropical.{u1} R) x z) (LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) x y)) (And (Eq.{succ u1} (Tropical.{u1} R) y z) (LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) y x)))
Case conversion may be inaccurate. Consider using '#align tropical.add_eq_iff Tropical.add_eq_iffₓ'. -/
theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x :=
  by
  rw [trop_add_def, trop_eq_iff_eq_untrop]
  simp [min_eq_iff]
#align tropical.add_eq_iff Tropical.add_eq_iff

/- warning: tropical.add_eq_zero_iff -> Tropical.add_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {a : Tropical.{u1} (WithTop.{u1} R)} {b : Tropical.{u1} (WithTop.{u1} R)}, Iff (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (instHAdd.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasAdd.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R _inst_1))) a b) (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (OfNat.mk.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.zero.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasZero.{u1} (WithTop.{u1} R) (WithTop.hasTop.{u1} R)))))) (And (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) a (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (OfNat.mk.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.zero.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasZero.{u1} (WithTop.{u1} R) (WithTop.hasTop.{u1} R)))))) (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) b (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (OfNat.mk.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.zero.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasZero.{u1} (WithTop.{u1} R) (WithTop.hasTop.{u1} R)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] {a : Tropical.{u1} (WithTop.{u1} R)} {b : Tropical.{u1} (WithTop.{u1} R)}, Iff (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (instHAdd.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instAddTropical.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R _inst_1))) a b) (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instZeroTropical.{u1} (WithTop.{u1} R) (WithTop.top.{u1} R))))) (And (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) a (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instZeroTropical.{u1} (WithTop.{u1} R) (WithTop.top.{u1} R))))) (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) b (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instZeroTropical.{u1} (WithTop.{u1} R) (WithTop.top.{u1} R))))))
Case conversion may be inaccurate. Consider using '#align tropical.add_eq_zero_iff Tropical.add_eq_zero_iffₓ'. -/
@[simp]
theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
  by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp
#align tropical.add_eq_zero_iff Tropical.add_eq_zero_iff

instance [OrderTop R] : AddCommMonoid (Tropical R) :=
  { Tropical.hasZero,
    Tropical.addCommSemigroup with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _) }

end Order

section Monoid

/-- Tropical multiplication is the addition in the underlying `R`. -/
instance [Add R] : Mul (Tropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

#print Tropical.trop_add /-
@[simp]
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl
#align tropical.trop_add Tropical.trop_add
-/

#print Tropical.untrop_mul /-
@[simp]
theorem untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop y :=
  rfl
#align tropical.untrop_mul Tropical.untrop_mul
-/

#print Tropical.trop_mul_def /-
theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop y) :=
  rfl
#align tropical.trop_mul_def Tropical.trop_mul_def
-/

instance [Zero R] : One (Tropical R) :=
  ⟨trop 0⟩

#print Tropical.trop_zero /-
@[simp]
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl
#align tropical.trop_zero Tropical.trop_zero
-/

#print Tropical.untrop_one /-
@[simp]
theorem untrop_one [Zero R] : untrop (1 : Tropical R) = 0 :=
  rfl
#align tropical.untrop_one Tropical.untrop_one
-/

instance [LinearOrder R] [OrderTop R] [Zero R] : AddMonoidWithOne (Tropical R) :=
  { Tropical.hasOne,
    Tropical.addCommMonoid with
    natCast := fun n => if n = 0 then 0 else 1
    nat_cast_zero := rfl
    nat_cast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp [Nat.cast]) }

instance [Zero R] : Nontrivial (Tropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.Ne WithTop.top_ne_coe⟩⟩

instance [Neg R] : Inv (Tropical R) :=
  ⟨fun x => trop (-untrop x)⟩

#print Tropical.untrop_inv /-
@[simp]
theorem untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x :=
  rfl
#align tropical.untrop_inv Tropical.untrop_inv
-/

instance [Sub R] : Div (Tropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

#print Tropical.untrop_div /-
@[simp]
theorem untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl
#align tropical.untrop_div Tropical.untrop_div
-/

instance [AddSemigroup R] : Semigroup (Tropical R)
    where
  mul := (· * ·)
  mul_assoc _ _ _ := untrop_injective (add_assoc _ _ _)

instance [AddCommSemigroup R] : CommSemigroup (Tropical R) :=
  { Tropical.semigroup with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

instance {α : Type _} [SMul α R] : Pow (Tropical R) α where pow x n := trop <| n • untrop x

/- warning: tropical.untrop_pow -> Tropical.untrop_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u2, u1} α R] (x : Tropical.{u1} R) (n : α), Eq.{succ u1} R (Tropical.untrop.{u1} R (HPow.hPow.{u1, u2, u1} (Tropical.{u1} R) α (Tropical.{u1} R) (instHPow.{u1, u2} (Tropical.{u1} R) α (Tropical.hasPow.{u1, u2} R α _inst_1)) x n)) (SMul.smul.{u2, u1} α R _inst_1 n (Tropical.untrop.{u1} R x))
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} [_inst_1 : SMul.{u1, u2} α R] (x : Tropical.{u2} R) (n : α), Eq.{succ u2} R (Tropical.untrop.{u2} R (HPow.hPow.{u2, u1, u2} (Tropical.{u2} R) α (Tropical.{u2} R) (instHPow.{u2, u1} (Tropical.{u2} R) α (Tropical.instPowTropical.{u2, u1} R α _inst_1)) x n)) (HSMul.hSMul.{u1, u2, u2} α R R (instHSMul.{u1, u2} α R _inst_1) n (Tropical.untrop.{u2} R x))
Case conversion may be inaccurate. Consider using '#align tropical.untrop_pow Tropical.untrop_powₓ'. -/
@[simp]
theorem untrop_pow {α : Type _} [SMul α R] (x : Tropical R) (n : α) :
    untrop (x ^ n) = n • untrop x :=
  rfl
#align tropical.untrop_pow Tropical.untrop_pow

/- warning: tropical.trop_smul -> Tropical.trop_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} [_inst_1 : SMul.{u2, u1} α R] (x : R) (n : α), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (SMul.smul.{u2, u1} α R _inst_1 n x)) (HPow.hPow.{u1, u2, u1} (Tropical.{u1} R) α (Tropical.{u1} R) (instHPow.{u1, u2} (Tropical.{u1} R) α (Tropical.hasPow.{u1, u2} R α _inst_1)) (Tropical.trop.{u1} R x) n)
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} [_inst_1 : SMul.{u1, u2} α R] (x : R) (n : α), Eq.{succ u2} (Tropical.{u2} R) (Tropical.trop.{u2} R (HSMul.hSMul.{u1, u2, u2} α R R (instHSMul.{u1, u2} α R _inst_1) n x)) (HPow.hPow.{u2, u1, u2} (Tropical.{u2} R) α (Tropical.{u2} R) (instHPow.{u2, u1} (Tropical.{u2} R) α (Tropical.instPowTropical.{u2, u1} R α _inst_1)) (Tropical.trop.{u2} R x) n)
Case conversion may be inaccurate. Consider using '#align tropical.trop_smul Tropical.trop_smulₓ'. -/
@[simp]
theorem trop_smul {α : Type _} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl
#align tropical.trop_smul Tropical.trop_smul

instance [AddZeroClass R] : MulOneClass (Tropical R)
    where
  one := 1
  mul := (· * ·)
  one_mul _ := untrop_injective <| zero_add _
  mul_one _ := untrop_injective <| add_zero _

instance [AddMonoid R] : Monoid (Tropical R) :=
  { Tropical.mulOneClass,
    Tropical.semigroup with
    npow := fun n x => x ^ n
    npow_zero' := fun _ => untrop_injective <| zero_smul _ _
    npow_succ' := fun _ _ => untrop_injective <| succ_nsmul _ _ }

#print Tropical.trop_nsmul /-
@[simp]
theorem trop_nsmul [AddMonoid R] (x : R) (n : ℕ) : trop (n • x) = trop x ^ n :=
  rfl
#align tropical.trop_nsmul Tropical.trop_nsmul
-/

instance [AddCommMonoid R] : CommMonoid (Tropical R) :=
  { Tropical.monoid, Tropical.commSemigroup with }

instance [AddGroup R] : Group (Tropical R) :=
  { Tropical.monoid with
    inv := Inv.inv
    mul_left_inv := fun _ => untrop_injective <| add_left_neg _
    zpow := fun n x => trop <| n • untrop x
    zpow_zero' := fun _ => untrop_injective <| zero_zsmul _
    zpow_succ' := fun _ _ => untrop_injective <| AddGroup.zsmul_succ' _ _
    zpow_neg' := fun _ _ => untrop_injective <| AddGroup.zsmul_neg' _ _ }

instance [AddCommGroup R] : CommGroup (Tropical R) :=
  { Tropical.group with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

#print Tropical.untrop_zpow /-
@[simp]
theorem untrop_zpow [AddGroup R] (x : Tropical R) (n : ℤ) : untrop (x ^ n) = n • untrop x :=
  rfl
#align tropical.untrop_zpow Tropical.untrop_zpow
-/

#print Tropical.trop_zsmul /-
@[simp]
theorem trop_zsmul [AddGroup R] (x : R) (n : ℤ) : trop (n • x) = trop x ^ n :=
  rfl
#align tropical.trop_zsmul Tropical.trop_zsmul
-/

end Monoid

section Distrib

#print Tropical.covariant_mul /-
instance covariant_mul [LE R] [Add R] [CovariantClass R R (· + ·) (· ≤ ·)] :
    CovariantClass (Tropical R) (Tropical R) (· * ·) (· ≤ ·) :=
  ⟨fun x y z h => add_le_add_left h _⟩
#align tropical.covariant_mul Tropical.covariant_mul
-/

#print Tropical.covariant_swap_mul /-
instance covariant_swap_mul [LE R] [Add R] [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] :
    CovariantClass (Tropical R) (Tropical R) (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨fun x y z h => add_le_add_right h _⟩
#align tropical.covariant_swap_mul Tropical.covariant_swap_mul
-/

/- warning: tropical.covariant_add -> Tropical.covariant_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R], CovariantClass.{u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1))) (LE.le.{u1} (Tropical.{u1} R) (Tropical.hasLe.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R], CovariantClass.{u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3275 : Tropical.{u1} R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3277 : Tropical.{u1} R) => HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x._@.Mathlib.Algebra.Tropical.Basic._hyg.3275 x._@.Mathlib.Algebra.Tropical.Basic._hyg.3277) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3290 : Tropical.{u1} R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3292 : Tropical.{u1} R) => LE.le.{u1} (Tropical.{u1} R) (Tropical.instLETropical.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))) x._@.Mathlib.Algebra.Tropical.Basic._hyg.3290 x._@.Mathlib.Algebra.Tropical.Basic._hyg.3292)
Case conversion may be inaccurate. Consider using '#align tropical.covariant_add Tropical.covariant_addₓ'. -/
instance covariant_add [LinearOrder R] : CovariantClass (Tropical R) (Tropical R) (· + ·) (· ≤ ·) :=
  ⟨fun x y z h => by
    cases' le_total x y with hx hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      cases' le_total x z with hx hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩
#align tropical.covariant_add Tropical.covariant_add

#print Tropical.covariant_mul_lt /-
instance covariant_mul_lt [LT R] [Add R] [CovariantClass R R (· + ·) (· < ·)] :
    CovariantClass (Tropical R) (Tropical R) (· * ·) (· < ·) :=
  ⟨fun x y z h => add_lt_add_left h _⟩
#align tropical.covariant_mul_lt Tropical.covariant_mul_lt
-/

#print Tropical.covariant_swap_mul_lt /-
instance covariant_swap_mul_lt [Preorder R] [Add R]
    [CovariantClass R R (Function.swap (· + ·)) (· < ·)] :
    CovariantClass (Tropical R) (Tropical R) (Function.swap (· * ·)) (· < ·) :=
  ⟨fun x y z h => add_lt_add_right h _⟩
#align tropical.covariant_swap_mul_lt Tropical.covariant_swap_mul_lt
-/

instance [LinearOrder R] [Add R] [CovariantClass R R (· + ·) (· ≤ ·)]
    [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] : Distrib (Tropical R)
    where
  mul := (· * ·)
  add := (· + ·)
  left_distrib _ _ _ := untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

/- warning: tropical.add_pow -> Tropical.add_pow is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : AddMonoid.{u1} R] [_inst_3 : CovariantClass.{u1, u1} R R (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_2)))) (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1))))))] [_inst_4 : CovariantClass.{u1, u1} R R (Function.swap.{succ u1, succ u1, succ u1} R R (fun (ᾰ : R) (ᾰ : R) => R) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_2))))) (LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1))))))] (x : Tropical.{u1} R) (y : Tropical.{u1} R) (n : Nat), Eq.{succ u1} (Tropical.{u1} R) (HPow.hPow.{u1, 0, u1} (Tropical.{u1} R) Nat (Tropical.{u1} R) (instHPow.{u1, 0} (Tropical.{u1} R) Nat (Tropical.hasPow.{u1, 0} R Nat (AddMonoid.SMul.{u1} R _inst_2))) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) x y) n) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.hasAdd.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} (Tropical.{u1} R) Nat (Tropical.{u1} R) (instHPow.{u1, 0} (Tropical.{u1} R) Nat (Tropical.hasPow.{u1, 0} R Nat (AddMonoid.SMul.{u1} R _inst_2))) x n) (HPow.hPow.{u1, 0, u1} (Tropical.{u1} R) Nat (Tropical.{u1} R) (instHPow.{u1, 0} (Tropical.{u1} R) Nat (Tropical.hasPow.{u1, 0} R Nat (AddMonoid.SMul.{u1} R _inst_2))) y n))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : AddMonoid.{u1} R] [_inst_3 : CovariantClass.{u1, u1} R R (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3850 : R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3852 : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_2))) x._@.Mathlib.Algebra.Tropical.Basic._hyg.3850 x._@.Mathlib.Algebra.Tropical.Basic._hyg.3852) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3865 : R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3867 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1)))))) x._@.Mathlib.Algebra.Tropical.Basic._hyg.3865 x._@.Mathlib.Algebra.Tropical.Basic._hyg.3867)] [_inst_4 : CovariantClass.{u1, u1} R R (Function.swap.{succ u1, succ u1, succ u1} R R (fun (ᾰ : R) (ᾰ : R) => R) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3887 : R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3889 : R) => HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_2))) x._@.Mathlib.Algebra.Tropical.Basic._hyg.3887 x._@.Mathlib.Algebra.Tropical.Basic._hyg.3889)) (fun (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3902 : R) (x._@.Mathlib.Algebra.Tropical.Basic._hyg.3904 : R) => LE.le.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1)))))) x._@.Mathlib.Algebra.Tropical.Basic._hyg.3902 x._@.Mathlib.Algebra.Tropical.Basic._hyg.3904)] (x : Tropical.{u1} R) (y : Tropical.{u1} R) (n : Nat), Eq.{succ u1} (Tropical.{u1} R) (HPow.hPow.{u1, 0, u1} (Tropical.{u1} R) Nat (Tropical.{u1} R) (instHPow.{u1, 0} (Tropical.{u1} R) Nat (Tropical.instPowTropical.{u1, 0} R Nat (AddMonoid.SMul.{u1} R _inst_2))) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) x y) n) (HAdd.hAdd.{u1, u1, u1} (Tropical.{u1} R) (Tropical.{u1} R) (Tropical.{u1} R) (instHAdd.{u1} (Tropical.{u1} R) (Tropical.instAddTropical.{u1} R _inst_1)) (HPow.hPow.{u1, 0, u1} (Tropical.{u1} R) Nat (Tropical.{u1} R) (instHPow.{u1, 0} (Tropical.{u1} R) Nat (Tropical.instPowTropical.{u1, 0} R Nat (AddMonoid.SMul.{u1} R _inst_2))) x n) (HPow.hPow.{u1, 0, u1} (Tropical.{u1} R) Nat (Tropical.{u1} R) (instHPow.{u1, 0} (Tropical.{u1} R) Nat (Tropical.instPowTropical.{u1, 0} R Nat (AddMonoid.SMul.{u1} R _inst_2))) y n))
Case conversion may be inaccurate. Consider using '#align tropical.add_pow Tropical.add_powₓ'. -/
@[simp]
theorem add_pow [LinearOrder R] [AddMonoid R] [CovariantClass R R (· + ·) (· ≤ ·)]
    [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] (x y : Tropical R) (n : ℕ) :
    (x + y) ^ n = x ^ n + y ^ n := by
  cases' le_total x y with h h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_of_le_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_of_le_left' h _)]
#align tropical.add_pow Tropical.add_pow

end Distrib

section Semiring

variable [LinearOrderedAddCommMonoidWithTop R]

instance : CommSemiring (Tropical R) :=
  { Tropical.addMonoidWithOne, Tropical.distrib, Tropical.addCommMonoid,
    Tropical.commMonoid with
    zero_mul := fun _ => untrop_injective (top_add _)
    mul_zero := fun _ => untrop_injective (add_top _) }

/- warning: tropical.succ_nsmul -> Tropical.succ_nsmul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : LinearOrder.{u1} R] [_inst_3 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_2)))))] (x : Tropical.{u1} R) (n : Nat), Eq.{succ u1} (Tropical.{u1} R) (SMul.smul.{0, u1} Nat (Tropical.{u1} R) (AddMonoid.SMul.{u1} (Tropical.{u1} R) (AddCommMonoid.toAddMonoid.{u1} (Tropical.{u1} R) (Tropical.addCommMonoid.{u1} R _inst_2 _inst_3))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) x) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : LinearOrder.{u1} R] [_inst_3 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_2))))))] (x : Tropical.{u1} R) (n : Nat), Eq.{succ u1} (Tropical.{u1} R) (HSMul.hSMul.{0, u1, u1} Nat (Tropical.{u1} R) (Tropical.{u1} R) (instHSMul.{0, u1} Nat (Tropical.{u1} R) (AddMonoid.SMul.{u1} (Tropical.{u1} R) (AddCommMonoid.toAddMonoid.{u1} (Tropical.{u1} R) (Tropical.instAddCommMonoidTropical.{u1} R _inst_2 _inst_3)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) x) x
Case conversion may be inaccurate. Consider using '#align tropical.succ_nsmul Tropical.succ_nsmulₓ'. -/
@[simp]
theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : ℕ) : (n + 1) • x = x :=
  by
  induction' n with n IH
  · simp
  · rw [add_nsmul, IH, one_nsmul, add_self]
#align tropical.succ_nsmul Tropical.succ_nsmul

/- warning: tropical.mul_eq_zero_iff -> Tropical.mul_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_2 : LinearOrderedAddCommMonoid.{u1} R] {a : Tropical.{u1} (WithTop.{u1} R)} {b : Tropical.{u1} (WithTop.{u1} R)}, Iff (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) (HMul.hMul.{u1, u1, u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (instHMul.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasMul.{u1} (WithTop.{u1} R) (WithTop.add.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (OrderedAddCommMonoid.toAddCommMonoid.{u1} R (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} R _inst_2)))))))) a b) (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (OfNat.mk.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.zero.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasZero.{u1} (WithTop.{u1} R) (WithTop.hasTop.{u1} R)))))) (Or (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) a (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (OfNat.mk.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.zero.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasZero.{u1} (WithTop.{u1} R) (WithTop.hasTop.{u1} R)))))) (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) b (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (OfNat.mk.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.zero.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.hasZero.{u1} (WithTop.{u1} R) (WithTop.hasTop.{u1} R)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_2 : LinearOrderedAddCommMonoid.{u1} R] {a : Tropical.{u1} (WithTop.{u1} R)} {b : Tropical.{u1} (WithTop.{u1} R)}, Iff (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) (HMul.hMul.{u1, u1, u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (Tropical.{u1} (WithTop.{u1} R)) (instHMul.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instMulTropical.{u1} (WithTop.{u1} R) (WithTop.add.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R (AddCommMonoid.toAddMonoid.{u1} R (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} R _inst_2))))))) a b) (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instZeroTropical.{u1} (WithTop.{u1} R) (WithTop.top.{u1} R))))) (Or (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) a (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instZeroTropical.{u1} (WithTop.{u1} R) (WithTop.top.{u1} R))))) (Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) b (OfNat.ofNat.{u1} (Tropical.{u1} (WithTop.{u1} R)) 0 (Zero.toOfNat0.{u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.instZeroTropical.{u1} (WithTop.{u1} R) (WithTop.top.{u1} R))))))
Case conversion may be inaccurate. Consider using '#align tropical.mul_eq_zero_iff Tropical.mul_eq_zero_iffₓ'. -/
-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
@[simp]
theorem mul_eq_zero_iff {R : Type _} [LinearOrderedAddCommMonoid R] {a b : Tropical (WithTop R)} :
    a * b = 0 ↔ a = 0 ∨ b = 0 := by simp [← untrop_inj_iff, WithTop.add_eq_top]
#align tropical.mul_eq_zero_iff Tropical.mul_eq_zero_iff

instance {R : Type _} [LinearOrderedAddCommMonoid R] : NoZeroDivisors (Tropical (WithTop R)) :=
  ⟨fun _ _ => mul_eq_zero_iff.mp⟩

end Semiring

end Tropical

