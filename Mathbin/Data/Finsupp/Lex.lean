/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.finsupp.lex
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Order
import Mathbin.Data.Dfinsupp.Lex
import Mathbin.Data.Finsupp.ToDfinsupp

/-!
# Lexicographic order on finitely supported functions

This file defines the lexicographic order on `finsupp`.
-/


variable {α N : Type _}

namespace Finsupp

section NHasZero

variable [Zero N]

#print Finsupp.Lex /-
/-- `finsupp.lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `lex (α →₀ N)` has an order given by `finsupp.lex (<) (<)`.
-/
protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r (fun _ => s) x y
#align finsupp.lex Finsupp.Lex
-/

/- warning: pi.lex_eq_finsupp_lex -> Pi.lex_eq_finsupp_lex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : Zero.{u2} N] {r : α -> α -> Prop} {s : N -> N -> Prop} (a : Finsupp.{u1, u2} α N _inst_1) (b : Finsupp.{u1, u2} α N _inst_1), Eq.{1} Prop (Pi.Lex.{u1, u2} α (fun (_x : α) => N) r (fun (_x : α) => s) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_1) (fun (_x : Finsupp.{u1, u2} α N _inst_1) => α -> N) (Finsupp.hasCoeToFun.{u1, u2} α N _inst_1) a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_1) (fun (_x : Finsupp.{u1, u2} α N _inst_1) => α -> N) (Finsupp.hasCoeToFun.{u1, u2} α N _inst_1) b)) (Finsupp.Lex.{u1, u2} α N _inst_1 r s a b)
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [_inst_1 : Zero.{u1} N] {r : α -> α -> Prop} {s : N -> N -> Prop} (a : Finsupp.{u2, u1} α N _inst_1) (b : Finsupp.{u2, u1} α N _inst_1), Eq.{1} Prop (Pi.Lex.{u2, u1} α (fun {_x : α} => N) r (fun {_x : α} => s) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α N _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u2, u1} α N _inst_1) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α N _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u2, u1} α N _inst_1) b)) (Finsupp.Lex.{u2, u1} α N _inst_1 r s a b)
Case conversion may be inaccurate. Consider using '#align pi.lex_eq_finsupp_lex Pi.lex_eq_finsupp_lexₓ'. -/
theorem Pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
    Pi.Lex r (fun _ => s) (a : α → N) (b : α → N) = Finsupp.Lex r s a b :=
  rfl
#align pi.lex_eq_finsupp_lex Pi.lex_eq_finsupp_lex

/- warning: finsupp.lex_def -> Finsupp.lex_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : Zero.{u2} N] {r : α -> α -> Prop} {s : N -> N -> Prop} {a : Finsupp.{u1, u2} α N _inst_1} {b : Finsupp.{u1, u2} α N _inst_1}, Iff (Finsupp.Lex.{u1, u2} α N _inst_1 r s a b) (Exists.{succ u1} α (fun (j : α) => And (forall (d : α), (r d j) -> (Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_1) (fun (_x : Finsupp.{u1, u2} α N _inst_1) => α -> N) (Finsupp.hasCoeToFun.{u1, u2} α N _inst_1) a d) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_1) (fun (_x : Finsupp.{u1, u2} α N _inst_1) => α -> N) (Finsupp.hasCoeToFun.{u1, u2} α N _inst_1) b d))) (s (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_1) (fun (_x : Finsupp.{u1, u2} α N _inst_1) => α -> N) (Finsupp.hasCoeToFun.{u1, u2} α N _inst_1) a j) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α N _inst_1) (fun (_x : Finsupp.{u1, u2} α N _inst_1) => α -> N) (Finsupp.hasCoeToFun.{u1, u2} α N _inst_1) b j))))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [_inst_1 : Zero.{u1} N] {r : α -> α -> Prop} {s : N -> N -> Prop} {a : Finsupp.{u2, u1} α N _inst_1} {b : Finsupp.{u2, u1} α N _inst_1}, Iff (Finsupp.Lex.{u2, u1} α N _inst_1 r s a b) (Exists.{succ u2} α (fun (j : α) => And (forall (d : α), (r d j) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) d) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α N _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u2, u1} α N _inst_1) a d) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α N _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u2, u1} α N _inst_1) b d))) (s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α N _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u2, u1} α N _inst_1) a j) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α N _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => N) _x) (Finsupp.funLike.{u2, u1} α N _inst_1) b j))))
Case conversion may be inaccurate. Consider using '#align finsupp.lex_def Finsupp.lex_defₓ'. -/
theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  Iff.rfl
#align finsupp.lex_def Finsupp.lex_def

/- warning: finsupp.lex_eq_inv_image_dfinsupp_lex -> Finsupp.lex_eq_invImage_dfinsupp_lex is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : Zero.{u2} N] (r : α -> α -> Prop) (s : N -> N -> Prop), Eq.{max (max (succ u1) (succ u2)) 1} ((Finsupp.{u1, u2} α N _inst_1) -> (Finsupp.{u1, u2} α N _inst_1) -> Prop) (Finsupp.Lex.{u1, u2} α N _inst_1 r s) (InvImage.{max (succ u1) (succ u2), succ (max u1 u2)} (Finsupp.{u1, u2} α N _inst_1) (Dfinsupp.{u1, u2} α (fun (i : α) => N) (fun (i : α) => _inst_1)) (Dfinsupp.Lex.{u1, u2} α (fun (a : α) => N) (fun (i : α) => _inst_1) r (fun (a : α) => s)) (Finsupp.toDfinsupp.{u1, u2} α N _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [_inst_1 : Zero.{u1} N] (r : α -> α -> Prop) (s : N -> N -> Prop), Eq.{max (succ u2) (succ u1)} ((Finsupp.{u2, u1} α N _inst_1) -> (Finsupp.{u2, u1} α N _inst_1) -> Prop) (Finsupp.Lex.{u2, u1} α N _inst_1 r s) (InvImage.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u2, u1} α N _inst_1) (Dfinsupp.{u2, u1} α (fun (i : α) => N) (fun (i : α) => _inst_1)) (Dfinsupp.Lex.{u2, u1} α (fun {a : α} => N) (fun (i : α) => _inst_1) r (fun {a : α} => s)) (Finsupp.toDfinsupp.{u2, u1} α N _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.lex_eq_inv_image_dfinsupp_lex Finsupp.lex_eq_invImage_dfinsupp_lexₓ'. -/
theorem lex_eq_invImage_dfinsupp_lex (r : α → α → Prop) (s : N → N → Prop) :
    Finsupp.Lex r s = InvImage (Dfinsupp.Lex r fun a => s) toDfinsupp :=
  rfl
#align finsupp.lex_eq_inv_image_dfinsupp_lex Finsupp.lex_eq_invImage_dfinsupp_lex

instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g => Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

#print Finsupp.lex_lt_of_lt_of_preorder /-
theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  Dfinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDfinsupp < y.toDfinsupp)
#align finsupp.lex_lt_of_lt_of_preorder Finsupp.lex_lt_of_lt_of_preorder
-/

#print Finsupp.lex_lt_of_lt /-
theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    Pi.Lex r (fun i => (· < ·)) x y :=
  Dfinsupp.lex_lt_of_lt r (id hlt : x.toDfinsupp < y.toDfinsupp)
#align finsupp.lex_lt_of_lt Finsupp.lex_lt_of_lt
-/

/- warning: finsupp.lex.is_strict_order -> Finsupp.Lex.isStrictOrder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : Zero.{u2} N] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : PartialOrder.{u2} N], IsStrictOrder.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1)) (LT.lt.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1)) (Finsupp.Lex.hasLt.{u1, u2} α N _inst_1 (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_2))))) (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N _inst_3))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : Zero.{u2} N] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : PartialOrder.{u2} N], IsStrictOrder.{max u2 u1} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N _inst_1)) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.436 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N _inst_1)) (x._@.Mathlib.Data.Finsupp.Lex._hyg.438 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N _inst_1)) => LT.lt.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N _inst_1)) (Finsupp.instLTLexFinsupp.{u1, u2} α N _inst_1 (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_2)))))) (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N _inst_3))) x._@.Mathlib.Data.Finsupp.Lex._hyg.436 x._@.Mathlib.Data.Finsupp.Lex._hyg.438)
Case conversion may be inaccurate. Consider using '#align finsupp.lex.is_strict_order Finsupp.Lex.isStrictOrderₓ'. -/
instance Lex.isStrictOrder [LinearOrder α] [PartialOrder N] :
    IsStrictOrder (Lex (α →₀ N)) (· < ·) :=
  let i : IsStrictOrder (Lex (α → N)) (· < ·) := Pi.Lex.isStrictOrder
  { irrefl := toLex.Surjective.forall.2 fun a => @irrefl _ _ i.to_isIrrefl a
    trans := toLex.Surjective.forall₃.2 fun a b c => @trans _ _ i.to_isTrans a b c }
#align finsupp.lex.is_strict_order Finsupp.Lex.isStrictOrder

variable [LinearOrder α]

#print Finsupp.Lex.partialOrder /-
/-- The partial order on `finsupp`s obtained by the lexicographic ordering.
See `finsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α →₀ N)) :=
  PartialOrder.lift (fun x => toLex ⇑(ofLex x)) Finsupp.coeFn_injective
#align finsupp.lex.partial_order Finsupp.Lex.partialOrder
-/

#print Finsupp.Lex.linearOrder /-
--fun_like.coe_injective
/-- The linear order on `finsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α →₀ N)) :=
  { Lex.partialOrder,
    LinearOrder.lift' (toLex ∘ toDfinsupp ∘ ofLex) finsuppEquivDfinsupp.Injective with }
#align finsupp.lex.linear_order Finsupp.Lex.linearOrder
-/

variable [PartialOrder N]

/- warning: finsupp.to_lex_monotone -> Finsupp.toLex_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : Zero.{u2} N] [_inst_2 : LinearOrder.{u1} α] [_inst_3 : PartialOrder.{u2} N], Monotone.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1)) (Finsupp.preorder.{u1, u2} α N _inst_1 (PartialOrder.toPreorder.{u2} N _inst_3)) (PartialOrder.toPreorder.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1)) (Finsupp.Lex.partialOrder.{u1, u2} α N _inst_1 _inst_2 _inst_3)) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1))) (fun (_x : Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1))) => (Finsupp.{u1, u2} α N _inst_1) -> (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1))) (Equiv.hasCoeToFun.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1))) (toLex.{max u1 u2} (Finsupp.{u1, u2} α N _inst_1)))
but is expected to have type
  forall {α : Type.{u2}} {N : Type.{u1}} [_inst_1 : Zero.{u1} N] [_inst_2 : LinearOrder.{u2} α] [_inst_3 : PartialOrder.{u1} N], Monotone.{max u2 u1, max u2 u1} (Finsupp.{u2, u1} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_1)) (Finsupp.preorder.{u2, u1} α N _inst_1 (PartialOrder.toPreorder.{u1} N _inst_3)) (PartialOrder.toPreorder.{max u2 u1} (Lex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_1)) (Finsupp.Lex.partialOrder.{u2, u1} α N _inst_1 _inst_2 _inst_3)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u2, u1} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_1))) (Finsupp.{u2, u1} α N _inst_1) (fun (_x : Finsupp.{u2, u1} α N _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finsupp.{u2, u1} α N _inst_1) => Lex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_1)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Finsupp.{u2, u1} α N _inst_1) (Lex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_1))) (toLex.{max u1 u2} (Finsupp.{u2, u1} α N _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.to_lex_monotone Finsupp.toLex_monotoneₓ'. -/
theorem toLex_monotone : Monotone (@toLex (α →₀ N)) := fun a b h =>
  Dfinsupp.toLex_monotone (id h : ∀ i, ofLex (toDfinsupp a) i ≤ ofLex (toDfinsupp b) i)
#align finsupp.to_lex_monotone Finsupp.toLex_monotone

#print Finsupp.lt_of_forall_lt_of_lt /-
theorem lt_of_forall_lt_of_lt (a b : Lex (α →₀ N)) (i : α) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b := fun h1 h2 => ⟨i, h1, h2⟩
#align finsupp.lt_of_forall_lt_of_lt Finsupp.lt_of_forall_lt_of_lt
-/

end NHasZero

section Covariants

variable [LinearOrder α] [AddMonoid N] [LinearOrder N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `covariant_class` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `lex (α →₀ N)` may fail to be
monotone, when it is "just" monotone on `N`.

See `counterexamples.zero_divisors_in_add_monoid_algebras` for a counterexample. -/


section Left

variable [CovariantClass N N (· + ·) (· < ·)]

/- warning: finsupp.lex.covariant_class_lt_left -> Finsupp.Lex.covariantClass_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toHasAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))))], CovariantClass.{max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (instHAdd.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.hasAdd.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) (Finsupp.hasAdd.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2))))) (LT.lt.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Finsupp.Lex.hasLt.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3)))))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.927 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.929 : N) => HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) x._@.Mathlib.Data.Finsupp.Lex._hyg.927 x._@.Mathlib.Data.Finsupp.Lex._hyg.929) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.942 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.944 : N) => LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3)))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.942 x._@.Mathlib.Data.Finsupp.Lex._hyg.944)], CovariantClass.{max u2 u1, max u2 u1} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.978 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.980 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instHAdd.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instAddLex.{max u1 u2} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2)) (Finsupp.add.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) x._@.Mathlib.Data.Finsupp.Lex._hyg.978 x._@.Mathlib.Data.Finsupp.Lex._hyg.980) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.993 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.995 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => LT.lt.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Finsupp.instLTLexFinsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3))))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.993 x._@.Mathlib.Data.Finsupp.Lex._hyg.995)
Case conversion may be inaccurate. Consider using '#align finsupp.lex.covariant_class_lt_left Finsupp.Lex.covariantClass_lt_leftₓ'. -/
instance Lex.covariantClass_lt_left :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg ((· + ·) _) (lta j ja), add_lt_add_left ha _⟩⟩
#align finsupp.lex.covariant_class_lt_left Finsupp.Lex.covariantClass_lt_left

/- warning: finsupp.lex.covariant_class_le_left -> Finsupp.Lex.covariantClass_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toHasAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))))], CovariantClass.{max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (instHAdd.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.hasAdd.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) (Finsupp.hasAdd.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2))))) (LE.le.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Preorder.toLE.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (PartialOrder.toPreorder.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Finsupp.Lex.partialOrder.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)) _inst_1 (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3)))))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1082 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1084 : N) => HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1082 x._@.Mathlib.Data.Finsupp.Lex._hyg.1084) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1097 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1099 : N) => LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3)))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1097 x._@.Mathlib.Data.Finsupp.Lex._hyg.1099)], CovariantClass.{max u2 u1, max u2 u1} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1133 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1135 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instHAdd.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instAddLex.{max u1 u2} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2)) (Finsupp.add.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1133 x._@.Mathlib.Data.Finsupp.Lex._hyg.1135) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1148 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1150 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => LE.le.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Preorder.toLE.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (PartialOrder.toPreorder.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Finsupp.Lex.partialOrder.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2) _inst_1 (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3))))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1148 x._@.Mathlib.Data.Finsupp.Lex._hyg.1150)
Case conversion may be inaccurate. Consider using '#align finsupp.lex.covariant_class_le_left Finsupp.Lex.covariantClass_le_leftₓ'. -/
instance Lex.covariantClass_le_left :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· ≤ ·) :=
  Add.to_covariantClass_left _
#align finsupp.lex.covariant_class_le_left Finsupp.Lex.covariantClass_le_left

end Left

section Right

variable [CovariantClass N N (Function.swap (· + ·)) (· < ·)]

/- warning: finsupp.lex.covariant_class_lt_right -> Finsupp.Lex.covariantClass_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (Function.swap.{succ u2, succ u2, succ u2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toHasAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))))) (LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))))], CovariantClass.{max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Function.swap.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (fun (ᾰ : Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (ᾰ : Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) => Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (instHAdd.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.hasAdd.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) (Finsupp.hasAdd.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))))) (LT.lt.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Finsupp.Lex.hasLt.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3)))))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (Function.swap.{succ u2, succ u2, succ u2} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1241 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1243 : N) => HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1241 x._@.Mathlib.Data.Finsupp.Lex._hyg.1243)) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1256 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1258 : N) => LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3)))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1256 x._@.Mathlib.Data.Finsupp.Lex._hyg.1258)], CovariantClass.{max u2 u1, max u2 u1} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Function.swap.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (fun (ᾰ : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (ᾰ : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1295 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1297 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instHAdd.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instAddLex.{max u1 u2} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2)) (Finsupp.add.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1295 x._@.Mathlib.Data.Finsupp.Lex._hyg.1297)) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1310 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1312 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => LT.lt.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Finsupp.instLTLexFinsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2) (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3))))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1310 x._@.Mathlib.Data.Finsupp.Lex._hyg.1312)
Case conversion may be inaccurate. Consider using '#align finsupp.lex.covariant_class_lt_right Finsupp.Lex.covariantClass_lt_rightₓ'. -/
instance Lex.covariantClass_lt_right :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩
#align finsupp.lex.covariant_class_lt_right Finsupp.Lex.covariantClass_lt_right

/- warning: finsupp.lex.covariant_class_le_right -> Finsupp.Lex.covariantClass_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (Function.swap.{succ u2, succ u2, succ u2} N N (fun (ᾰ : N) (ᾰ : N) => N) (HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toHasAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))))) (LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3))))))], CovariantClass.{max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Function.swap.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (fun (ᾰ : Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (ᾰ : Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) => Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (instHAdd.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Lex.hasAdd.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) (Finsupp.hasAdd.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))))) (LE.le.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Preorder.toLE.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (PartialOrder.toPreorder.{max u1 u2} (Lex.{max u1 u2} (Finsupp.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) (Finsupp.Lex.partialOrder.{u1, u2} α N (AddZeroClass.toHasZero.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2)) _inst_1 (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (LinearOrder.toLattice.{u2} N _inst_3)))))))
but is expected to have type
  forall {α : Type.{u1}} {N : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : AddMonoid.{u2} N] [_inst_3 : LinearOrder.{u2} N] [_inst_4 : CovariantClass.{u2, u2} N N (Function.swap.{succ u2, succ u2, succ u2} N N (fun (ᾰ : N) (ᾰ : N) => N) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1414 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1416 : N) => HAdd.hAdd.{u2, u2, u2} N N N (instHAdd.{u2} N (AddZeroClass.toAdd.{u2} N (AddMonoid.toAddZeroClass.{u2} N _inst_2))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1414 x._@.Mathlib.Data.Finsupp.Lex._hyg.1416)) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1429 : N) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1431 : N) => LT.lt.{u2} N (Preorder.toLT.{u2} N (PartialOrder.toPreorder.{u2} N (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3)))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1429 x._@.Mathlib.Data.Finsupp.Lex._hyg.1431)], CovariantClass.{max u2 u1, max u2 u1} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Function.swap.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (fun (ᾰ : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (ᾰ : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1468 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1470 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instHAdd.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (instAddLex.{max u1 u2} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2)) (Finsupp.add.{u1, u2} α N (AddMonoid.toAddZeroClass.{u2} N _inst_2)))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1468 x._@.Mathlib.Data.Finsupp.Lex._hyg.1470)) (fun (x._@.Mathlib.Data.Finsupp.Lex._hyg.1483 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (x._@.Mathlib.Data.Finsupp.Lex._hyg.1485 : Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) => LE.le.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Preorder.toLE.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (PartialOrder.toPreorder.{max u1 u2} (Lex.{max u2 u1} (Finsupp.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2))) (Finsupp.Lex.partialOrder.{u1, u2} α N (AddMonoid.toZero.{u2} N _inst_2) _inst_1 (SemilatticeInf.toPartialOrder.{u2} N (Lattice.toSemilatticeInf.{u2} N (DistribLattice.toLattice.{u2} N (instDistribLattice.{u2} N _inst_3))))))) x._@.Mathlib.Data.Finsupp.Lex._hyg.1483 x._@.Mathlib.Data.Finsupp.Lex._hyg.1485)
Case conversion may be inaccurate. Consider using '#align finsupp.lex.covariant_class_le_right Finsupp.Lex.covariantClass_le_rightₓ'. -/
instance Lex.covariantClass_le_right :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· ≤ ·) :=
  Add.to_covariantClass_right _
#align finsupp.lex.covariant_class_le_right Finsupp.Lex.covariantClass_le_right

end Right

end Covariants

end Finsupp

