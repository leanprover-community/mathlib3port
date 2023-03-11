/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.sym.sym2
! leanprover-community/mathlib commit fac369018417f980cec5fcdafc766a69f88d8cfe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Prod
import Mathbin.Data.Sym.Basic
import Mathbin.Data.SetLike.Basic
import Mathbin.Tactic.Linarith.Default

/-!
# The symmetric square

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `data.sym.basic`). The equivalence is `sym2.equiv_sym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `sym2.equiv_multiset`), there is a
`has_mem` instance `sym2.mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : sym2 α`, then `h.other` is the other
element of the pair, defined using `classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `sym2` is provided as `sym2.lift`, which
states that functions from `sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `sym2.from_rel` which is a special case of `sym2.lift`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
-/


open Finset Function Sym

universe u

variable {α β γ : Type _}

namespace Sym2

#print Sym2.Rel /-
/-- This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive Rel (α : Type u) : α × α → α × α → Prop
  | refl (x y : α) : Rel (x, y) (x, y)
  | swap (x y : α) : Rel (x, y) (y, x)
#align sym2.rel Sym2.Rel
-/

attribute [refl] rel.refl

#print Sym2.Rel.symm /-
@[symm]
theorem Rel.symm {x y : α × α} : Rel α x y → Rel α y x := by rintro ⟨_, _⟩ <;> constructor
#align sym2.rel.symm Sym2.Rel.symm
-/

#print Sym2.Rel.trans /-
@[trans]
theorem Rel.trans {x y z : α × α} (a : Rel α x y) (b : Rel α y z) : Rel α x z := by
  casesm*Rel _ _ _ <;> first |apply rel.refl|apply rel.swap
#align sym2.rel.trans Sym2.Rel.trans
-/

#print Sym2.Rel.is_equivalence /-
theorem Rel.is_equivalence : Equivalence (Rel α) := by tidy <;> apply rel.trans <;> assumption
#align sym2.rel.is_equivalence Sym2.Rel.is_equivalence
-/

#print Sym2.Rel.setoid /-
instance Rel.setoid (α : Type u) : Setoid (α × α) :=
  ⟨Rel α, Rel.is_equivalence⟩
#align sym2.rel.setoid Sym2.Rel.setoid
-/

#print Sym2.rel_iff /-
@[simp]
theorem rel_iff {x y z w : α} : (x, y) ≈ (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
  by
  constructor <;> intro h
  · cases h <;> simp
  · cases h <;> rw [h.1, h.2]
    constructor
#align sym2.rel_iff Sym2.rel_iff
-/

end Sym2

#print Sym2 /-
/-- `sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`sym2.equiv_multiset`).
-/
@[reducible]
def Sym2 (α : Type u) :=
  Quotient (Sym2.Rel.setoid α)
#align sym2 Sym2
-/

namespace Sym2

#print Sym2.ind /-
@[elab_as_elim]
protected theorem ind {f : Sym2 α → Prop} (h : ∀ x y, f ⟦(x, y)⟧) : ∀ i, f i :=
  Quotient.ind <| Prod.rec <| h
#align sym2.ind Sym2.ind
-/

#print Sym2.inductionOn /-
@[elab_as_elim]
protected theorem inductionOn {f : Sym2 α → Prop} (i : Sym2 α) (hf : ∀ x y, f ⟦(x, y)⟧) : f i :=
  i.ind hf
#align sym2.induction_on Sym2.inductionOn
-/

/- warning: sym2.induction_on₂ -> Sym2.inductionOn₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : (Sym2.{u1} α) -> (Sym2.{u2} β) -> Prop} (i : Sym2.{u1} α) (j : Sym2.{u2} β), (forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), f (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (Prod.mk.{u1, u1} α α a₁ a₂)) (Quotient.mk'.{succ u2} (Prod.{u2, u2} β β) (Sym2.Rel.setoid.{u2} β) (Prod.mk.{u2, u2} β β b₁ b₂))) -> (f i j)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : (Sym2.{u2} α) -> (Sym2.{u1} β) -> Prop} (i : Sym2.{u2} α) (j : Sym2.{u1} β), (forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), f (Quotient.mk.{succ u2} (Prod.{u2, u2} α α) (Sym2.Rel.setoid.{u2} α) (Prod.mk.{u2, u2} α α a₁ a₂)) (Quotient.mk.{succ u1} (Prod.{u1, u1} β β) (Sym2.Rel.setoid.{u1} β) (Prod.mk.{u1, u1} β β b₁ b₂))) -> (f i j)
Case conversion may be inaccurate. Consider using '#align sym2.induction_on₂ Sym2.inductionOn₂ₓ'. -/
@[elab_as_elim]
protected theorem inductionOn₂ {f : Sym2 α → Sym2 β → Prop} (i : Sym2 α) (j : Sym2 β)
    (hf : ∀ a₁ a₂ b₁ b₂, f ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧) : f i j :=
  Quotient.induction_on₂ i j <| by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _
#align sym2.induction_on₂ Sym2.inductionOn₂

#print Sym2.exists /-
protected theorem exists {α : Sort _} {f : Sym2 α → Prop} :
    (∃ x : Sym2 α, f x) ↔ ∃ x y, f ⟦(x, y)⟧ :=
  (surjective_quotient_mk _).exists.trans Prod.exists
#align sym2.exists Sym2.exists
-/

#print Sym2.forall /-
protected theorem forall {α : Sort _} {f : Sym2 α → Prop} :
    (∀ x : Sym2 α, f x) ↔ ∀ x y, f ⟦(x, y)⟧ :=
  (surjective_quotient_mk _).forall.trans Prod.forall
#align sym2.forall Sym2.forall
-/

#print Sym2.eq_swap /-
theorem eq_swap {a b : α} : ⟦(a, b)⟧ = ⟦(b, a)⟧ :=
  by
  rw [Quotient.eq']
  apply rel.swap
#align sym2.eq_swap Sym2.eq_swap
-/

#print Sym2.mk''_prod_swap_eq /-
@[simp]
theorem mk''_prod_swap_eq {p : α × α} : ⟦p.symm⟧ = ⟦p⟧ :=
  by
  cases p
  exact eq_swap
#align sym2.mk_prod_swap_eq Sym2.mk''_prod_swap_eq
-/

#print Sym2.congr_right /-
theorem congr_right {a b c : α} : ⟦(a, b)⟧ = ⟦(a, c)⟧ ↔ b = c :=
  by
  constructor <;> intro h
  · rw [Quotient.eq'] at h
    cases h <;> rfl
  rw [h]
#align sym2.congr_right Sym2.congr_right
-/

#print Sym2.congr_left /-
theorem congr_left {a b c : α} : ⟦(b, a)⟧ = ⟦(c, a)⟧ ↔ b = c :=
  by
  constructor <;> intro h
  · rw [Quotient.eq'] at h
    cases h <;> rfl
  rw [h]
#align sym2.congr_left Sym2.congr_left
-/

#print Sym2.eq_iff /-
theorem eq_iff {x y z w : α} : ⟦(x, y)⟧ = ⟦(z, w)⟧ ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by simp
#align sym2.eq_iff Sym2.eq_iff
-/

#print Sym2.mk''_eq_mk''_iff /-
theorem mk''_eq_mk''_iff {p q : α × α} : ⟦p⟧ = ⟦q⟧ ↔ p = q ∨ p = q.symm :=
  by
  cases p
  cases q
  simp only [eq_iff, Prod.mk.inj_iff, Prod.swap_prod_mk]
#align sym2.mk_eq_mk_iff Sym2.mk''_eq_mk''_iff
-/

#print Sym2.lift /-
/-- The universal property of `sym2`; symmetric functions of two arguments are equivalent to
functions from `sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`sym2.from_rel` instead. -/
def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β)
    where
  toFun f :=
    Quotient.lift (uncurry ↑f) <| by
      rintro _ _ ⟨⟩
      exacts[rfl, f.prop _ _]
  invFun F := ⟨curry (F ∘ Quotient.mk'), fun a₁ a₂ => congr_arg F eq_swap⟩
  left_inv f := Subtype.ext rfl
  right_inv F := funext <| Sym2.ind fun x y => rfl
#align sym2.lift Sym2.lift
-/

/- warning: sym2.lift_mk -> Sym2.lift_mk'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (a₁ : α) (a₂ : α), Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (Equiv.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u1} α) -> β)) (fun (_x : Equiv.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u1} α) -> β)) => (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) -> (Sym2.{u1} α) -> β) (Equiv.hasCoeToFun.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u1} α) -> β)) (Sym2.lift.{u1, u2} α β) f (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (Prod.mk.{u1, u1} α α a₁ a₂))) ((fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (coeSubtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁)))))) f a₁ a₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) (a₁ : α) (a₂ : α), Eq.{succ u1} β (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max 1 (succ u2) (succ u1), max (succ u2) (succ u1)} (Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u2} α) -> β)) (Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) (fun (_x : Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) => (Sym2.{u2} α) -> β) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u2} α) -> β)) (Sym2.lift.{u2, u1} α β) f (Quotient.mk.{succ u2} (Prod.{u2, u2} α α) (Sym2.Rel.setoid.{u2} α) (Prod.mk.{u2, u2} α α a₁ a₂))) (Subtype.val.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁)) f a₁ a₂)
Case conversion may be inaccurate. Consider using '#align sym2.lift_mk Sym2.lift_mk''ₓ'. -/
@[simp]
theorem lift_mk'' (f : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a₁ a₂ : α) :
    lift f ⟦(a₁, a₂)⟧ = (f : α → α → β) a₁ a₂ :=
  rfl
#align sym2.lift_mk Sym2.lift_mk''

/- warning: sym2.coe_lift_symm_apply -> Sym2.coe_lift_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (F : (Sym2.{u1} α) -> β) (a₁ : α) (a₂ : α), Eq.{succ u2} β ((fun (a : Sort.{max 1 (succ u1) (succ u2)}) (b : Sort.{max (succ u1) (succ u2)}) [self : HasLiftT.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} a b] => self.0) (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (HasLiftT.mk.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (coeBase.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) (α -> α -> β) (coeSubtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁)))))) (coeFn.{max 1 (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} ((Sym2.{u1} α) -> β) (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁)))) (fun (_x : Equiv.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} ((Sym2.{u1} α) -> β) (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁)))) => ((Sym2.{u1} α) -> β) -> (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁)))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} ((Sym2.{u1} α) -> β) (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁)))) (Equiv.symm.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u2} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u1} α) -> β) (Sym2.lift.{u1, u2} α β)) F) a₁ a₂) (F (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (Prod.mk.{u1, u1} α α a₁ a₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (F : (Sym2.{u2} α) -> β) (a₁ : α) (a₂ : α), Eq.{succ u1} β (Subtype.val.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} ((Sym2.{u2} α) -> β) (Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁)))) ((Sym2.{u2} α) -> β) (fun (_x : (Sym2.{u2} α) -> β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : (Sym2.{u2} α) -> β) => Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} ((Sym2.{u2} α) -> β) (Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁)))) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Subtype.{max (succ u2) (succ u1)} (α -> α -> β) (fun (f : α -> α -> β) => forall (a₁ : α) (a₂ : α), Eq.{succ u1} β (f a₁ a₂) (f a₂ a₁))) ((Sym2.{u2} α) -> β) (Sym2.lift.{u2, u1} α β)) F) a₁ a₂) (F (Quotient.mk.{succ u2} (Prod.{u2, u2} α α) (Sym2.Rel.setoid.{u2} α) (Prod.mk.{u2, u2} α α a₁ a₂)))
Case conversion may be inaccurate. Consider using '#align sym2.coe_lift_symm_apply Sym2.coe_lift_symm_applyₓ'. -/
@[simp]
theorem coe_lift_symm_apply (F : Sym2 α → β) (a₁ a₂ : α) :
    (lift.symm F : α → α → β) a₁ a₂ = F ⟦(a₁, a₂)⟧ :=
  rfl
#align sym2.coe_lift_symm_apply Sym2.coe_lift_symm_apply

#print Sym2.lift₂ /-
/-- A two-argument version of `sym2.lift`. -/
def lift₂ :
    { f : α → α → β → β → γ //
        ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ } ≃
      (Sym2 α → Sym2 β → γ)
    where
  toFun f :=
    Quotient.lift₂ (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts[rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧, fun a₁ a₂ b₁ b₂ =>
      by
      constructor
      exacts[congr_arg₂ F eq_swap rfl, congr_arg₂ F rfl eq_swap]⟩
  left_inv f := Subtype.ext rfl
  right_inv F := funext₂ fun a b => Sym2.inductionOn₂ a b fun _ _ _ _ => rfl
#align sym2.lift₂ Sym2.lift₂
-/

/- warning: sym2.lift₂_mk -> Sym2.lift₂_mk'' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), Eq.{succ u3} γ (coeFn.{max 1 (succ u1) (succ u2) (succ u3), max 1 (succ u1) (succ u2) (succ u3)} (Equiv.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ)) (fun (_x : Equiv.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ)) => (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) -> (Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) (Equiv.hasCoeToFun.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ)) (Sym2.lift₂.{u1, u2, u3} α β γ) f (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (Prod.mk.{u1, u1} α α a₁ a₂)) (Quotient.mk'.{succ u2} (Prod.{u2, u2} β β) (Sym2.Rel.setoid.{u2} β) (Prod.mk.{u2, u2} β β b₁ b₂))) ((fun (a : Sort.{max 1 (succ u1) (succ u2) (succ u3)}) (b : Sort.{max (succ u1) (succ u2) (succ u3)}) [self : HasLiftT.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} a b] => self.0) (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (HasLiftT.mk.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (coeBase.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (coeSubtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))))) f a₁ a₂ b₁ b₂)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), Eq.{succ u1} γ (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max 1 (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u2)) (succ u1)} (Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u3} α) -> (Sym2.{u2} β) -> γ)) (Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (fun (_x : Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) => (Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u3} α) -> (Sym2.{u2} β) -> γ)) (Sym2.lift₂.{u3, u2, u1} α β γ) f (Quotient.mk.{succ u3} (Prod.{u3, u3} α α) (Sym2.Rel.setoid.{u3} α) (Prod.mk.{u3, u3} α α a₁ a₂)) (Quotient.mk.{succ u2} (Prod.{u2, u2} β β) (Sym2.Rel.setoid.{u2} β) (Prod.mk.{u2, u2} β β b₁ b₂))) (Subtype.val.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))) f a₁ a₂ b₁ b₂)
Case conversion may be inaccurate. Consider using '#align sym2.lift₂_mk Sym2.lift₂_mk''ₓ'. -/
@[simp]
theorem lift₂_mk''
    (f :
      { f : α → α → β → β → γ //
        ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ })
    (a₁ a₂ : α) (b₁ b₂ : β) : lift₂ f ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧ = (f : α → α → β → β → γ) a₁ a₂ b₁ b₂ :=
  rfl
#align sym2.lift₂_mk Sym2.lift₂_mk''

/- warning: sym2.coe_lift₂_symm_apply -> Sym2.coe_lift₂_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (F : (Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), Eq.{succ u3} γ ((fun (a : Sort.{max 1 (succ u1) (succ u2) (succ u3)}) (b : Sort.{max (succ u1) (succ u2) (succ u3)}) [self : HasLiftT.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} a b] => self.0) (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (HasLiftT.mk.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (CoeTCₓ.coe.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (coeBase.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) (α -> α -> β -> β -> γ) (coeSubtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))))) (coeFn.{max 1 (succ u1) (succ u2) (succ u3), max 1 (succ u1) (succ u2) (succ u3)} (Equiv.{max (succ u1) (succ u2) (succ u3), max 1 (succ u1) (succ u2) (succ u3)} ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))) (fun (_x : Equiv.{max (succ u1) (succ u2) (succ u3), max 1 (succ u1) (succ u2) (succ u3)} ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))) => ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) -> (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), max 1 (succ u1) (succ u2) (succ u3)} ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))) (Equiv.symm.{max 1 (succ u1) (succ u2) (succ u3), max (succ u1) (succ u2) (succ u3)} (Subtype.{max (succ u1) (succ u2) (succ u3)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u3} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u1} α) -> (Sym2.{u2} β) -> γ) (Sym2.lift₂.{u1, u2, u3} α β γ)) F) a₁ a₂ b₁ b₂) (F (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (Prod.mk.{u1, u1} α α a₁ a₂)) (Quotient.mk'.{succ u2} (Prod.{u2, u2} β β) (Sym2.Rel.setoid.{u2} β) (Prod.mk.{u2, u2} β β b₁ b₂)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (F : (Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), Eq.{succ u1} γ (Subtype.val.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Equiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} ((Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) (Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))) ((Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) (fun (_x : (Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : (Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) => Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) _x) (Equiv.instFunLikeEquiv.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} ((Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) (Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁))))) (Equiv.symm.{max (max (succ u1) (succ u2)) (succ u3), max (max (succ u1) (succ u2)) (succ u3)} (Subtype.{max (max (succ u3) (succ u2)) (succ u1)} (α -> α -> β -> β -> γ) (fun (f : α -> α -> β -> β -> γ) => forall (a₁ : α) (a₂ : α) (b₁ : β) (b₂ : β), And (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₂ a₁ b₁ b₂)) (Eq.{succ u1} γ (f a₁ a₂ b₁ b₂) (f a₁ a₂ b₂ b₁)))) ((Sym2.{u3} α) -> (Sym2.{u2} β) -> γ) (Sym2.lift₂.{u3, u2, u1} α β γ)) F) a₁ a₂ b₁ b₂) (F (Quotient.mk.{succ u3} (Prod.{u3, u3} α α) (Sym2.Rel.setoid.{u3} α) (Prod.mk.{u3, u3} α α a₁ a₂)) (Quotient.mk.{succ u2} (Prod.{u2, u2} β β) (Sym2.Rel.setoid.{u2} β) (Prod.mk.{u2, u2} β β b₁ b₂)))
Case conversion may be inaccurate. Consider using '#align sym2.coe_lift₂_symm_apply Sym2.coe_lift₂_symm_applyₓ'. -/
@[simp]
theorem coe_lift₂_symm_apply (F : Sym2 α → Sym2 β → γ) (a₁ a₂ : α) (b₁ b₂ : β) :
    (lift₂.symm F : α → α → β → β → γ) a₁ a₂ b₁ b₂ = F ⟦(a₁, a₂)⟧ ⟦(b₁, b₂)⟧ :=
  rfl
#align sym2.coe_lift₂_symm_apply Sym2.coe_lift₂_symm_apply

#print Sym2.map /-
/-- The functor `sym2` is functorial, and this function constructs the induced maps.
-/
def map (f : α → β) : Sym2 α → Sym2 β :=
  Quotient.map (Prod.map f f)
    (by
      rintro _ _ h
      cases h
      · rfl
      apply rel.swap)
#align sym2.map Sym2.map
-/

#print Sym2.map_id /-
@[simp]
theorem map_id : map (@id α) = id := by
  ext ⟨⟨x, y⟩⟩
  rfl
#align sym2.map_id Sym2.map_id
-/

/- warning: sym2.map_comp -> Sym2.map_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {g : β -> γ} {f : α -> β}, Eq.{max (succ u1) (succ u3)} ((Sym2.{u1} α) -> (Sym2.{u3} γ)) (Sym2.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Function.comp.{succ u1, succ u2, succ u3} (Sym2.{u1} α) (Sym2.{u2} β) (Sym2.{u3} γ) (Sym2.map.{u2, u3} β γ g) (Sym2.map.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {g : β -> γ} {f : α -> β}, Eq.{max (succ u3) (succ u2)} ((Sym2.{u3} α) -> (Sym2.{u2} γ)) (Sym2.map.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) (Function.comp.{succ u3, succ u1, succ u2} (Sym2.{u3} α) (Sym2.{u1} β) (Sym2.{u2} γ) (Sym2.map.{u1, u2} β γ g) (Sym2.map.{u3, u1} α β f))
Case conversion may be inaccurate. Consider using '#align sym2.map_comp Sym2.map_compₓ'. -/
theorem map_comp {g : β → γ} {f : α → β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f :=
  by
  ext ⟨⟨x, y⟩⟩
  rfl
#align sym2.map_comp Sym2.map_comp

/- warning: sym2.map_map -> Sym2.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {g : β -> γ} {f : α -> β} (x : Sym2.{u1} α), Eq.{succ u3} (Sym2.{u3} γ) (Sym2.map.{u2, u3} β γ g (Sym2.map.{u1, u2} α β f x)) (Sym2.map.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {g : β -> γ} {f : α -> β} (x : Sym2.{u3} α), Eq.{succ u2} (Sym2.{u2} γ) (Sym2.map.{u1, u2} β γ g (Sym2.map.{u3, u1} α β f x)) (Sym2.map.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f) x)
Case conversion may be inaccurate. Consider using '#align sym2.map_map Sym2.map_mapₓ'. -/
theorem map_map {g : β → γ} {f : α → β} (x : Sym2 α) : map g (map f x) = map (g ∘ f) x := by tidy
#align sym2.map_map Sym2.map_map

#print Sym2.map_pair_eq /-
@[simp]
theorem map_pair_eq (f : α → β) (x y : α) : map f ⟦(x, y)⟧ = ⟦(f x, f y)⟧ :=
  rfl
#align sym2.map_pair_eq Sym2.map_pair_eq
-/

/- warning: sym2.map.injective -> Sym2.map.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Function.Injective.{succ u1, succ u2} (Sym2.{u1} α) (Sym2.{u2} β) (Sym2.map.{u1, u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Function.Injective.{succ u2, succ u1} (Sym2.{u2} α) (Sym2.{u1} β) (Sym2.map.{u2, u1} α β f))
Case conversion may be inaccurate. Consider using '#align sym2.map.injective Sym2.map.injectiveₓ'. -/
theorem map.injective {f : α → β} (hinj : Injective f) : Injective (map f) :=
  by
  intro z z'
  refine' Quotient.ind₂ (fun z z' => _) z z'
  cases' z with x y
  cases' z' with x' y'
  repeat' rw [map_pair_eq, eq_iff]
  rintro (h | h) <;> simp [hinj h.1, hinj h.2]
#align sym2.map.injective Sym2.map.injective

section Membership

/-! ### Membership and set coercion -/


#print Sym2.Mem /-
/-- This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
protected def Mem (x : α) (z : Sym2 α) : Prop :=
  ∃ y : α, z = ⟦(x, y)⟧
#align sym2.mem Sym2.Mem
-/

#print Sym2.mem_iff' /-
theorem mem_iff' {a b c : α} : Sym2.Mem a ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
  { mp := by
      rintro ⟨_, h⟩
      rw [eq_iff] at h
      tidy
    mpr := by
      rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      rw [eq_swap]
      exact ⟨_, rfl⟩ }
#align sym2.mem_iff' Sym2.mem_iff'
-/

instance : SetLike (Sym2 α) α where
  coe z := { x | z.Mem x }
  coe_injective' z z' h := by
    simp only [Set.ext_iff, Set.mem_setOf_eq] at h
    induction' z using Sym2.ind with x y
    induction' z' using Sym2.ind with x' y'
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    simp only [mem_iff', eq_self_iff_true, or_true_iff, iff_true_iff, true_or_iff, true_iff_iff] at
      hx hy hx' hy'
    cases hx <;> cases hy <;> cases hx' <;> cases hy' <;> subst_vars
    rw [Sym2.eq_swap]

#print Sym2.mem_iff_mem /-
@[simp]
theorem mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x ∈ z :=
  Iff.rfl
#align sym2.mem_iff_mem Sym2.mem_iff_mem
-/

#print Sym2.mem_iff_exists /-
theorem mem_iff_exists {x : α} {z : Sym2 α} : x ∈ z ↔ ∃ y : α, z = ⟦(x, y)⟧ :=
  Iff.rfl
#align sym2.mem_iff_exists Sym2.mem_iff_exists
-/

#print Sym2.ext /-
@[ext]
theorem ext {p q : Sym2 α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
#align sym2.ext Sym2.ext
-/

#print Sym2.mem_mk''_left /-
theorem mem_mk''_left (x y : α) : x ∈ ⟦(x, y)⟧ :=
  ⟨y, rfl⟩
#align sym2.mem_mk_left Sym2.mem_mk''_left
-/

#print Sym2.mem_mk''_right /-
theorem mem_mk''_right (x y : α) : y ∈ ⟦(x, y)⟧ :=
  eq_swap.subst <| mem_mk''_left y x
#align sym2.mem_mk_right Sym2.mem_mk''_right
-/

#print Sym2.mem_iff /-
@[simp]
theorem mem_iff {a b c : α} : a ∈ ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
  mem_iff'
#align sym2.mem_iff Sym2.mem_iff
-/

#print Sym2.out_fst_mem /-
theorem out_fst_mem (e : Sym2 α) : e.out.1 ∈ e :=
  ⟨e.out.2, by rw [Prod.mk.eta, e.out_eq]⟩
#align sym2.out_fst_mem Sym2.out_fst_mem
-/

#print Sym2.out_snd_mem /-
theorem out_snd_mem (e : Sym2 α) : e.out.2 ∈ e :=
  ⟨e.out.1, by rw [eq_swap, Prod.mk.eta, e.out_eq]⟩
#align sym2.out_snd_mem Sym2.out_snd_mem
-/

#print Sym2.ball /-
theorem ball {p : α → Prop} {a b : α} : (∀ c ∈ ⟦(a, b)⟧, p c) ↔ p a ∧ p b :=
  by
  refine' ⟨fun h => ⟨h _ <| mem_mk_left _ _, h _ <| mem_mk_right _ _⟩, fun h c hc => _⟩
  obtain rfl | rfl := Sym2.mem_iff.1 hc
  · exact h.1
  · exact h.2
#align sym2.ball Sym2.ball
-/

#print Sym2.Mem.other /-
/-- Given an element of the unordered pair, give the other element using `classical.some`.
See also `mem.other'` for the computable version.
-/
noncomputable def Mem.other {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Classical.choose h
#align sym2.mem.other Sym2.Mem.other
-/

#print Sym2.other_spec /-
@[simp]
theorem other_spec {a : α} {z : Sym2 α} (h : a ∈ z) : ⟦(a, h.other)⟧ = z := by
  erw [← Classical.choose_spec h]
#align sym2.other_spec Sym2.other_spec
-/

#print Sym2.other_mem /-
theorem other_mem {a : α} {z : Sym2 α} (h : a ∈ z) : h.other ∈ z :=
  by
  convert mem_mk_right a h.other
  rw [other_spec h]
#align sym2.other_mem Sym2.other_mem
-/

#print Sym2.mem_and_mem_iff /-
theorem mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x ≠ y) : x ∈ z ∧ y ∈ z ↔ z = ⟦(x, y)⟧ :=
  by
  constructor
  · induction' z using Sym2.ind with x' y'
    rw [mem_iff, mem_iff]
    rintro ⟨rfl | rfl, rfl | rfl⟩ <;> try trivial <;> simp only [Sym2.eq_swap]
  · rintro rfl
    simp
#align sym2.mem_and_mem_iff Sym2.mem_and_mem_iff
-/

#print Sym2.eq_of_ne_mem /-
theorem eq_of_ne_mem {x y : α} {z z' : Sym2 α} (h : x ≠ y) (h1 : x ∈ z) (h2 : y ∈ z) (h3 : x ∈ z')
    (h4 : y ∈ z') : z = z' :=
  ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm
#align sym2.eq_of_ne_mem Sym2.eq_of_ne_mem
-/

#print Sym2.Mem.decidable /-
instance Mem.decidable [DecidableEq α] (x : α) (z : Sym2 α) : Decidable (x ∈ z) :=
  Quotient.recOnSubsingleton z fun ⟨y₁, y₂⟩ => decidable_of_iff' _ mem_iff
#align sym2.mem.decidable Sym2.Mem.decidable
-/

end Membership

/- warning: sym2.mem_map -> Sym2.mem_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {z : Sym2.{u1} α}, Iff (Membership.Mem.{u2, u2} β (Sym2.{u2} β) (SetLike.hasMem.{u2, u2} (Sym2.{u2} β) β (Sym2.setLike.{u2} β)) b (Sym2.map.{u1, u2} α β f z)) (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Sym2.{u1} α) (SetLike.hasMem.{u1, u1} (Sym2.{u1} α) α (Sym2.setLike.{u1} α)) a z) (Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {b : β} {z : Sym2.{u2} α}, Iff (Membership.mem.{u1, u1} β (Sym2.{u1} β) (SetLike.instMembership.{u1, u1} (Sym2.{u1} β) β (Sym2.instSetLikeSym2.{u1} β)) b (Sym2.map.{u2, u1} α β f z)) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Sym2.{u2} α) (SetLike.instMembership.{u2, u2} (Sym2.{u2} α) α (Sym2.instSetLikeSym2.{u2} α)) a z) (Eq.{succ u1} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align sym2.mem_map Sym2.mem_mapₓ'. -/
@[simp]
theorem mem_map {f : α → β} {b : β} {z : Sym2 α} : b ∈ Sym2.map f z ↔ ∃ a, a ∈ z ∧ f a = b :=
  by
  induction' z using Sym2.ind with x y
  simp only [map, Quotient.map_mk, Prod.map_mk, mem_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨x, by simp⟩
    · exact ⟨y, by simp⟩
  · rintro ⟨w, rfl | rfl, rfl⟩ <;> simp
#align sym2.mem_map Sym2.mem_map

/- warning: sym2.map_congr -> Sym2.map_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {s : Sym2.{u1} α}, (forall (x : α), (Membership.Mem.{u1, u1} α (Sym2.{u1} α) (SetLike.hasMem.{u1, u1} (Sym2.{u1} α) α (Sym2.setLike.{u1} α)) x s) -> (Eq.{succ u2} β (f x) (g x))) -> (Eq.{succ u2} (Sym2.{u2} β) (Sym2.map.{u1, u2} α β f s) (Sym2.map.{u1, u2} α β g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {s : Sym2.{u2} α}, (forall (x : α), (Membership.mem.{u2, u2} α (Sym2.{u2} α) (SetLike.instMembership.{u2, u2} (Sym2.{u2} α) α (Sym2.instSetLikeSym2.{u2} α)) x s) -> (Eq.{succ u1} β (f x) (g x))) -> (Eq.{succ u1} (Sym2.{u1} β) (Sym2.map.{u2, u1} α β f s) (Sym2.map.{u2, u1} α β g s))
Case conversion may be inaccurate. Consider using '#align sym2.map_congr Sym2.map_congrₓ'. -/
@[congr]
theorem map_congr {f g : α → β} {s : Sym2 α} (h : ∀ x ∈ s, f x = g x) : map f s = map g s :=
  by
  ext y
  simp only [mem_map]
  constructor <;>
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [hw, h]⟩
#align sym2.map_congr Sym2.map_congr

#print Sym2.map_id' /-
/-- Note: `sym2.map_id` will not simplify `sym2.map id z` due to `sym2.map_congr`. -/
@[simp]
theorem map_id' : (map fun x : α => x) = id :=
  map_id
#align sym2.map_id' Sym2.map_id'
-/

/-! ### Diagonal -/


#print Sym2.diag /-
/-- A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `sym2 α`.
-/
def diag (x : α) : Sym2 α :=
  ⟦(x, x)⟧
#align sym2.diag Sym2.diag
-/

#print Sym2.diag_injective /-
theorem diag_injective : Function.Injective (Sym2.diag : α → Sym2 α) := fun x y h => by
  cases Quotient.exact h <;> rfl
#align sym2.diag_injective Sym2.diag_injective
-/

#print Sym2.IsDiag /-
/-- A predicate for testing whether an element of `sym2 α` is on the diagonal.
-/
def IsDiag : Sym2 α → Prop :=
  lift ⟨Eq, fun _ _ => propext eq_comm⟩
#align sym2.is_diag Sym2.IsDiag
-/

#print Sym2.mk''_isDiag_iff /-
theorem mk''_isDiag_iff {x y : α} : IsDiag ⟦(x, y)⟧ ↔ x = y :=
  Iff.rfl
#align sym2.mk_is_diag_iff Sym2.mk''_isDiag_iff
-/

#print Sym2.isDiag_iff_proj_eq /-
@[simp]
theorem isDiag_iff_proj_eq (z : α × α) : IsDiag ⟦z⟧ ↔ z.1 = z.2 :=
  Prod.recOn z fun _ _ => mk''_isDiag_iff
#align sym2.is_diag_iff_proj_eq Sym2.isDiag_iff_proj_eq
-/

#print Sym2.diag_isDiag /-
@[simp]
theorem diag_isDiag (a : α) : IsDiag (diag a) :=
  Eq.refl a
#align sym2.diag_is_diag Sym2.diag_isDiag
-/

#print Sym2.IsDiag.mem_range_diag /-
theorem IsDiag.mem_range_diag {z : Sym2 α} : IsDiag z → z ∈ Set.range (@diag α) :=
  by
  induction' z using Sym2.ind with x y
  rintro (rfl : x = y)
  exact ⟨_, rfl⟩
#align sym2.is_diag.mem_range_diag Sym2.IsDiag.mem_range_diag
-/

#print Sym2.isDiag_iff_mem_range_diag /-
theorem isDiag_iff_mem_range_diag (z : Sym2 α) : IsDiag z ↔ z ∈ Set.range (@diag α) :=
  ⟨IsDiag.mem_range_diag, fun ⟨i, hi⟩ => hi ▸ diag_isDiag i⟩
#align sym2.is_diag_iff_mem_range_diag Sym2.isDiag_iff_mem_range_diag
-/

#print Sym2.IsDiag.decidablePred /-
instance IsDiag.decidablePred (α : Type u) [DecidableEq α] : DecidablePred (@IsDiag α) :=
  by
  refine' fun z => Quotient.recOnSubsingleton z fun a => _
  erw [is_diag_iff_proj_eq]
  infer_instance
#align sym2.is_diag.decidable_pred Sym2.IsDiag.decidablePred
-/

#print Sym2.other_ne /-
theorem other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a ∈ z) : h.other ≠ a :=
  by
  contrapose! hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp
#align sym2.other_ne Sym2.other_ne
-/

section Relations

/-! ### Declarations about symmetric relations -/


variable {r : α → α → Prop}

#print Sym2.fromRel /-
/-- Symmetric relations define a set on `sym2 α` by taking all those pairs
of elements that are related.
-/
def fromRel (sym : Symmetric r) : Set (Sym2 α) :=
  setOf (lift ⟨r, fun x y => propext ⟨fun h => Sym h, fun h => Sym h⟩⟩)
#align sym2.from_rel Sym2.fromRel
-/

#print Sym2.fromRel_proj_prop /-
@[simp]
theorem fromRel_proj_prop {sym : Symmetric r} {z : α × α} : ⟦z⟧ ∈ fromRel Sym ↔ r z.1 z.2 :=
  Iff.rfl
#align sym2.from_rel_proj_prop Sym2.fromRel_proj_prop
-/

#print Sym2.fromRel_prop /-
@[simp]
theorem fromRel_prop {sym : Symmetric r} {a b : α} : ⟦(a, b)⟧ ∈ fromRel Sym ↔ r a b :=
  Iff.rfl
#align sym2.from_rel_prop Sym2.fromRel_prop
-/

/- warning: sym2.from_rel_bot -> Sym2.fromRel_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Sym2.{u1} α)) (Sym2.fromRel.{u1} α (fun (x : α) (y : α) => Bot.bot.{u1} (α -> α -> Prop) (Pi.hasBot.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasBot.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasBot.{0} Prop Prop.completeLattice))) x y) (fun (x : α) (y : α) (z : Bot.bot.{u1} (α -> α -> Prop) (Pi.hasBot.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasBot.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasBot.{0} Prop Prop.completeLattice))) x y) => z)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Sym2.{u1} α)) (Set.hasEmptyc.{u1} (Sym2.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Sym2.{u1} α)) (Sym2.fromRel.{u1} α (fun (x : α) (y : α) => Bot.bot.{u1} (α -> α -> Prop) (Pi.instBotForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instBotForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toBot.{0} Prop Prop.completeLattice))) x y) (fun (x : α) (y : α) (z : Bot.bot.{u1} (α -> α -> Prop) (Pi.instBotForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instBotForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toBot.{0} Prop Prop.completeLattice))) x y) => z)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Sym2.{u1} α)) (Set.instEmptyCollectionSet.{u1} (Sym2.{u1} α)))
Case conversion may be inaccurate. Consider using '#align sym2.from_rel_bot Sym2.fromRel_botₓ'. -/
theorem fromRel_bot : fromRel (fun (x y : α) z => z : Symmetric ⊥) = ∅ :=
  by
  apply Set.eq_empty_of_forall_not_mem fun e => _
  refine' e.ind _
  simp [-Set.bot_eq_empty, Prop.bot_eq_false]
#align sym2.from_rel_bot Sym2.fromRel_bot

/- warning: sym2.from_rel_top -> Sym2.fromRel_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Sym2.{u1} α)) (Sym2.fromRel.{u1} α (fun (x : α) (y : α) => Top.top.{u1} (α -> α -> Prop) (Pi.hasTop.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasTop.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice))) x y) (fun (x : α) (y : α) (z : Top.top.{u1} (α -> α -> Prop) (Pi.hasTop.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.hasTop.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toHasTop.{0} Prop Prop.completeLattice))) x y) => z)) (Set.univ.{u1} (Sym2.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Sym2.{u1} α)) (Sym2.fromRel.{u1} α (fun (x : α) (y : α) => Top.top.{u1} (α -> α -> Prop) (Pi.instTopForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instTopForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toTop.{0} Prop Prop.completeLattice))) x y) (fun (x : α) (y : α) (z : Top.top.{u1} (α -> α -> Prop) (Pi.instTopForAll.{u1, u1} α (fun (ᾰ : α) => α -> Prop) (fun (i : α) => Pi.instTopForAll.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => CompleteLattice.toTop.{0} Prop Prop.completeLattice))) x y) => z)) (Set.univ.{u1} (Sym2.{u1} α))
Case conversion may be inaccurate. Consider using '#align sym2.from_rel_top Sym2.fromRel_topₓ'. -/
theorem fromRel_top : fromRel (fun (x y : α) z => z : Symmetric ⊤) = Set.univ :=
  by
  apply Set.eq_univ_of_forall fun e => _
  refine' e.ind _
  simp [-Set.top_eq_univ, Prop.top_eq_true]
#align sym2.from_rel_top Sym2.fromRel_top

#print Sym2.fromRel_irreflexive /-
theorem fromRel_irreflexive {sym : Symmetric r} :
    Irreflexive r ↔ ∀ {z}, z ∈ fromRel Sym → ¬IsDiag z :=
  { mp := fun h =>
      Sym2.ind <| by
        rintro a b hr (rfl : a = b)
        exact h _ hr
    mpr := fun h x hr => h (fromRel_prop.mpr hr) rfl }
#align sym2.from_rel_irreflexive Sym2.fromRel_irreflexive
-/

#print Sym2.mem_fromRel_irrefl_other_ne /-
theorem mem_fromRel_irrefl_other_ne {sym : Symmetric r} (irrefl : Irreflexive r) {a : α}
    {z : Sym2 α} (hz : z ∈ fromRel Sym) (h : a ∈ z) : h.other ≠ a :=
  other_ne (fromRel_irreflexive.mp irrefl hz) h
#align sym2.mem_from_rel_irrefl_other_ne Sym2.mem_fromRel_irrefl_other_ne
-/

#print Sym2.fromRel.decidablePred /-
instance fromRel.decidablePred (sym : Symmetric r) [h : DecidableRel r] :
    DecidablePred (· ∈ Sym2.fromRel Sym) := fun z => Quotient.recOnSubsingleton z fun x => h _ _
#align sym2.from_rel.decidable_pred Sym2.fromRel.decidablePred
-/

#print Sym2.ToRel /-
/-- The inverse to `sym2.from_rel`. Given a set on `sym2 α`, give a symmetric relation on `α`
(see `sym2.to_rel_symmetric`). -/
def ToRel (s : Set (Sym2 α)) (x y : α) : Prop :=
  ⟦(x, y)⟧ ∈ s
#align sym2.to_rel Sym2.ToRel
-/

#print Sym2.toRel_prop /-
@[simp]
theorem toRel_prop (s : Set (Sym2 α)) (x y : α) : ToRel s x y ↔ ⟦(x, y)⟧ ∈ s :=
  Iff.rfl
#align sym2.to_rel_prop Sym2.toRel_prop
-/

#print Sym2.toRel_symmetric /-
theorem toRel_symmetric (s : Set (Sym2 α)) : Symmetric (ToRel s) := fun x y => by simp [eq_swap]
#align sym2.to_rel_symmetric Sym2.toRel_symmetric
-/

#print Sym2.toRel_fromRel /-
theorem toRel_fromRel (sym : Symmetric r) : ToRel (fromRel Sym) = r :=
  rfl
#align sym2.to_rel_from_rel Sym2.toRel_fromRel
-/

#print Sym2.fromRel_toRel /-
theorem fromRel_toRel (s : Set (Sym2 α)) : fromRel (toRel_symmetric s) = s :=
  Set.ext fun z => Sym2.ind (fun x y => Iff.rfl) z
#align sym2.from_rel_to_rel Sym2.fromRel_toRel
-/

end Relations

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] Vector.Perm.isSetoid

private def from_vector : Vector α 2 → α × α
  | ⟨[a, b], h⟩ => (a, b)
#align sym2.from_vector sym2.from_vector

private theorem perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp := by
      simp [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.cons_eq_cons]
      tidy
    mpr := by
      intro h
      cases h <;> rw [h.1, h.2]
      apply List.Perm.swap'
      rfl }
#align sym2.perm_card_two_iff sym2.perm_card_two_iff

#print Sym2.sym2EquivSym' /-
/-- The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2)
    where
  toFun :=
    Quotient.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · rfl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quotient.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        cases' x with _ x; · simpa using hx
        cases' x with _ x; · simpa using hx
        cases' x with _ x; swap;
        · exfalso
          simp at hx
          linarith [hx]
        cases' y with _ y; · simpa using hy
        cases' y with _ y; · simpa using hy
        cases' y with _ y; swap;
        · exfalso
          simp at hy
          linarith [hy]
        rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); · rfl
        apply Sym2.Rel.swap)
  left_inv := by tidy
  right_inv x := by
    refine' Quotient.recOnSubsingleton x fun x => _
    · cases' x with x hx
      cases' x with _ x
      · simpa using hx
      cases' x with _ x
      · simpa using hx
      cases' x with _ x
      swap
      · exfalso
        simp at hx
        linarith [hx]
      rfl
#align sym2.sym2_equiv_sym' Sym2.sym2EquivSym'
-/

#print Sym2.equivSym /-
/-- The symmetric square is equivalent to the second symmetric power.
-/
def equivSym (α : Type _) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2EquivSym' symEquivSym'.symm
#align sym2.equiv_sym Sym2.equivSym
-/

/- warning: sym2.equiv_multiset -> Sym2.equivMultiset is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (Sym2.{u1} α) (Subtype.{succ u1} (Multiset.{u1} α) (fun (s : Multiset.{u1} α) => Eq.{1} Nat (coeFn.{succ u1, succ u1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (fun (_x : AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) => (Multiset.{u1} α) -> Nat) (AddMonoidHom.hasCoeToFun.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (Sym2.{u1} α) (Subtype.{succ u1} (Multiset.{u1} α) (fun (s : Multiset.{u1} α) => Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) (FunLike.coe.{succ u1, succ u1, 1} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) (fun (_x : Multiset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) _x) (AddHomClass.toFunLike.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddZeroClass.toAdd.{u1} (Multiset.{u1} α) (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (AddMonoidHomClass.toAddHomClass.{u1, u1, 0} (AddMonoidHom.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)) (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) (AddMonoidHom.addMonoidHomClass.{u1, 0} (Multiset.{u1} α) Nat (AddMonoid.toAddZeroClass.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α)))))) (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) (Multiset.card.{u1} α) s) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Multiset.{u1} α) => Nat) s) 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align sym2.equiv_multiset Sym2.equivMultisetₓ'. -/
/-- The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equiv_sym`, but it's provided
in case the definition for `sym` changes.)
-/
def equivMultiset (α : Type _) : Sym2 α ≃ { s : Multiset α // s.card = 2 } :=
  equivSym α
#align sym2.equiv_multiset Sym2.equivMultiset

end SymEquiv

section Decidable

#print Sym2.relBool /-
/-- An algorithm for computing `sym2.rel`.
-/
def relBool [DecidableEq α] (x y : α × α) : Bool :=
  if x.1 = y.1 then x.2 = y.2 else if x.1 = y.2 then x.2 = y.1 else false
#align sym2.rel_bool Sym2.relBool
-/

#print Sym2.relBool_spec /-
theorem relBool_spec [DecidableEq α] (x y : α × α) : ↥(relBool x y) ↔ Rel α x y :=
  by
  cases' x with x₁ x₂; cases' y with y₁ y₂
  dsimp [rel_bool]; split_ifs <;> simp only [false_iff_iff, Bool.coeSort_false, Bool.of_decide_iff]
  rotate_left 2;
  · contrapose! h
    cases h <;> cc
  all_goals
    subst x₁; constructor <;> intro h1
    · subst h1 <;> apply Sym2.Rel.swap
    · cases h1 <;> cc
#align sym2.rel_bool_spec Sym2.relBool_spec
-/

/-- Given `[decidable_eq α]` and `[fintype α]`, the following instance gives `fintype (sym2 α)`.
-/
instance (α : Type _) [DecidableEq α] : DecidableRel (Sym2.Rel α) := fun x y =>
  decidable_of_bool (relBool x y) (relBool_spec x y)

/-! ### The other element of an element of the symmetric square -/


/--
A function that gives the other element of a pair given one of the elements.  Used in `mem.other'`.
-/
private def pair_other [DecidableEq α] (a : α) (z : α × α) : α :=
  if a = z.1 then z.2 else z.1
#align sym2.pair_other sym2.pair_other

#print Sym2.Mem.other' /-
/-- Get the other element of the unordered pair using the decidable equality.
This is the computable version of `mem.other`.
-/
def Mem.other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Quot.rec (fun x h' => pairOther a x)
    (by
      clear h z
      intro x y h
      ext hy
      convert_to pair_other a x = _
      · have h' :
          ∀ {c e h},
            @Eq.ndrec _ ⟦x⟧ (fun s => a ∈ s → α) (fun _ => pair_other a x) c e h = pair_other a x :=
          by
          intro _ e _
          subst e
        apply h'
      have h' := (rel_bool_spec x y).mpr h
      cases' x with x₁ x₂; cases' y with y₁ y₂
      cases' mem_iff.mp hy with hy' <;> subst a <;> dsimp [rel_bool] at h' <;> split_ifs  at h' <;>
          try rw [Bool.of_decide_iff] at h'; subst x₁; subst x₂ <;>
        dsimp [pair_other]
      simp only [Ne.symm h_1, if_true, eq_self_iff_true, if_false]
      exfalso; exact Bool.not_false' h'
      simp only [h_1, if_true, eq_self_iff_true, if_false]
      exfalso; exact Bool.not_false' h')
    z h
#align sym2.mem.other' Sym2.Mem.other'
-/

#print Sym2.other_spec' /-
@[simp]
theorem other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : ⟦(a, h.other')⟧ = z :=
  by
  induction z; cases' z with x y
  have h' := mem_iff.mp h
  dsimp [mem.other', Quot.rec, pair_other]
  cases h' <;> subst a
  · simp only [eq_self_iff_true]
    rfl
  · split_ifs
    subst h_1
    rfl
    rw [eq_swap]
    rfl
  rfl
#align sym2.other_spec' Sym2.other_spec'
-/

#print Sym2.other_eq_other' /-
@[simp]
theorem other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : h.other = h.other' := by
  rw [← congr_right, other_spec' h, other_spec]
#align sym2.other_eq_other' Sym2.other_eq_other'
-/

#print Sym2.other_mem' /-
theorem other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : h.other' ∈ z :=
  by
  rw [← other_eq_other']
  exact other_mem h
#align sym2.other_mem' Sym2.other_mem'
-/

#print Sym2.other_invol' /-
theorem other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : ha.other' ∈ z) :
    hb.other' = a := by
  induction z; cases' z with x y
  dsimp [mem.other', Quot.rec, pair_other] at hb
  split_ifs  at hb <;> dsimp [mem.other', Quot.rec, pair_other]
  simp only [h, if_true, eq_self_iff_true]
  split_ifs; assumption; rfl
  simp only [h, if_false, eq_self_iff_true]
  exact ((mem_iff.mp ha).resolve_left h).symm
  rfl
#align sym2.other_invol' Sym2.other_invol'
-/

#print Sym2.other_invol /-
theorem other_invol {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : ha.other ∈ z) : hb.other = a := by
  classical
    rw [other_eq_other'] at hb⊢
    convert other_invol' ha hb
    rw [other_eq_other']
#align sym2.other_invol Sym2.other_invol
-/

/- warning: sym2.filter_image_quotient_mk_is_diag -> Sym2.filter_image_quotient_mk''_isDiag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α))) (Finset.filter.{u1} (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Sym2.IsDiag.{u1} α) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Sym2.IsDiag.decidablePred.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Quotient.decidableEq.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Sym2.Rel.decidableRel.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) a b) (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.product.{u1, u1} α α s s))) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Quotient.decidableEq.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Sym2.Rel.decidableRel.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) a b) (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Sym2.{u1} α)) (Finset.filter.{u1} (Sym2.{u1} α) (Sym2.IsDiag.{u1} α) (fun (a : Sym2.{u1} α) => Sym2.IsDiag.decidablePred.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Sym2.instDecidableEqSym2.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Quotient.mk''.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.product.{u1, u1} α α s s))) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Sym2.instDecidableEqSym2.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Quotient.mk''.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
Case conversion may be inaccurate. Consider using '#align sym2.filter_image_quotient_mk_is_diag Sym2.filter_image_quotient_mk''_isDiagₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem filter_image_quotient_mk''_isDiag [DecidableEq α] (s : Finset α) :
    ((s ×ˢ s).image Quotient.mk').filterₓ IsDiag = s.diag.image Quotient.mk' :=
  by
  ext z
  induction z using Quotient.inductionOn
  rcases z with ⟨x, y⟩
  simp only [mem_image, mem_diag, exists_prop, mem_filter, Prod.exists, mem_product]
  constructor
  · rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
    rw [← h, Sym2.mk''_isDiag_iff] at hab
    exact ⟨a, b, ⟨ha, hab⟩, h⟩
  · rintro ⟨a, b, ⟨ha, rfl⟩, h⟩
    rw [← h]
    exact ⟨⟨a, a, ⟨ha, ha⟩, rfl⟩, rfl⟩
#align sym2.filter_image_quotient_mk_is_diag Sym2.filter_image_quotient_mk''_isDiag

/- warning: sym2.filter_image_quotient_mk_not_is_diag -> Sym2.filter_image_quotient_mk''_not_isDiag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α))) (Finset.filter.{u1} (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Sym2.{u1} α) => Not (Sym2.IsDiag.{u1} α a)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Not.decidable (Sym2.IsDiag.{u1} α a) (Sym2.IsDiag.decidablePred.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Quotient.decidableEq.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Sym2.Rel.decidableRel.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) a b) (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.product.{u1, u1} α α s s))) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Quotient.decidableEq.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Sym2.Rel.decidableRel.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) a b) (Quotient.mk'.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Sym2.{u1} α)) (Finset.filter.{u1} (Sym2.{u1} α) (fun (a : Sym2.{u1} α) => Not (Sym2.IsDiag.{u1} α a)) (fun (a : Sym2.{u1} α) => instDecidableNot (Sym2.IsDiag.{u1} α a) (Sym2.IsDiag.decidablePred.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a)) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Sym2.instDecidableEqSym2.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Quotient.mk''.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.product.{u1, u1} α α s s))) (Finset.image.{u1, u1} (Prod.{u1, u1} α α) (Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (fun (a : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (b : Quotient.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) => Sym2.instDecidableEqSym2.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (Quotient.mk''.{succ u1} (Prod.{u1, u1} α α) (Sym2.Rel.setoid.{u1} α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
Case conversion may be inaccurate. Consider using '#align sym2.filter_image_quotient_mk_not_is_diag Sym2.filter_image_quotient_mk''_not_isDiagₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem filter_image_quotient_mk''_not_isDiag [DecidableEq α] (s : Finset α) :
    (((s ×ˢ s).image Quotient.mk').filterₓ fun a : Sym2 α => ¬a.IsDiag) =
      s.offDiag.image Quotient.mk' :=
  by
  ext z
  induction z using Quotient.inductionOn
  rcases z with ⟨x, y⟩
  simp only [mem_image, mem_off_diag, mem_filter, Prod.exists, mem_product]
  constructor
  · rintro ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
    rw [← h, Sym2.mk''_isDiag_iff] at hab
    exact ⟨a, b, ⟨ha, hb, hab⟩, h⟩
  · rintro ⟨a, b, ⟨ha, hb, hab⟩, h⟩
    rw [Ne.def, ← Sym2.mk''_isDiag_iff, h] at hab
    exact ⟨⟨a, b, ⟨ha, hb⟩, h⟩, hab⟩
#align sym2.filter_image_quotient_mk_not_is_diag Sym2.filter_image_quotient_mk''_not_isDiag

end Decidable

instance [Subsingleton α] : Subsingleton (Sym2 α) :=
  (equivSym α).Injective.Subsingleton

instance [Unique α] : Unique (Sym2 α) :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty (Sym2 α) :=
  (equivSym α).isEmpty

instance [Nontrivial α] : Nontrivial (Sym2 α) :=
  diag_injective.Nontrivial

end Sym2

