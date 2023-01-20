/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.finsupp.lex
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
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

/-- `finsupp.lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `lex (α →₀ N)` has an order given by `finsupp.lex (<) (<)`.
-/
protected def Lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
  Pi.Lex r (fun _ => s) x y
#align finsupp.lex Finsupp.Lex

theorem Pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
    Pi.Lex r (fun _ => s) (a : α → N) (b : α → N) = Finsupp.Lex r s a b :=
  rfl
#align pi.lex_eq_finsupp_lex Pi.lex_eq_finsupp_lex

theorem lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
    Finsupp.Lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) :=
  Iff.rfl
#align finsupp.lex_def Finsupp.lex_def

theorem lex_eq_inv_image_dfinsupp_lex (r : α → α → Prop) (s : N → N → Prop) :
    Finsupp.Lex r s = InvImage (Dfinsupp.Lex r fun a => s) toDfinsupp :=
  rfl
#align finsupp.lex_eq_inv_image_dfinsupp_lex Finsupp.lex_eq_inv_image_dfinsupp_lex

instance [LT α] [LT N] : LT (Lex (α →₀ N)) :=
  ⟨fun f g => Finsupp.Lex (· < ·) (· < ·) (ofLex f) (ofLex g)⟩

theorem lex_lt_of_lt_of_preorder [Preorder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  Dfinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.toDfinsupp < y.toDfinsupp)
#align finsupp.lex_lt_of_lt_of_preorder Finsupp.lex_lt_of_lt_of_preorder

theorem lex_lt_of_lt [PartialOrder N] (r) [IsStrictOrder α r] {x y : α →₀ N} (hlt : x < y) :
    Pi.Lex r (fun i => (· < ·)) x y :=
  Dfinsupp.lex_lt_of_lt r (id hlt : x.toDfinsupp < y.toDfinsupp)
#align finsupp.lex_lt_of_lt Finsupp.lex_lt_of_lt

instance Lex.is_strict_order [LinearOrder α] [PartialOrder N] :
    IsStrictOrder (Lex (α →₀ N)) (· < ·) :=
  let i : IsStrictOrder (Lex (α → N)) (· < ·) := Pi.Lex.isStrictOrder
  { irrefl := toLex.Surjective.forall.2 fun a => @irrefl _ _ i.to_is_irrefl a
    trans := toLex.Surjective.forall₃.2 fun a b c => @trans _ _ i.to_is_trans a b c }
#align finsupp.lex.is_strict_order Finsupp.Lex.is_strict_order

variable [LinearOrder α]

/-- The partial order on `finsupp`s obtained by the lexicographic ordering.
See `finsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance Lex.partialOrder [PartialOrder N] : PartialOrder (Lex (α →₀ N)) :=
  PartialOrder.lift (fun x => toLex ⇑(ofLex x)) Finsupp.coe_fn_injective
#align finsupp.lex.partial_order Finsupp.Lex.partialOrder

--fun_like.coe_injective
/-- The linear order on `finsupp`s obtained by the lexicographic ordering. -/
instance Lex.linearOrder [LinearOrder N] : LinearOrder (Lex (α →₀ N)) :=
  { Lex.partialOrder,
    LinearOrder.lift' (toLex ∘ to_dfinsupp ∘ ofLex) finsuppEquivDfinsupp.Injective with }
#align finsupp.lex.linear_order Finsupp.Lex.linearOrder

variable [PartialOrder N]

theorem to_lex_monotone : Monotone (@toLex (α →₀ N)) := fun a b h =>
  Dfinsupp.to_lex_monotone (id h : ∀ i, ofLex (toDfinsupp a) i ≤ ofLex (toDfinsupp b) i)
#align finsupp.to_lex_monotone Finsupp.to_lex_monotone

theorem lt_of_forall_lt_of_lt (a b : Lex (α →₀ N)) (i : α) :
    (∀ j < i, ofLex a j = ofLex b j) → ofLex a i < ofLex b i → a < b := fun h1 h2 => ⟨i, h1, h2⟩
#align finsupp.lt_of_forall_lt_of_lt Finsupp.lt_of_forall_lt_of_lt

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

instance Lex.covariant_class_lt_left :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg ((· + ·) _) (lta j ja), add_lt_add_left ha _⟩⟩
#align finsupp.lex.covariant_class_lt_left Finsupp.Lex.covariant_class_lt_left

instance Lex.covariant_class_le_left :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (· + ·) (· ≤ ·) :=
  Add.to_covariantClass_left _
#align finsupp.lex.covariant_class_le_left Finsupp.Lex.covariant_class_le_left

end Left

section Right

variable [CovariantClass N N (Function.swap (· + ·)) (· < ·)]

instance Lex.covariant_class_lt_right :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· < ·) :=
  ⟨fun f g h ⟨a, lta, ha⟩ =>
    ⟨a, fun j ja => congr_arg (· + ofLex f j) (lta j ja), add_lt_add_right ha _⟩⟩
#align finsupp.lex.covariant_class_lt_right Finsupp.Lex.covariant_class_lt_right

instance Lex.covariant_class_le_right :
    CovariantClass (Lex (α →₀ N)) (Lex (α →₀ N)) (Function.swap (· + ·)) (· ≤ ·) :=
  Add.to_covariantClass_right _
#align finsupp.lex.covariant_class_le_right Finsupp.Lex.covariant_class_le_right

end Right

end Covariants

end Finsupp

