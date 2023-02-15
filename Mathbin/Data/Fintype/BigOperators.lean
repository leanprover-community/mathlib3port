/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.big_operators
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Option
import Mathbin.Data.Fintype.Powerset
import Mathbin.Data.Fintype.Sigma
import Mathbin.Data.Fintype.Sum
import Mathbin.Data.Fintype.Vector
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Algebra.BigOperators.Option

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This content had previously been in `data.fintype.basic`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.

However many of the results here really belong in `algebra.big_operators.basic`
and should be moved at some point.
-/


universe u v

variable {α : Type _} {β : Type _} {γ : Type _}

open BigOperators

namespace Fintype

/- warning: fintype.prod_bool -> Fintype.prod_bool is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (f : Bool -> α), Eq.{succ u1} α (Finset.prod.{u1, 0} α Bool _inst_1 (Finset.univ.{0} Bool Bool.fintype) (fun (b : Bool) => f b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (f Bool.true) (f Bool.false))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (f : Bool -> α), Eq.{succ u1} α (Finset.prod.{u1, 0} α Bool _inst_1 (Finset.univ.{0} Bool instFintypeBool) (fun (b : Bool) => f b)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (f Bool.true) (f Bool.false))
Case conversion may be inaccurate. Consider using '#align fintype.prod_bool Fintype.prod_boolₓ'. -/
@[to_additive]
theorem prod_bool [CommMonoid α] (f : Bool → α) : (∏ b, f b) = f true * f false := by simp
#align fintype.prod_bool Fintype.prod_bool
#align fintype.sum_bool Fintype.sum_bool

#print Fintype.card_eq_sum_ones /-
theorem card_eq_sum_ones {α} [Fintype α] : Fintype.card α = ∑ a : α, 1 :=
  Finset.card_eq_sum_ones _
#align fintype.card_eq_sum_ones Fintype.card_eq_sum_ones
-/

section

open Finset

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

/- warning: fintype.prod_extend_by_one -> Fintype.prod_extend_by_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} ι] [_inst_2 : Fintype.{u2} ι] [_inst_3 : CommMonoid.{u1} α] (s : Finset.{u2} ι) (f : ι -> α), Eq.{succ u1} α (Finset.prod.{u1, u2} α ι _inst_3 (Finset.univ.{u2} ι _inst_2) (fun (i : ι) => ite.{succ u1} α (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) (Finset.decidableMem.{u2} ι (fun (a : ι) (b : ι) => _inst_1 a b) i s) (f i) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_3)))))))) (Finset.prod.{u1, u2} α ι _inst_3 s (fun (i : ι) => f i))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Fintype.{u1} ι] [_inst_3 : CommMonoid.{u2} α] (s : Finset.{u1} ι) (f : ι -> α), Eq.{succ u2} α (Finset.prod.{u2, u1} α ι _inst_3 (Finset.univ.{u1} ι _inst_2) (fun (i : ι) => ite.{succ u2} α (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) (Finset.decidableMem.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b) i s) (f i) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α (Monoid.toOne.{u2} α (CommMonoid.toMonoid.{u2} α _inst_3)))))) (Finset.prod.{u2, u1} α ι _inst_3 s (fun (i : ι) => f i))
Case conversion may be inaccurate. Consider using '#align fintype.prod_extend_by_one Fintype.prod_extend_by_oneₓ'. -/
@[to_additive]
theorem prod_extend_by_one [CommMonoid α] (s : Finset ι) (f : ι → α) :
    (∏ i, if i ∈ s then f i else 1) = ∏ i in s, f i := by
  rw [← prod_filter, filter_mem_eq_inter, univ_inter]
#align fintype.prod_extend_by_one Fintype.prod_extend_by_one
#align fintype.sum_extend_by_zero Fintype.sum_extend_by_zero

end

section

variable {M : Type _} [Fintype α] [CommMonoid M]

/- warning: fintype.prod_eq_one -> Fintype.prod_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} M] (f : α -> M), (forall (a : α), Eq.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))))) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))))))
but is expected to have type
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} M] (f : α -> M), (forall (a : α), Eq.{succ u2} M (f a) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (a : α) => f a)) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))))
Case conversion may be inaccurate. Consider using '#align fintype.prod_eq_one Fintype.prod_eq_oneₓ'. -/
@[to_additive]
theorem prod_eq_one (f : α → M) (h : ∀ a, f a = 1) : (∏ a, f a) = 1 :=
  Finset.prod_eq_one fun a ha => h a
#align fintype.prod_eq_one Fintype.prod_eq_one
#align fintype.sum_eq_zero Fintype.sum_eq_zero

#print Fintype.prod_congr /-
@[to_additive]
theorem prod_congr (f g : α → M) (h : ∀ a, f a = g a) : (∏ a, f a) = ∏ a, g a :=
  Finset.prod_congr rfl fun a ha => h a
#align fintype.prod_congr Fintype.prod_congr
#align fintype.sum_congr Fintype.sum_congr
-/

/- warning: fintype.prod_eq_single -> Fintype.prod_eq_single is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} M] {f : α -> M} (a : α), (forall (x : α), (Ne.{succ u1} α x a) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))))))) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (x : α) => f x)) (f a))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} M] {f : α -> M} (a : α), (forall (x : α), (Ne.{succ u2} α x a) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))))) -> (Eq.{succ u1} M (Finset.prod.{u1, u2} M α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (x : α) => f x)) (f a))
Case conversion may be inaccurate. Consider using '#align fintype.prod_eq_single Fintype.prod_eq_singleₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ≠ » a) -/
@[to_additive]
theorem prod_eq_single {f : α → M} (a : α) (h : ∀ (x) (_ : x ≠ a), f x = 1) : (∏ x, f x) = f a :=
  Finset.prod_eq_single a (fun x _ hx => h x hx) fun ha => (ha (Finset.mem_univ a)).elim
#align fintype.prod_eq_single Fintype.prod_eq_single
#align fintype.sum_eq_single Fintype.sum_eq_single

/- warning: fintype.prod_eq_mul -> Fintype.prod_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} M] {f : α -> M} (a : α) (b : α), (Ne.{succ u1} α a b) -> (forall (x : α), (And (Ne.{succ u1} α x a) (Ne.{succ u1} α x b)) -> (Eq.{succ u2} M (f x) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))))))) -> (Eq.{succ u2} M (Finset.prod.{u2, u1} M α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (x : α) => f x)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))) (f a) (f b)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} M] {f : α -> M} (a : α) (b : α), (Ne.{succ u2} α a b) -> (forall (x : α), (And (Ne.{succ u2} α x a) (Ne.{succ u2} α x b)) -> (Eq.{succ u1} M (f x) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))))) -> (Eq.{succ u1} M (Finset.prod.{u1, u2} M α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (x : α) => f x)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) (f a) (f b)))
Case conversion may be inaccurate. Consider using '#align fintype.prod_eq_mul Fintype.prod_eq_mulₓ'. -/
@[to_additive]
theorem prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) :
    (∏ x, f x) = f a * f b := by
  apply Finset.prod_eq_mul a b h₁ fun x _ hx => h₂ x hx <;>
    exact fun hc => (hc (Finset.mem_univ _)).elim
#align fintype.prod_eq_mul Fintype.prod_eq_mul
#align fintype.sum_eq_add Fintype.sum_eq_add

#print Fintype.eq_of_subsingleton_of_prod_eq /-
/-- If a product of a `finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive
      "If a sum of a `finset` of a subsingleton type has a given\nvalue, so do the terms in that sum."]
theorem eq_of_subsingleton_of_prod_eq {ι : Type _} [Subsingleton ι] {s : Finset ι} {f : ι → M}
    {b : M} (h : (∏ i in s, f i) = b) : ∀ i ∈ s, f i = b :=
  Finset.eq_of_card_le_one_of_prod_eq (Finset.card_le_one_of_subsingleton s) h
#align fintype.eq_of_subsingleton_of_prod_eq Fintype.eq_of_subsingleton_of_prod_eq
#align fintype.eq_of_subsingleton_of_sum_eq Fintype.eq_of_subsingleton_of_sum_eq
-/

end

end Fintype

open Finset

section

variable {M : Type _} [Fintype α] [CommMonoid M]

/- warning: fintype.prod_option -> Fintype.prod_option is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} M] (f : (Option.{u1} α) -> M), Eq.{succ u2} M (Finset.prod.{u2, u1} M (Option.{u1} α) _inst_2 (Finset.univ.{u1} (Option.{u1} α) (Option.fintype.{u1} α _inst_1)) (fun (i : Option.{u1} α) => f i)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))) (f (Option.none.{u1} α)) (Finset.prod.{u2, u1} M α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (i : α) => f (Option.some.{u1} α i))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} M] (f : (Option.{u2} α) -> M), Eq.{succ u1} M (Finset.prod.{u1, u2} M (Option.{u2} α) _inst_2 (Finset.univ.{u2} (Option.{u2} α) (instFintypeOption.{u2} α _inst_1)) (fun (i : Option.{u2} α) => f i)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) (f (Option.none.{u2} α)) (Finset.prod.{u1, u2} M α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (i : α) => f (Option.some.{u2} α i))))
Case conversion may be inaccurate. Consider using '#align fintype.prod_option Fintype.prod_optionₓ'. -/
@[simp, to_additive]
theorem Fintype.prod_option (f : Option α → M) : (∏ i, f i) = f none * ∏ i, f (some i) :=
  Finset.prod_insertNone f univ
#align fintype.prod_option Fintype.prod_option
#align fintype.sum_option Fintype.sum_option

end

open Finset

/- warning: fintype.card_sigma -> Fintype.card_sigma is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (β : α -> Type.{u2}) [_inst_1 : Fintype.{u1} α] [_inst_2 : forall (a : α), Fintype.{u2} (β a)], Eq.{1} Nat (Fintype.card.{max u1 u2} (Sigma.{u1, u2} α β) (Sigma.fintype.{u1, u2} α β _inst_1 (fun (a : α) => _inst_2 a))) (Finset.sum.{0, u1} Nat α Nat.addCommMonoid (Finset.univ.{u1} α _inst_1) (fun (a : α) => Fintype.card.{u2} (β a) (_inst_2 a)))
but is expected to have type
  forall {α : Type.{u2}} (β : α -> Type.{u1}) [_inst_1 : Fintype.{u2} α] [_inst_2 : forall (a : α), Fintype.{u1} (β a)], Eq.{1} Nat (Fintype.card.{max u1 u2} (Sigma.{u2, u1} α β) (instFintypeSigma.{u2, u1} α β _inst_1 (fun (a : α) => _inst_2 a))) (Finset.sum.{0, u2} Nat α Nat.addCommMonoid (Finset.univ.{u2} α _inst_1) (fun (a : α) => Fintype.card.{u1} (β a) (_inst_2 a)))
Case conversion may be inaccurate. Consider using '#align fintype.card_sigma Fintype.card_sigmaₓ'. -/
@[simp]
theorem Fintype.card_sigma {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] :
    Fintype.card (Sigma β) = ∑ a, Fintype.card (β a) :=
  card_sigma _ _
#align fintype.card_sigma Fintype.card_sigma

/- warning: finset.card_pi -> Finset.card_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {δ : α -> Type.{u2}} (s : Finset.{u1} α) (t : forall (a : α), Finset.{u2} (δ a)), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (δ a)) (Finset.pi.{u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (Finset.prod.{0, u1} Nat α Nat.commMonoid s (fun (a : α) => Finset.card.{u2} (δ a) (t a)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] {δ : α -> Type.{u1}} (s : Finset.{u2} α) (t : forall (a : α), Finset.{u1} (δ a)), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (δ a)) (Finset.pi.{u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) s t)) (Finset.prod.{0, u2} Nat α Nat.commMonoid s (fun (a : α) => Finset.card.{u1} (δ a) (t a)))
Case conversion may be inaccurate. Consider using '#align finset.card_pi Finset.card_piₓ'. -/
@[simp]
theorem Finset.card_pi [DecidableEq α] {δ : α → Type _} (s : Finset α) (t : ∀ a, Finset (δ a)) :
    (s.pi t).card = ∏ a in s, card (t a) :=
  Multiset.card_pi _ _
#align finset.card_pi Finset.card_pi

/- warning: fintype.card_pi_finset -> Fintype.card_piFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {δ : α -> Type.{u2}} (t : forall (a : α), Finset.{u2} (δ a)), Eq.{1} Nat (Finset.card.{max u1 u2} (forall (a : α), δ a) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t)) (Finset.prod.{0, u1} Nat α Nat.commMonoid (Finset.univ.{u1} α _inst_2) (fun (a : α) => Finset.card.{u2} (δ a) (t a)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] {δ : α -> Type.{u1}} (t : forall (a : α), Finset.{u1} (δ a)), Eq.{1} Nat (Finset.card.{max u2 u1} (forall (a : α), δ a) (Fintype.piFinset.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t)) (Finset.prod.{0, u2} Nat α Nat.commMonoid (Finset.univ.{u2} α _inst_2) (fun (a : α) => Finset.card.{u1} (δ a) (t a)))
Case conversion may be inaccurate. Consider using '#align fintype.card_pi_finset Fintype.card_piFinsetₓ'. -/
@[simp]
theorem Fintype.card_piFinset [DecidableEq α] [Fintype α] {δ : α → Type _} (t : ∀ a, Finset (δ a)) :
    (Fintype.piFinset t).card = ∏ a, card (t a) := by simp [Fintype.piFinset, card_map]
#align fintype.card_pi_finset Fintype.card_piFinset

#print Fintype.card_pi /-
@[simp]
theorem Fintype.card_pi {β : α → Type _} [DecidableEq α] [Fintype α] [f : ∀ a, Fintype (β a)] :
    Fintype.card (∀ a, β a) = ∏ a, Fintype.card (β a) :=
  Fintype.card_piFinset _
#align fintype.card_pi Fintype.card_pi
-/

/- warning: fintype.card_fun -> Fintype.card_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : Fintype.{u2} β], Eq.{1} Nat (Fintype.card.{max u1 u2} (α -> β) (Pi.fintype.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => _inst_3))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (Fintype.card.{u2} β _inst_3) (Fintype.card.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] [_inst_3 : Fintype.{u1} β], Eq.{1} Nat (Fintype.card.{max u2 u1} (α -> β) (Pi.fintype.{u2, u1} α (fun (ᾰ : α) => β) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => _inst_3))) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (Fintype.card.{u1} β _inst_3) (Fintype.card.{u2} α _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_fun Fintype.card_funₓ'. -/
-- FIXME ouch, this should be in the main file.
@[simp]
theorem Fintype.card_fun [DecidableEq α] [Fintype α] [Fintype β] :
    Fintype.card (α → β) = Fintype.card β ^ Fintype.card α := by
  rw [Fintype.card_pi, Finset.prod_const] <;> rfl
#align fintype.card_fun Fintype.card_fun

#print card_vector /-
@[simp]
theorem card_vector [Fintype α] (n : ℕ) : Fintype.card (Vector α n) = Fintype.card α ^ n := by
  rw [Fintype.ofEquiv_card] <;> simp
#align card_vector card_vector
-/

/- warning: finset.prod_attach_univ -> Finset.prod_attach_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : CommMonoid.{u2} β] (f : (Subtype.{succ u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_1))) -> β), Eq.{succ u2} β (Finset.prod.{u2, u1} β (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.univ.{u1} α _inst_1))) _inst_2 (Finset.attach.{u1} α (Finset.univ.{u1} α _inst_1)) (fun (x : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.univ.{u1} α _inst_1))) => f x)) (Finset.prod.{u2, u1} β α _inst_2 (Finset.univ.{u1} α _inst_1) (fun (x : α) => f (Subtype.mk.{succ u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_1)) x (Finset.mem_univ.{u1} α _inst_1 x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : CommMonoid.{u1} β] (f : (Subtype.{succ u2} α (fun (a : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_1))) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.univ.{u2} α _inst_1))) _inst_2 (Finset.attach.{u2} α (Finset.univ.{u2} α _inst_1)) (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.univ.{u2} α _inst_1))) => f x)) (Finset.prod.{u1, u2} β α _inst_2 (Finset.univ.{u2} α _inst_1) (fun (x : α) => f (Subtype.mk.{succ u2} α (fun (a : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_1)) x (Finset.mem_univ.{u2} α _inst_1 x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_attach_univ Finset.prod_attach_univₓ'. -/
@[simp, to_additive]
theorem Finset.prod_attach_univ [Fintype α] [CommMonoid β] (f : { a : α // a ∈ @univ α _ } → β) :
    (∏ x in univ.attach, f x) = ∏ x, f ⟨x, mem_univ _⟩ :=
  Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun x => mem_univ _) _ _ fun x => by simp
#align finset.prod_attach_univ Finset.prod_attach_univ
#align finset.sum_attach_univ Finset.sum_attach_univ

/- warning: finset.prod_univ_pi -> Finset.prod_univ_pi is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : CommMonoid.{u2} β] {δ : α -> Type.{u3}} {t : forall (a : α), Finset.{u3} (δ a)} (f : (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) -> (δ a)) -> β), Eq.{succ u2} β (Finset.prod.{u2, max u1 u3} β (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) -> (δ a)) _inst_3 (Finset.pi.{u1, u3} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) (Finset.univ.{u1} α _inst_2) t) (fun (x : forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) -> (δ a)) => f x)) (Finset.prod.{u2, max u1 u3} β (forall (a : α), δ a) _inst_3 (Fintype.piFinset.{u1, u3} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t) (fun (x : forall (a : α), δ a) => f (fun (a : α) (_x : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) => x a)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u3} α] [_inst_2 : Fintype.{u3} α] [_inst_3 : CommMonoid.{u2} β] {δ : α -> Type.{u1}} {t : forall (a : α), Finset.{u1} (δ a)} (f : (forall (a : α), (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a (Finset.univ.{u3} α _inst_2)) -> (δ a)) -> β), Eq.{succ u2} β (Finset.prod.{u2, max u1 u3} β (forall (a : α), (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a (Finset.univ.{u3} α _inst_2)) -> (δ a)) _inst_3 (Finset.pi.{u3, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_1 a b) (Finset.univ.{u3} α _inst_2) t) (fun (x : forall (a : α), (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a (Finset.univ.{u3} α _inst_2)) -> (δ a)) => f x)) (Finset.prod.{u2, max u1 u3} β (forall (a : α), δ a) _inst_3 (Fintype.piFinset.{u3, u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t) (fun (x : forall (a : α), δ a) => f (fun (a : α) (_x : Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a (Finset.univ.{u3} α _inst_2)) => x a)))
Case conversion may be inaccurate. Consider using '#align finset.prod_univ_pi Finset.prod_univ_piₓ'. -/
/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
@[to_additive
      "Taking a sum over `univ.pi t` is the same as taking the sum over\n  `fintype.pi_finset t`. `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`,\n  but differ in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and\n  `fintype.pi_finset t` is a `finset (Π a, t a)`."]
theorem Finset.prod_univ_pi [DecidableEq α] [Fintype α] [CommMonoid β] {δ : α → Type _}
    {t : ∀ a : α, Finset (δ a)} (f : (∀ a : α, a ∈ (univ : Finset α) → δ a) → β) :
    (∏ x in univ.pi t, f x) = ∏ x in Fintype.piFinset t, f fun a _ => x a :=
  prod_bij (fun x _ a => x a (mem_univ _)) (by simp) (by simp)
    (by simp (config := { contextual := true }) [Function.funext_iff]) fun x hx =>
    ⟨fun a _ => x a, by simp_all⟩
#align finset.prod_univ_pi Finset.prod_univ_pi
#align finset.sum_univ_pi Finset.sum_univ_pi

/- warning: finset.prod_univ_sum -> Finset.prod_univ_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {β : Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} α] [_inst_2 : Fintype.{u_1} α] [_inst_3 : CommSemiring.{u_2} β] {δ : α -> Type.{u_1}} [_inst_4 : forall (a : α), DecidableEq.{succ u_1} (δ a)] {t : forall (a : α), Finset.{u_1} (δ a)} {f : forall (a : α), (δ a) -> β}, Eq.{succ u_2} β (Finset.prod.{u_2, u_1} β α (CommSemiring.toCommMonoid.{u_2} β _inst_3) (Finset.univ.{u_1} α _inst_2) (fun (a : α) => Finset.sum.{u_2, u_1} β (δ a) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u_2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_2} β (Semiring.toNonAssocSemiring.{u_2} β (CommSemiring.toSemiring.{u_2} β _inst_3)))) (t a) (fun (b : δ a) => f a b))) (Finset.sum.{u_2, u_1} β (forall (a : α), δ a) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u_2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_2} β (Semiring.toNonAssocSemiring.{u_2} β (CommSemiring.toSemiring.{u_2} β _inst_3)))) (Fintype.piFinset.{u_1, u_1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t) (fun (p : forall (a : α), δ a) => Finset.prod.{u_2, u_1} β α (CommSemiring.toCommMonoid.{u_2} β _inst_3) (Finset.univ.{u_1} α _inst_2) (fun (x : α) => f x (p x))))
but is expected to have type
  forall {α : Type.{u_2}} {β : Type.{u_3}} [_inst_1 : DecidableEq.{succ u_2} α] [_inst_2 : Fintype.{u_2} α] [_inst_3 : CommSemiring.{u_3} β] {δ : α -> Type.{u_1}} [_inst_4 : forall (a : α), DecidableEq.{succ u_1} (δ a)] {t : forall (a : α), Finset.{u_1} (δ a)} {f : forall (a : α), (δ a) -> β}, Eq.{succ u_3} β (Finset.prod.{u_3, u_2} β α (CommSemiring.toCommMonoid.{u_3} β _inst_3) (Finset.univ.{u_2} α _inst_2) (fun (a : α) => Finset.sum.{u_3, u_1} β (δ a) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u_3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_3} β (Semiring.toNonAssocSemiring.{u_3} β (CommSemiring.toSemiring.{u_3} β _inst_3)))) (t a) (fun (b : δ a) => f a b))) (Finset.sum.{u_3, max u_1 u_2} β (forall (a : α), δ a) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u_3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_3} β (Semiring.toNonAssocSemiring.{u_3} β (CommSemiring.toSemiring.{u_3} β _inst_3)))) (Fintype.piFinset.{u_2, u_1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t) (fun (p : forall (a : α), δ a) => Finset.prod.{u_3, u_2} β α (CommSemiring.toCommMonoid.{u_3} β _inst_3) (Finset.univ.{u_2} α _inst_2) (fun (x : α) => f x (p x))))
Case conversion may be inaccurate. Consider using '#align finset.prod_univ_sum Finset.prod_univ_sumₓ'. -/
/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
theorem Finset.prod_univ_sum [DecidableEq α] [Fintype α] [CommSemiring β] {δ : α → Type u_1}
    [∀ a : α, DecidableEq (δ a)] {t : ∀ a : α, Finset (δ a)} {f : ∀ a : α, δ a → β} :
    (∏ a, ∑ b in t a, f a b) = ∑ p in Fintype.piFinset t, ∏ x, f x (p x) := by
  simp only [Finset.prod_attach_univ, prod_sum, Finset.sum_univ_pi]
#align finset.prod_univ_sum Finset.prod_univ_sum

/- warning: fintype.sum_pow_mul_eq_add_pow -> Fintype.sum_pow_mul_eq_add_pow is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α] {R : Type.{u2}} [_inst_2 : CommSemiring.{u2} R] (a : R) (b : R), Eq.{succ u2} R (Finset.sum.{u2, u1} R (Finset.{u1} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))) (Finset.univ.{u1} (Finset.{u1} α) (Finset.fintype.{u1} α _inst_1)) (fun (s : Finset.{u1} α) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))))) a (Finset.card.{u1} α s)) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))))) b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Fintype.card.{u1} α _inst_1) (Finset.card.{u1} α s))))) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2))))) (HAdd.hAdd.{u2, u2, u2} R R R (instHAdd.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_2)))))) a b) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u2}) [_inst_1 : Fintype.{u2} α] {R : Type.{u1}} [_inst_2 : CommSemiring.{u1} R] (a : R) (b : R), Eq.{succ u1} R (Finset.sum.{u1, u2} R (Finset.{u2} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) (Finset.univ.{u2} (Finset.{u2} α) (Finset.fintype.{u2} α _inst_1)) (fun (s : Finset.{u2} α) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) a (Finset.card.{u2} α s)) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) b (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fintype.card.{u2} α _inst_1) (Finset.card.{u2} α s))))) (HPow.hPow.{u1, 0, u1} R Nat R (instHPow.{u1, 0} R Nat (Monoid.Pow.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))))) (HAdd.hAdd.{u1, u1, u1} R R R (instHAdd.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))))) a b) (Fintype.card.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align fintype.sum_pow_mul_eq_add_pow Fintype.sum_pow_mul_eq_add_powₓ'. -/
/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
theorem Fintype.sum_pow_mul_eq_add_pow (α : Type _) [Fintype α] {R : Type _} [CommSemiring R]
    (a b : R) :
    (∑ s : Finset α, a ^ s.card * b ^ (Fintype.card α - s.card)) = (a + b) ^ Fintype.card α :=
  Finset.sum_pow_mul_eq_add_pow _ _ _
#align fintype.sum_pow_mul_eq_add_pow Fintype.sum_pow_mul_eq_add_pow

/- warning: function.bijective.prod_comp -> Function.Bijective.prod_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u3} γ] {f : α -> β}, (Function.Bijective.{succ u1, succ u2} α β f) -> (forall (g : β -> γ), Eq.{succ u3} γ (Finset.prod.{u3, u1} γ α _inst_3 (Finset.univ.{u1} α _inst_1) (fun (i : α) => g (f i))) (Finset.prod.{u3, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (i : β) => g i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Fintype.{u3} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u1} γ] {f : α -> β}, (Function.Bijective.{succ u3, succ u2} α β f) -> (forall (g : β -> γ), Eq.{succ u1} γ (Finset.prod.{u1, u3} γ α _inst_3 (Finset.univ.{u3} α _inst_1) (fun (i : α) => g (f i))) (Finset.prod.{u1, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (i : β) => g i)))
Case conversion may be inaccurate. Consider using '#align function.bijective.prod_comp Function.Bijective.prod_compₓ'. -/
@[to_additive]
theorem Function.Bijective.prod_comp [Fintype α] [Fintype β] [CommMonoid γ] {f : α → β}
    (hf : Function.Bijective f) (g : β → γ) : (∏ i, g (f i)) = ∏ i, g i :=
  Fintype.prod_bijective f hf _ _ fun x => rfl
#align function.bijective.prod_comp Function.Bijective.prod_comp
#align function.bijective.sum_comp Function.Bijective.sum_comp

/- warning: equiv.prod_comp -> Equiv.prod_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u3} γ] (e : Equiv.{succ u1, succ u2} α β) (f : β -> γ), Eq.{succ u3} γ (Finset.prod.{u3, u1} γ α _inst_3 (Finset.univ.{u1} α _inst_1) (fun (i : α) => f (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e i))) (Finset.prod.{u3, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (i : β) => f i))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Fintype.{u3} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u1} γ] (e : Equiv.{succ u3, succ u2} α β) (f : β -> γ), Eq.{succ u1} γ (Finset.prod.{u1, u3} γ α _inst_3 (Finset.univ.{u3} α _inst_1) (fun (i : α) => f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} α β) e i))) (Finset.prod.{u1, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (i : β) => f i))
Case conversion may be inaccurate. Consider using '#align equiv.prod_comp Equiv.prod_compₓ'. -/
@[to_additive]
theorem Equiv.prod_comp [Fintype α] [Fintype β] [CommMonoid γ] (e : α ≃ β) (f : β → γ) :
    (∏ i, f (e i)) = ∏ i, f i :=
  e.Bijective.prod_comp f
#align equiv.prod_comp Equiv.prod_comp
#align equiv.sum_comp Equiv.sum_comp

/- warning: equiv.prod_comp' -> Equiv.prod_comp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u3} γ] (e : Equiv.{succ u1, succ u2} α β) (f : α -> γ) (g : β -> γ), (forall (i : α), Eq.{succ u3} γ (f i) (g (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) e i))) -> (Eq.{succ u3} γ (Finset.prod.{u3, u1} γ α _inst_3 (Finset.univ.{u1} α _inst_1) (fun (i : α) => f i)) (Finset.prod.{u3, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (i : β) => g i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Fintype.{u3} α] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u1} γ] (e : Equiv.{succ u3, succ u2} α β) (f : α -> γ) (g : β -> γ), (forall (i : α), Eq.{succ u1} γ (f i) (g (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Equiv.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u2} α β) e i))) -> (Eq.{succ u1} γ (Finset.prod.{u1, u3} γ α _inst_3 (Finset.univ.{u3} α _inst_1) (fun (i : α) => f i)) (Finset.prod.{u1, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (i : β) => g i)))
Case conversion may be inaccurate. Consider using '#align equiv.prod_comp' Equiv.prod_comp'ₓ'. -/
@[to_additive]
theorem Equiv.prod_comp' [Fintype α] [Fintype β] [CommMonoid γ] (e : α ≃ β) (f : α → γ) (g : β → γ)
    (h : ∀ i, f i = g (e i)) : (∏ i, f i) = ∏ i, g i :=
  (show f = g ∘ e from funext h).symm ▸ e.prod_comp _
#align equiv.prod_comp' Equiv.prod_comp'
#align equiv.sum_comp' Equiv.sum_comp'

#print Fin.prod_univ_eq_prod_range /-
/-- It is equivalent to compute the product of a function over `fin n` or `finset.range n`. -/
@[to_additive "It is equivalent to sum a function over `fin n` or `finset.range n`."]
theorem Fin.prod_univ_eq_prod_range [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    (∏ i : Fin n, f i) = ∏ i in range n, f i :=
  calc
    (∏ i : Fin n, f i) = ∏ i : { x // x ∈ range n }, f i :=
      (Fin.equivSubtype.trans (Equiv.subtypeEquivRight (by simp))).prod_comp' _ _ (by simp)
    _ = ∏ i in range n, f i := by rw [← attach_eq_univ, prod_attach]
    
#align fin.prod_univ_eq_prod_range Fin.prod_univ_eq_prod_range
#align fin.sum_univ_eq_sum_range Fin.sum_univ_eq_sum_range
-/

/- warning: finset.prod_fin_eq_prod_range -> Finset.prod_fin_eq_prod_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (c : (Fin n) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => c i)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (i : Nat) => dite.{succ u1} β (LT.lt.{0} Nat Nat.hasLt i n) (Nat.decidableLt i n) (fun (h : LT.lt.{0} Nat Nat.hasLt i n) => c (Fin.mk n i h)) (fun (h : Not (LT.lt.{0} Nat Nat.hasLt i n)) => OfNat.ofNat.{u1} β 1 (OfNat.mk.{u1} β 1 (One.one.{u1} β (MulOneClass.toHasOne.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : CommMonoid.{u1} β] {n : Nat} (c : (Fin n) -> β), Eq.{succ u1} β (Finset.prod.{u1, 0} β (Fin n) _inst_1 (Finset.univ.{0} (Fin n) (Fin.fintype n)) (fun (i : Fin n) => c i)) (Finset.prod.{u1, 0} β Nat _inst_1 (Finset.range n) (fun (i : Nat) => dite.{succ u1} β (LT.lt.{0} Nat instLTNat i n) (Nat.decLt i n) (fun (h : LT.lt.{0} Nat instLTNat i n) => c (Fin.mk n i h)) (fun (h : Not (LT.lt.{0} Nat instLTNat i n)) => OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Monoid.toOne.{u1} β (CommMonoid.toMonoid.{u1} β _inst_1))))))
Case conversion may be inaccurate. Consider using '#align finset.prod_fin_eq_prod_range Finset.prod_fin_eq_prod_rangeₓ'. -/
@[to_additive]
theorem Finset.prod_fin_eq_prod_range [CommMonoid β] {n : ℕ} (c : Fin n → β) :
    (∏ i, c i) = ∏ i in Finset.range n, if h : i < n then c ⟨i, h⟩ else 1 :=
  by
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_congr rfl]
  rintro ⟨i, hi⟩ _
  simp only [[anonymous], hi, dif_pos]
#align finset.prod_fin_eq_prod_range Finset.prod_fin_eq_prod_range
#align finset.sum_fin_eq_sum_range Finset.sum_fin_eq_sum_range

#print Finset.prod_toFinset_eq_subtype /-
@[to_additive]
theorem Finset.prod_toFinset_eq_subtype {M : Type _} [CommMonoid M] [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → M) : (∏ a in { x | p x }.toFinset, f a) = ∏ a : Subtype p, f a :=
  by
  rw [← Finset.prod_subtype]
  simp
#align finset.prod_to_finset_eq_subtype Finset.prod_toFinset_eq_subtype
#align finset.sum_to_finset_eq_subtype Finset.sum_toFinset_eq_subtype
-/

/- warning: finset.prod_fiberwise -> Finset.prod_fiberwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Fintype.{u2} β] [_inst_3 : CommMonoid.{u3} γ] (s : Finset.{u1} α) (f : α -> β) (g : α -> γ), Eq.{succ u3} γ (Finset.prod.{u3, u2} γ β _inst_3 (Finset.univ.{u2} β _inst_2) (fun (b : β) => Finset.prod.{u3, u1} γ α _inst_3 (Finset.filter.{u1} α (fun (a : α) => Eq.{succ u2} β (f a) b) (fun (a : α) => _inst_1 (f a) b) s) (fun (a : α) => g a))) (Finset.prod.{u3, u1} γ α _inst_3 s (fun (a : α) => g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : DecidableEq.{succ u3} β] [_inst_2 : Fintype.{u3} β] [_inst_3 : CommMonoid.{u2} γ] (s : Finset.{u1} α) (f : α -> β) (g : α -> γ), Eq.{succ u2} γ (Finset.prod.{u2, u3} γ β _inst_3 (Finset.univ.{u3} β _inst_2) (fun (b : β) => Finset.prod.{u2, u1} γ α _inst_3 (Finset.filter.{u1} α (fun (a : α) => Eq.{succ u3} β (f a) b) (fun (a : α) => _inst_1 (f a) b) s) (fun (a : α) => g a))) (Finset.prod.{u2, u1} γ α _inst_3 s (fun (a : α) => g a))
Case conversion may be inaccurate. Consider using '#align finset.prod_fiberwise Finset.prod_fiberwiseₓ'. -/
@[to_additive]
theorem Finset.prod_fiberwise [DecidableEq β] [Fintype β] [CommMonoid γ] (s : Finset α) (f : α → β)
    (g : α → γ) : (∏ b : β, ∏ a in s.filterₓ fun a => f a = b, g a) = ∏ a in s, g a :=
  Finset.prod_fiberwise_of_maps_to (fun x _ => mem_univ _) _
#align finset.prod_fiberwise Finset.prod_fiberwise
#align finset.sum_fiberwise Finset.sum_fiberwise

/- warning: fintype.prod_fiberwise -> Fintype.prod_fiberwise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : Fintype.{u2} β] [_inst_4 : CommMonoid.{u3} γ] (f : α -> β) (g : α -> γ), Eq.{succ u3} γ (Finset.prod.{u3, u2} γ β _inst_4 (Finset.univ.{u2} β _inst_3) (fun (b : β) => Finset.prod.{u3, u1} γ (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) _inst_4 (Finset.univ.{u1} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) (Subtype.fintype.{u1} α (fun (a : α) => Eq.{succ u2} β (f a) b) (fun (a : α) => _inst_2 (f a) b) _inst_1)) (fun (a : Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) => g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b)) α (coeSubtype.{succ u1} α (fun (a : α) => Eq.{succ u2} β (f a) b))))) a)))) (Finset.prod.{u3, u1} γ α _inst_4 (Finset.univ.{u1} α _inst_1) (fun (a : α) => g a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Fintype.{u3} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : Fintype.{u2} β] [_inst_4 : CommMonoid.{u1} γ] (f : α -> β) (g : α -> γ), Eq.{succ u1} γ (Finset.prod.{u1, u2} γ β _inst_4 (Finset.univ.{u2} β _inst_3) (fun (b : β) => Finset.prod.{u1, u3} γ (Subtype.{succ u3} α (fun (a : α) => Eq.{succ u2} β (f a) b)) _inst_4 (Finset.univ.{u3} (Subtype.{succ u3} α (fun (a : α) => Eq.{succ u2} β (f a) b)) (Subtype.fintype.{u3} α (fun (a : α) => Eq.{succ u2} β (f a) b) (fun (a : α) => _inst_2 (f a) b) _inst_1)) (fun (a : Subtype.{succ u3} α (fun (a : α) => Eq.{succ u2} β (f a) b)) => g (Subtype.val.{succ u3} α (fun (a : α) => Eq.{succ u2} β (f a) b) a)))) (Finset.prod.{u1, u3} γ α _inst_4 (Finset.univ.{u3} α _inst_1) (fun (a : α) => g a))
Case conversion may be inaccurate. Consider using '#align fintype.prod_fiberwise Fintype.prod_fiberwiseₓ'. -/
@[to_additive]
theorem Fintype.prod_fiberwise [Fintype α] [DecidableEq β] [Fintype β] [CommMonoid γ] (f : α → β)
    (g : α → γ) : (∏ b : β, ∏ a : { a // f a = b }, g (a : α)) = ∏ a, g a :=
  by
  rw [← (Equiv.sigmaFiberEquiv f).prod_comp, ← univ_sigma_univ, prod_sigma]
  rfl
#align fintype.prod_fiberwise Fintype.prod_fiberwise
#align fintype.sum_fiberwise Fintype.sum_fiberwise

/- warning: fintype.prod_dite -> Fintype.prod_dite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u1} α p] [_inst_3 : CommMonoid.{u2} β] (f : forall (a : α), (p a) -> β) (g : forall (a : α), (Not (p a)) -> β), Eq.{succ u2} β (Finset.prod.{u2, u1} β α _inst_3 (Finset.univ.{u1} α _inst_1) (fun (a : α) => dite.{succ u2} β (p a) (_inst_2 a) (f a) (g a))) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_3)))) (Finset.prod.{u2, u1} β (Subtype.{succ u1} α (fun (a : α) => p a)) _inst_3 (Finset.univ.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)) (Subtype.fintype.{u1} α (fun (a : α) => p a) (fun (a : α) => _inst_2 a) _inst_1)) (fun (a : Subtype.{succ u1} α (fun (a : α) => p a)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (a : α) => p a)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => p a)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => p a)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => p a)) α (coeSubtype.{succ u1} α (fun (a : α) => p a))))) a) (Subtype.property.{succ u1} α (fun (a : α) => p a) a))) (Finset.prod.{u2, u1} β (Subtype.{succ u1} α (fun (a : α) => Not (p a))) _inst_3 (Finset.univ.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))) (Subtype.fintype.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => Not.decidable (p a) (_inst_2 a)) _inst_1)) (fun (a : Subtype.{succ u1} α (fun (a : α) => Not (p a))) => g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (a : α) => Not (p a))) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))) α (coeSubtype.{succ u1} α (fun (a : α) => Not (p a)))))) a) (Subtype.property.{succ u1} α (fun (a : α) => Not (p a)) a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] {p : α -> Prop} [_inst_2 : DecidablePred.{succ u2} α p] [_inst_3 : CommMonoid.{u1} β] (f : forall (a : α), (p a) -> β) (g : forall (a : α), (Not (p a)) -> β), Eq.{succ u1} β (Finset.prod.{u1, u2} β α _inst_3 (Finset.univ.{u2} α _inst_1) (fun (a : α) => dite.{succ u1} β (p a) (_inst_2 a) (f a) (g a))) (HMul.hMul.{u1, u1, u1} β β β (instHMul.{u1} β (MulOneClass.toMul.{u1} β (Monoid.toMulOneClass.{u1} β (CommMonoid.toMonoid.{u1} β _inst_3)))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (a : α) => p a)) _inst_3 (Finset.univ.{u2} (Subtype.{succ u2} α (fun (a : α) => p a)) (Subtype.fintype.{u2} α (fun (a : α) => p a) (fun (a : α) => _inst_2 a) _inst_1)) (fun (a : Subtype.{succ u2} α (fun (a : α) => p a)) => f (Subtype.val.{succ u2} α (fun (a : α) => p a) a) (Subtype.property.{succ u2} α (fun (a : α) => p a) a))) (Finset.prod.{u1, u2} β (Subtype.{succ u2} α (fun (a : α) => Not (p a))) _inst_3 (Finset.univ.{u2} (Subtype.{succ u2} α (fun (a : α) => Not (p a))) (Subtype.fintype.{u2} α (fun (a : α) => Not (p a)) (fun (a : α) => instDecidableNot (p a) (_inst_2 a)) _inst_1)) (fun (a : Subtype.{succ u2} α (fun (a : α) => Not (p a))) => g (Subtype.val.{succ u2} α (fun (a : α) => Not (p a)) a) (Subtype.property.{succ u2} α (fun (a : α) => Not (p a)) a))))
Case conversion may be inaccurate. Consider using '#align fintype.prod_dite Fintype.prod_diteₓ'. -/
theorem Fintype.prod_dite [Fintype α] {p : α → Prop} [DecidablePred p] [CommMonoid β]
    (f : ∀ (a : α) (ha : p a), β) (g : ∀ (a : α) (ha : ¬p a), β) :
    (∏ a, dite (p a) (f a) (g a)) = (∏ a : { a // p a }, f a a.2) * ∏ a : { a // ¬p a }, g a a.2 :=
  by
  simp only [prod_dite, attach_eq_univ]
  congr 1
  · convert (Equiv.subtypeEquivRight _).prod_comp fun x : { x // p x } => f x x.2
    simp
  · convert (Equiv.subtypeEquivRight _).prod_comp fun x : { x // ¬p x } => g x x.2
    simp
#align fintype.prod_dite Fintype.prod_dite

section

open Finset

variable {α₁ : Type _} {α₂ : Type _} {M : Type _} [Fintype α₁] [Fintype α₂] [CommMonoid M]

/- warning: fintype.prod_sum_elim -> Fintype.prod_sum_elim is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {M : Type.{u3}} [_inst_1 : Fintype.{u1} α₁] [_inst_2 : Fintype.{u2} α₂] [_inst_3 : CommMonoid.{u3} M] (f : α₁ -> M) (g : α₂ -> M), Eq.{succ u3} M (Finset.prod.{u3, max u1 u2} M (Sum.{u1, u2} α₁ α₂) _inst_3 (Finset.univ.{max u1 u2} (Sum.{u1, u2} α₁ α₂) (Sum.fintype.{u1, u2} α₁ α₂ _inst_1 _inst_2)) (fun (x : Sum.{u1, u2} α₁ α₂) => Sum.elim.{u1, u2, succ u3} α₁ α₂ M f g x)) (HMul.hMul.{u3, u3, u3} M M M (instHMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))) (Finset.prod.{u3, u1} M α₁ _inst_3 (Finset.univ.{u1} α₁ _inst_1) (fun (a₁ : α₁) => f a₁)) (Finset.prod.{u3, u2} M α₂ _inst_3 (Finset.univ.{u2} α₂ _inst_2) (fun (a₂ : α₂) => g a₂)))
but is expected to have type
  forall {α₁ : Type.{u2}} {α₂ : Type.{u1}} {M : Type.{u3}} [_inst_1 : Fintype.{u2} α₁] [_inst_2 : Fintype.{u1} α₂] [_inst_3 : CommMonoid.{u3} M] (f : α₁ -> M) (g : α₂ -> M), Eq.{succ u3} M (Finset.prod.{u3, max u2 u1} M (Sum.{u2, u1} α₁ α₂) _inst_3 (Finset.univ.{max u2 u1} (Sum.{u2, u1} α₁ α₂) (instFintypeSum.{u2, u1} α₁ α₂ _inst_1 _inst_2)) (fun (x : Sum.{u2, u1} α₁ α₂) => Sum.elim.{u2, u1, succ u3} α₁ α₂ M f g x)) (HMul.hMul.{u3, u3, u3} M M M (instHMul.{u3} M (MulOneClass.toMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))) (Finset.prod.{u3, u2} M α₁ _inst_3 (Finset.univ.{u2} α₁ _inst_1) (fun (a₁ : α₁) => f a₁)) (Finset.prod.{u3, u1} M α₂ _inst_3 (Finset.univ.{u1} α₂ _inst_2) (fun (a₂ : α₂) => g a₂)))
Case conversion may be inaccurate. Consider using '#align fintype.prod_sum_elim Fintype.prod_sum_elimₓ'. -/
@[to_additive]
theorem Fintype.prod_sum_elim (f : α₁ → M) (g : α₂ → M) :
    (∏ x, Sum.elim f g x) = (∏ a₁, f a₁) * ∏ a₂, g a₂ :=
  prod_disj_sum _ _ _
#align fintype.prod_sum_elim Fintype.prod_sum_elim
#align fintype.sum_sum_elim Fintype.sum_sum_elim

/- warning: fintype.prod_sum_type -> Fintype.prod_sum_type is a dubious translation:
lean 3 declaration is
  forall {α₁ : Type.{u1}} {α₂ : Type.{u2}} {M : Type.{u3}} [_inst_1 : Fintype.{u1} α₁] [_inst_2 : Fintype.{u2} α₂] [_inst_3 : CommMonoid.{u3} M] (f : (Sum.{u1, u2} α₁ α₂) -> M), Eq.{succ u3} M (Finset.prod.{u3, max u1 u2} M (Sum.{u1, u2} α₁ α₂) _inst_3 (Finset.univ.{max u1 u2} (Sum.{u1, u2} α₁ α₂) (Sum.fintype.{u1, u2} α₁ α₂ _inst_1 _inst_2)) (fun (x : Sum.{u1, u2} α₁ α₂) => f x)) (HMul.hMul.{u3, u3, u3} M M M (instHMul.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))) (Finset.prod.{u3, u1} M α₁ _inst_3 (Finset.univ.{u1} α₁ _inst_1) (fun (a₁ : α₁) => f (Sum.inl.{u1, u2} α₁ α₂ a₁))) (Finset.prod.{u3, u2} M α₂ _inst_3 (Finset.univ.{u2} α₂ _inst_2) (fun (a₂ : α₂) => f (Sum.inr.{u1, u2} α₁ α₂ a₂))))
but is expected to have type
  forall {α₁ : Type.{u3}} {α₂ : Type.{u2}} {M : Type.{u1}} [_inst_1 : Fintype.{u3} α₁] [_inst_2 : Fintype.{u2} α₂] [_inst_3 : CommMonoid.{u1} M] (f : (Sum.{u3, u2} α₁ α₂) -> M), Eq.{succ u1} M (Finset.prod.{u1, max u3 u2} M (Sum.{u3, u2} α₁ α₂) _inst_3 (Finset.univ.{max u3 u2} (Sum.{u3, u2} α₁ α₂) (instFintypeSum.{u3, u2} α₁ α₂ _inst_1 _inst_2)) (fun (x : Sum.{u3, u2} α₁ α₂) => f x)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))) (Finset.prod.{u1, u3} M α₁ _inst_3 (Finset.univ.{u3} α₁ _inst_1) (fun (a₁ : α₁) => f (Sum.inl.{u3, u2} α₁ α₂ a₁))) (Finset.prod.{u1, u2} M α₂ _inst_3 (Finset.univ.{u2} α₂ _inst_2) (fun (a₂ : α₂) => f (Sum.inr.{u3, u2} α₁ α₂ a₂))))
Case conversion may be inaccurate. Consider using '#align fintype.prod_sum_type Fintype.prod_sum_typeₓ'. -/
@[simp, to_additive]
theorem Fintype.prod_sum_type (f : Sum α₁ α₂ → M) :
    (∏ x, f x) = (∏ a₁, f (Sum.inl a₁)) * ∏ a₂, f (Sum.inr a₂) :=
  prod_disj_sum _ _ _
#align fintype.prod_sum_type Fintype.prod_sum_type
#align fintype.sum_sum_type Fintype.sum_sum_type

end

