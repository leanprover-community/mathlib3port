/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies

! This file was ported from Lean 3 source module data.finset.pointwise
! leanprover-community/mathlib commit f16e7a22e11fc09c71f25446ac1db23a24e8a0bd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.NAry
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.Data.Set.Pointwise.ListOfFn

/-!
# Pointwise operations of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`finset.has_zero`): The singleton `{0}`.
* `1` (`finset.has_one`): The singleton `{1}`.
* `-s` (`finset.has_neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`finset.has_inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`finset.has_add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`finset.has_mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`finset.has_sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`finset.has_div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t` (`finset.has_vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`finset.has_smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`finset.has_vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`finset.has_smul_finset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`finset.has_vadd_finset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the locale `pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


open Function

open BigOperators Pointwise

variable {F α β γ : Type _}

namespace Finset

/-! ### `0`/`1` as finsets -/


section One

variable [One α] {s : Finset α} {a : α}

#print Finset.one /-
/-- The finset `1 : finset α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The finset `0 : finset α` is defined as `{0}` in locale `pointwise`."]
protected def one : One (Finset α) :=
  ⟨{1}⟩
#align finset.has_one Finset.one
#align finset.has_zero Finset.zero
-/

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

#print Finset.mem_one /-
@[simp, to_additive]
theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 :=
  mem_singleton
#align finset.mem_one Finset.mem_one
#align finset.mem_zero Finset.mem_zero
-/

#print Finset.coe_one /-
@[simp, norm_cast, to_additive]
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1
#align finset.coe_one Finset.coe_one
#align finset.coe_zero Finset.coe_zero
-/

#print Finset.one_subset /-
@[simp, to_additive]
theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align finset.one_subset Finset.one_subset
#align finset.zero_subset Finset.zero_subset
-/

#print Finset.singleton_one /-
@[to_additive]
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl
#align finset.singleton_one Finset.singleton_one
#align finset.singleton_zero Finset.singleton_zero
-/

#print Finset.one_mem_one /-
@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Finset α) :=
  mem_singleton_self _
#align finset.one_mem_one Finset.one_mem_one
#align finset.zero_mem_zero Finset.zero_mem_zero
-/

#print Finset.one_nonempty /-
@[to_additive]
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩
#align finset.one_nonempty Finset.one_nonempty
#align finset.zero_nonempty Finset.zero_nonempty
-/

/- warning: finset.map_one -> Finset.map_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u1} α] {f : Function.Embedding.{succ u1, succ u2} α β}, Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α _inst_1))))) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u2} α] {f : Function.Embedding.{succ u2, succ u1} α β}, Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (OfNat.ofNat.{u2} (Finset.{u2} α) 1 (One.toOfNat1.{u2} (Finset.{u2} α) (Finset.one.{u2} α _inst_1)))) (Singleton.singleton.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1))) (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f (OfNat.ofNat.{u2} α 1 (One.toOfNat1.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align finset.map_one Finset.map_oneₓ'. -/
@[simp, to_additive]
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1
#align finset.map_one Finset.map_one
#align finset.map_zero Finset.map_zero

#print Finset.image_one /-
@[simp, to_additive]
theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} :=
  image_singleton _ _
#align finset.image_one Finset.image_one
#align finset.image_zero Finset.image_zero
-/

#print Finset.subset_one_iff_eq /-
@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff
#align finset.subset_one_iff_eq Finset.subset_one_iff_eq
#align finset.subset_zero_iff_eq Finset.subset_zero_iff_eq
-/

#print Finset.Nonempty.subset_one_iff /-
@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align finset.nonempty.subset_one_iff Finset.Nonempty.subset_one_iff
#align finset.nonempty.subset_zero_iff Finset.Nonempty.subset_zero_iff
-/

#print Finset.singletonOneHom /-
/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singletonOneHom : OneHom α (Finset α) :=
  ⟨singleton, singleton_one⟩
#align finset.singleton_one_hom Finset.singletonOneHom
#align finset.singleton_zero_hom Finset.singletonZeroHom
-/

#print Finset.coe_singletonOneHom /-
@[simp, to_additive]
theorem coe_singletonOneHom : (singletonOneHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_one_hom Finset.coe_singletonOneHom
#align finset.coe_singleton_zero_hom Finset.coe_singletonZeroHom
-/

#print Finset.singletonOneHom_apply /-
@[simp, to_additive]
theorem singletonOneHom_apply (a : α) : singletonOneHom a = {a} :=
  rfl
#align finset.singleton_one_hom_apply Finset.singletonOneHom_apply
#align finset.singleton_zero_hom_apply Finset.singletonZeroHom_apply
-/

#print Finset.imageOneHom /-
/-- Lift a `one_hom` to `finset` via `image`. -/
@[to_additive "Lift a `zero_hom` to `finset` via `image`", simps]
def imageOneHom [DecidableEq β] [One β] [OneHomClass F α β] (f : F) : OneHom (Finset α) (Finset β)
    where
  toFun := Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]
#align finset.image_one_hom Finset.imageOneHom
#align finset.image_zero_hom Finset.imageZeroHom
-/

end One

/-! ### Finset negation/inversion -/


section Inv

variable [DecidableEq α] [Inv α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

#print Finset.inv /-
/-- The pointwise inversion of finset `s⁻¹` is defined as `{x⁻¹ | x ∈ s}` in locale `pointwise`. -/
@[to_additive
      "The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in locale\n`pointwise`."]
protected def inv : Inv (Finset α) :=
  ⟨image Inv.inv⟩
#align finset.has_inv Finset.inv
#align finset.has_neg Finset.neg
-/

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

#print Finset.inv_def /-
@[to_additive]
theorem inv_def : s⁻¹ = s.image fun x => x⁻¹ :=
  rfl
#align finset.inv_def Finset.inv_def
#align finset.neg_def Finset.neg_def
-/

#print Finset.image_inv /-
@[to_additive]
theorem image_inv : (s.image fun x => x⁻¹) = s⁻¹ :=
  rfl
#align finset.image_inv Finset.image_inv
#align finset.image_neg Finset.image_neg
-/

/- warning: finset.mem_inv -> Finset.mem_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Inv.{u1} α] {s : Finset.{u1} α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s)) (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) y s) => Eq.{succ u1} α (Inv.inv.{u1} α _inst_2 y) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Inv.{u1} α] {s : Finset.{u1} α} {x : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s)) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) y s) (Eq.{succ u1} α (Inv.inv.{u1} α _inst_2 y) x)))
Case conversion may be inaccurate. Consider using '#align finset.mem_inv Finset.mem_invₓ'. -/
@[to_additive]
theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x :=
  mem_image
#align finset.mem_inv Finset.mem_inv
#align finset.mem_neg Finset.mem_neg

#print Finset.inv_mem_inv /-
@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  mem_image_of_mem _ ha
#align finset.inv_mem_inv Finset.inv_mem_inv
#align finset.neg_mem_neg Finset.neg_mem_neg
-/

#print Finset.card_inv_le /-
@[to_additive]
theorem card_inv_le : s⁻¹.card ≤ s.card :=
  card_image_le
#align finset.card_inv_le Finset.card_inv_le
#align finset.card_neg_le Finset.card_neg_le
-/

#print Finset.inv_empty /-
@[simp, to_additive]
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  image_empty _
#align finset.inv_empty Finset.inv_empty
#align finset.neg_empty Finset.neg_empty
-/

#print Finset.inv_nonempty_iff /-
@[simp, to_additive]
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty :=
  Nonempty.image_iff _
#align finset.inv_nonempty_iff Finset.inv_nonempty_iff
#align finset.neg_nonempty_iff Finset.neg_nonempty_iff
-/

alias inv_nonempty_iff ↔ nonempty.inv nonempty.of_inv
#align finset.nonempty.inv Finset.nonempty.inv
#align finset.nonempty.of_inv Finset.nonempty.of_inv

#print Finset.inv_subset_inv /-
@[to_additive, mono]
theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ :=
  image_subset_image h
#align finset.inv_subset_inv Finset.inv_subset_inv
#align finset.neg_subset_neg Finset.neg_subset_neg
-/

attribute [mono] neg_subset_neg

#print Finset.inv_singleton /-
@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _
#align finset.inv_singleton Finset.inv_singleton
#align finset.neg_singleton Finset.neg_singleton
-/

#print Finset.inv_insert /-
@[simp, to_additive]
theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
  image_insert _ _ _
#align finset.inv_insert Finset.inv_insert
#align finset.neg_insert Finset.neg_insert
-/

end Inv

open Pointwise

section InvolutiveInv

variable [DecidableEq α] [InvolutiveInv α] (s : Finset α)

/- warning: finset.coe_inv -> Finset.coe_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : InvolutiveInv.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvolutiveInv.toHasInv.{u1} α _inst_2)) s)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : InvolutiveInv.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvolutiveInv.toInv.{u1} α _inst_2)) s)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_2)) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.coe_inv Finset.coe_invₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_inv : ↑s⁻¹ = (s : Set α)⁻¹ :=
  coe_image.trans Set.image_inv
#align finset.coe_inv Finset.coe_inv
#align finset.coe_neg Finset.coe_neg

/- warning: finset.card_inv -> Finset.card_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : InvolutiveInv.{u1} α] (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvolutiveInv.toHasInv.{u1} α _inst_2)) s)) (Finset.card.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : InvolutiveInv.{u1} α] (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvolutiveInv.toInv.{u1} α _inst_2)) s)) (Finset.card.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.card_inv Finset.card_invₓ'. -/
@[simp, to_additive]
theorem card_inv : s⁻¹.card = s.card :=
  card_image_of_injective _ inv_injective
#align finset.card_inv Finset.card_inv
#align finset.card_neg Finset.card_neg

/- warning: finset.preimage_inv -> Finset.preimage_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : InvolutiveInv.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α s (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_2)) (Function.Injective.injOn.{u1, u1} α α (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_2)) (inv_injective.{u1} α _inst_2) (Set.preimage.{u1, u1} α α (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))) (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvolutiveInv.toHasInv.{u1} α _inst_2)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : InvolutiveInv.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α s (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_2)) (Function.Injective.injOn.{u1, u1} α α (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_2)) (inv_injective.{u1} α _inst_2) (Set.preimage.{u1, u1} α α (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_2)) (Finset.toSet.{u1} α s)))) (Inv.inv.{u1} (Finset.{u1} α) (Finset.inv.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvolutiveInv.toInv.{u1} α _inst_2)) s)
Case conversion may be inaccurate. Consider using '#align finset.preimage_inv Finset.preimage_invₓ'. -/
@[simp, to_additive]
theorem preimage_inv : s.Preimage Inv.inv (inv_injective.InjOn _) = s⁻¹ :=
  coe_injective <| by rw [coe_preimage, Set.inv_preimage, coe_inv]
#align finset.preimage_inv Finset.preimage_inv
#align finset.preimage_neg Finset.preimage_neg

end InvolutiveInv

/-! ### Finset addition/multiplication -/


section Mul

variable [DecidableEq α] [DecidableEq β] [Mul α] [Mul β] [MulHomClass F α β] (f : F)
  {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

#print Finset.mul /-
/-- The pointwise multiplication of finsets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}`
in locale `pointwise`. -/
@[to_additive
      "The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def mul : Mul (Finset α) :=
  ⟨image₂ (· * ·)⟩
#align finset.has_mul Finset.mul
#align finset.has_add Finset.add
-/

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.mul_def /-
@[to_additive]
theorem mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2 :=
  rfl
#align finset.mul_def Finset.mul_def
#align finset.add_def Finset.add_def
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.image_mul_product /-
@[to_additive]
theorem image_mul_product : ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * t :=
  rfl
#align finset.image_mul_product Finset.image_mul_product
#align finset.image_add_product Finset.image_add_product
-/

#print Finset.mem_mul /-
@[to_additive]
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
  mem_image₂
#align finset.mem_mul Finset.mem_mul
#align finset.mem_add Finset.mem_add
-/

#print Finset.coe_mul /-
@[simp, norm_cast, to_additive]
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  coe_image₂ _ _ _
#align finset.coe_mul Finset.coe_mul
#align finset.coe_add Finset.coe_add
-/

#print Finset.mul_mem_mul /-
@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image₂_of_mem
#align finset.mul_mem_mul Finset.mul_mem_mul
#align finset.add_mem_add Finset.add_mem_add
-/

#print Finset.card_mul_le /-
@[to_additive]
theorem card_mul_le : (s * t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.card_mul_le Finset.card_mul_le
#align finset.card_add_le Finset.card_add_le
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.card_mul_iff /-
@[to_additive]
theorem card_mul_iff :
    (s * t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff
#align finset.card_mul_iff Finset.card_mul_iff
#align finset.card_add_iff Finset.card_add_iff
-/

#print Finset.empty_mul /-
@[simp, to_additive]
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  image₂_empty_left
#align finset.empty_mul Finset.empty_mul
#align finset.empty_add Finset.empty_add
-/

#print Finset.mul_empty /-
@[simp, to_additive]
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  image₂_empty_right
#align finset.mul_empty Finset.mul_empty
#align finset.add_empty Finset.add_empty
-/

#print Finset.mul_eq_empty /-
@[simp, to_additive]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.mul_eq_empty Finset.mul_eq_empty
#align finset.add_eq_empty Finset.add_eq_empty
-/

#print Finset.mul_nonempty /-
@[simp, to_additive]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.mul_nonempty Finset.mul_nonempty
#align finset.add_nonempty Finset.add_nonempty
-/

#print Finset.Nonempty.mul /-
@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.mul Finset.Nonempty.mul
#align finset.nonempty.add Finset.Nonempty.add
-/

#print Finset.Nonempty.of_mul_left /-
@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_mul_left Finset.Nonempty.of_mul_left
#align finset.nonempty.of_add_left Finset.Nonempty.of_add_left
-/

#print Finset.Nonempty.of_mul_right /-
@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_mul_right Finset.Nonempty.of_mul_right
#align finset.nonempty.of_add_right Finset.Nonempty.of_add_right
-/

#print Finset.mul_singleton /-
@[to_additive]
theorem mul_singleton (a : α) : s * {a} = s.image (· * a) :=
  image₂_singleton_right
#align finset.mul_singleton Finset.mul_singleton
#align finset.add_singleton Finset.add_singleton
-/

#print Finset.singleton_mul /-
@[to_additive]
theorem singleton_mul (a : α) : {a} * s = s.image ((· * ·) a) :=
  image₂_singleton_left
#align finset.singleton_mul Finset.singleton_mul
#align finset.singleton_add Finset.singleton_add
-/

#print Finset.singleton_mul_singleton /-
@[simp, to_additive]
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} :=
  image₂_singleton
#align finset.singleton_mul_singleton Finset.singleton_mul_singleton
#align finset.singleton_add_singleton Finset.singleton_add_singleton
-/

#print Finset.mul_subset_mul /-
@[to_additive, mono]
theorem mul_subset_mul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ * t₁ ⊆ s₂ * t₂ :=
  image₂_subset
#align finset.mul_subset_mul Finset.mul_subset_mul
#align finset.add_subset_add Finset.add_subset_add
-/

#print Finset.mul_subset_mul_left /-
@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image₂_subset_left
#align finset.mul_subset_mul_left Finset.mul_subset_mul_left
#align finset.add_subset_add_left Finset.add_subset_add_left
-/

#print Finset.mul_subset_mul_right /-
@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image₂_subset_right
#align finset.mul_subset_mul_right Finset.mul_subset_mul_right
#align finset.add_subset_add_right Finset.add_subset_add_right
-/

#print Finset.mul_subset_iff /-
@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image₂_subset_iff
#align finset.mul_subset_iff Finset.mul_subset_iff
#align finset.add_subset_iff Finset.add_subset_iff
-/

attribute [mono] add_subset_add

#print Finset.union_mul /-
@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image₂_union_left
#align finset.union_mul Finset.union_mul
#align finset.union_add Finset.union_add
-/

#print Finset.mul_union /-
@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image₂_union_right
#align finset.mul_union Finset.mul_union
#align finset.add_union Finset.add_union
-/

#print Finset.inter_mul_subset /-
@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image₂_inter_subset_left
#align finset.inter_mul_subset Finset.inter_mul_subset
#align finset.inter_add_subset Finset.inter_add_subset
-/

#print Finset.mul_inter_subset /-
@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image₂_inter_subset_right
#align finset.mul_inter_subset Finset.mul_inter_subset
#align finset.add_inter_subset Finset.add_inter_subset
-/

#print Finset.subset_mul /-
/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets\n`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`."]
theorem subset_mul {s t : Set α} :
    ↑u ⊆ s * t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' :=
  subset_image₂
#align finset.subset_mul Finset.subset_mul
#align finset.subset_add Finset.subset_add
-/

#print Finset.image_mul /-
@[to_additive]
theorem image_mul : (s * t).image (f : α → β) = s.image f * t.image f :=
  image_image₂_distrib <| map_mul f
#align finset.image_mul Finset.image_mul
#align finset.image_add Finset.image_add
-/

#print Finset.singletonMulHom /-
/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singletonMulHom : α →ₙ* Finset α :=
  ⟨singleton, fun a b => (singleton_mul_singleton _ _).symm⟩
#align finset.singleton_mul_hom Finset.singletonMulHom
#align finset.singleton_add_hom Finset.singletonAddHom
-/

#print Finset.coe_singletonMulHom /-
@[simp, to_additive]
theorem coe_singletonMulHom : (singletonMulHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_mul_hom Finset.coe_singletonMulHom
#align finset.coe_singleton_add_hom Finset.coe_singletonAddHom
-/

#print Finset.singletonMulHom_apply /-
@[simp, to_additive]
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align finset.singleton_mul_hom_apply Finset.singletonMulHom_apply
#align finset.singleton_add_hom_apply Finset.singletonAddHom_apply
-/

#print Finset.imageMulHom /-
/-- Lift a `mul_hom` to `finset` via `image`. -/
@[to_additive "Lift an `add_hom` to `finset` via `image`", simps]
def imageMulHom : Finset α →ₙ* Finset β
    where
  toFun := Finset.image f
  map_mul' s t := image_mul _
#align finset.image_mul_hom Finset.imageMulHom
#align finset.image_add_hom Finset.imageAddHom
-/

end Mul

/-! ### Finset subtraction/division -/


section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

#print Finset.div /-
/-- The pointwise division of sfinets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive
      "The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`\nin locale `pointwise`."]
protected def div : Div (Finset α) :=
  ⟨image₂ (· / ·)⟩
#align finset.has_div Finset.div
#align finset.has_sub Finset.sub
-/

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.div_def /-
@[to_additive]
theorem div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2 :=
  rfl
#align finset.div_def Finset.div_def
#align finset.sub_def Finset.sub_def
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.image_div_prod /-
@[to_additive add_image_prod]
theorem image_div_prod : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t :=
  rfl
#align finset.image_div_prod Finset.image_div_prod
#align finset.add_image_prod Finset.add_image_prod
-/

#print Finset.mem_div /-
@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b / c = a :=
  mem_image₂
#align finset.mem_div Finset.mem_div
#align finset.mem_sub Finset.mem_sub
-/

#print Finset.coe_div /-
@[simp, norm_cast, to_additive]
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  coe_image₂ _ _ _
#align finset.coe_div Finset.coe_div
#align finset.coe_sub Finset.coe_sub
-/

#print Finset.div_mem_div /-
@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image₂_of_mem
#align finset.div_mem_div Finset.div_mem_div
#align finset.sub_mem_sub Finset.sub_mem_sub
-/

#print Finset.div_card_le /-
@[to_additive]
theorem div_card_le : (s / t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.div_card_le Finset.div_card_le
#align finset.sub_card_le Finset.sub_card_le
-/

#print Finset.empty_div /-
@[simp, to_additive]
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  image₂_empty_left
#align finset.empty_div Finset.empty_div
#align finset.empty_sub Finset.empty_sub
-/

#print Finset.div_empty /-
@[simp, to_additive]
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  image₂_empty_right
#align finset.div_empty Finset.div_empty
#align finset.sub_empty Finset.sub_empty
-/

#print Finset.div_eq_empty /-
@[simp, to_additive]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.div_eq_empty Finset.div_eq_empty
#align finset.sub_eq_empty Finset.sub_eq_empty
-/

#print Finset.div_nonempty /-
@[simp, to_additive]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.div_nonempty Finset.div_nonempty
#align finset.sub_nonempty Finset.sub_nonempty
-/

#print Finset.Nonempty.div /-
@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.div Finset.Nonempty.div
#align finset.nonempty.sub Finset.Nonempty.sub
-/

#print Finset.Nonempty.of_div_left /-
@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_div_left Finset.Nonempty.of_div_left
#align finset.nonempty.of_sub_left Finset.Nonempty.of_sub_left
-/

#print Finset.Nonempty.of_div_right /-
@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_div_right Finset.Nonempty.of_div_right
#align finset.nonempty.of_sub_right Finset.Nonempty.of_sub_right
-/

#print Finset.div_singleton /-
@[simp, to_additive]
theorem div_singleton (a : α) : s / {a} = s.image (· / a) :=
  image₂_singleton_right
#align finset.div_singleton Finset.div_singleton
#align finset.sub_singleton Finset.sub_singleton
-/

#print Finset.singleton_div /-
@[simp, to_additive]
theorem singleton_div (a : α) : {a} / s = s.image ((· / ·) a) :=
  image₂_singleton_left
#align finset.singleton_div Finset.singleton_div
#align finset.singleton_sub Finset.singleton_sub
-/

#print Finset.singleton_div_singleton /-
@[simp, to_additive]
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} :=
  image₂_singleton
#align finset.singleton_div_singleton Finset.singleton_div_singleton
#align finset.singleton_sub_singleton Finset.singleton_sub_singleton
-/

#print Finset.div_subset_div /-
@[to_additive, mono]
theorem div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ :=
  image₂_subset
#align finset.div_subset_div Finset.div_subset_div
#align finset.sub_subset_sub Finset.sub_subset_sub
-/

#print Finset.div_subset_div_left /-
@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image₂_subset_left
#align finset.div_subset_div_left Finset.div_subset_div_left
#align finset.sub_subset_sub_left Finset.sub_subset_sub_left
-/

#print Finset.div_subset_div_right /-
@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image₂_subset_right
#align finset.div_subset_div_right Finset.div_subset_div_right
#align finset.sub_subset_sub_right Finset.sub_subset_sub_right
-/

#print Finset.div_subset_iff /-
@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image₂_subset_iff
#align finset.div_subset_iff Finset.div_subset_iff
#align finset.sub_subset_iff Finset.sub_subset_iff
-/

attribute [mono] sub_subset_sub

#print Finset.union_div /-
@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image₂_union_left
#align finset.union_div Finset.union_div
#align finset.union_sub Finset.union_sub
-/

#print Finset.div_union /-
@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image₂_union_right
#align finset.div_union Finset.div_union
#align finset.sub_union Finset.sub_union
-/

#print Finset.inter_div_subset /-
@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image₂_inter_subset_left
#align finset.inter_div_subset Finset.inter_div_subset
#align finset.inter_sub_subset Finset.inter_sub_subset
-/

#print Finset.div_inter_subset /-
@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image₂_inter_subset_right
#align finset.div_inter_subset Finset.div_inter_subset
#align finset.sub_inter_subset Finset.sub_inter_subset
-/

#print Finset.subset_div /-
/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive
      "If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets\n`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`."]
theorem subset_div {s t : Set α} :
    ↑u ⊆ s / t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' :=
  subset_image₂
#align finset.subset_div Finset.subset_div
#align finset.subset_sub Finset.subset_sub
-/

end Div

/-! ### Instances -/


open Pointwise

section Instances

variable [DecidableEq α] [DecidableEq β]

#print Finset.nsmul /-
/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action]. -/
protected def nsmul [Zero α] [Add α] : SMul ℕ (Finset α) :=
  ⟨nsmulRec⟩
#align finset.has_nsmul Finset.nsmul
-/

#print Finset.npow /-
/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`finset`. See note [pointwise nat action]. -/
@[to_additive]
protected def npow [One α] [Mul α] : Pow (Finset α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align finset.has_npow Finset.npow
#align finset.has_nsmul Finset.nsmul
-/

#print Finset.zsmul /-
/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `finset`. See note [pointwise nat action]. -/
protected def zsmul [Zero α] [Add α] [Neg α] : SMul ℤ (Finset α) :=
  ⟨zsmulRec⟩
#align finset.has_zsmul Finset.zsmul
-/

#print Finset.zpow /-
/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `finset`. See note [pointwise nat action]. -/
@[to_additive]
protected def zpow [One α] [Mul α] [Inv α] : Pow (Finset α) ℤ :=
  ⟨fun s n => zpowRec n s⟩
#align finset.has_zpow Finset.zpow
#align finset.has_zsmul Finset.zsmul
-/

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

#print Finset.semigroup /-
/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_semigroup` under pointwise operations if `α` is. "]
protected def semigroup [Semigroup α] : Semigroup (Finset α) :=
  coe_injective.Semigroup _ coe_mul
#align finset.semigroup Finset.semigroup
#align finset.add_semigroup Finset.addSemigroup
-/

#print Finset.commSemigroup /-
/-- `finset α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_semigroup` under pointwise operations if `α` is. "]
protected def commSemigroup [CommSemigroup α] : CommSemigroup (Finset α) :=
  coe_injective.CommSemigroup _ coe_mul
#align finset.comm_semigroup Finset.commSemigroup
#align finset.add_comm_semigroup Finset.addCommSemigroup
-/

section MulOneClass

variable [MulOneClass α]

#print Finset.mulOneClass /-
/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Finset α) :=
  coe_injective.MulOneClass _ (coe_singleton 1) coe_mul
#align finset.mul_one_class Finset.mulOneClass
#align finset.add_zero_class Finset.addZeroClass
-/

scoped[Pointwise]
  attribute [instance]
    Finset.semigroup Finset.addSemigroup Finset.commSemigroup Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

/- warning: finset.subset_mul_left -> Finset.subset_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] (s : Finset.{u1} α) {t : Finset.{u1} α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_3)))) t) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α _inst_3))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] (s : Finset.{u1} α) {t : Finset.{u1} α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_3))) t) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α _inst_3))) s t))
Case conversion may be inaccurate. Consider using '#align finset.subset_mul_left Finset.subset_mul_leftₓ'. -/
@[to_additive]
theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨a, 1, ha, ht, mul_one _⟩
#align finset.subset_mul_left Finset.subset_mul_left
#align finset.subset_add_left Finset.subset_add_left

/- warning: finset.subset_mul_right -> Finset.subset_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] {s : Finset.{u1} α} (t : Finset.{u1} α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_3)))) s) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α _inst_3))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] {s : Finset.{u1} α} (t : Finset.{u1} α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_3))) s) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) t (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α _inst_3))) s t))
Case conversion may be inaccurate. Consider using '#align finset.subset_mul_right Finset.subset_mul_rightₓ'. -/
@[to_additive]
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨1, a, hs, ha, one_mul _⟩
#align finset.subset_mul_right Finset.subset_mul_right
#align finset.subset_add_right Finset.subset_add_right

#print Finset.singletonMonoidHom /-
/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singletonMonoidHom : α →* Finset α :=
  { singletonMulHom, singletonOneHom with }
#align finset.singleton_monoid_hom Finset.singletonMonoidHom
#align finset.singleton_add_monoid_hom Finset.singletonAddMonoidHom
-/

/- warning: finset.coe_singleton_monoid_hom -> Finset.coe_singletonMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α], Eq.{succ u1} ((fun (_x : MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) => α -> (Finset.{u1} α)) (Finset.singletonMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (fun (_x : MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) => α -> (Finset.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (Finset.singletonMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α], Eq.{succ u1} (forall (a : α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Finset.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Finset.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) α (Finset.{u1} α) (MulOneClass.toMul.{u1} α _inst_3) (MulOneClass.toMul.{u1} (Finset.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (MonoidHom.monoidHomClass.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)))) (Finset.singletonMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.coe_singleton_monoid_hom Finset.coe_singletonMonoidHomₓ'. -/
@[simp, to_additive]
theorem coe_singletonMonoidHom : (singletonMonoidHom : α → Finset α) = singleton :=
  rfl
#align finset.coe_singleton_monoid_hom Finset.coe_singletonMonoidHom
#align finset.coe_singleton_add_monoid_hom Finset.coe_singletonAddMonoidHom

/- warning: finset.singleton_monoid_hom_apply -> Finset.singletonMonoidHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] (a : α), Eq.{succ u1} (Finset.{u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (fun (_x : MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) => α -> (Finset.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (Finset.singletonMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Finset.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Finset.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) α (Finset.{u1} α) (MulOneClass.toMul.{u1} α _inst_3) (MulOneClass.toMul.{u1} (Finset.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (MonoidHom.monoidHomClass.{u1, u1} α (Finset.{u1} α) _inst_3 (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)))) (Finset.singletonMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) a) (Singleton.singleton.{u1, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => Finset.{u1} α) a) (Finset.instSingletonFinset.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align finset.singleton_monoid_hom_apply Finset.singletonMonoidHom_applyₓ'. -/
@[simp, to_additive]
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align finset.singleton_monoid_hom_apply Finset.singletonMonoidHom_apply
#align finset.singleton_add_monoid_hom_apply Finset.singletonAddMonoidHom_apply

#print Finset.coeMonoidHom /-
/-- The coercion from `finset` to `set` as a `monoid_hom`. -/
@[to_additive "The coercion from `finset` to `set` as an `add_monoid_hom`."]
def coeMonoidHom : Finset α →* Set α where
  toFun := coe
  map_one' := coe_one
  map_mul' := coe_mul
#align finset.coe_monoid_hom Finset.coeMonoidHom
#align finset.coe_add_monoid_hom Finset.coeAddMonoidHom
-/

/- warning: finset.coe_coe_monoid_hom -> Finset.coe_coeMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α], Eq.{succ u1} ((fun (_x : MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) => (Finset.{u1} α) -> (Set.{u1} α)) (Finset.coeMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (fun (_x : MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) => (Finset.{u1} α) -> (Set.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.coeMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α], Eq.{succ u1} (forall (a : Finset.{u1} α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Finset.{u1} α) => Set.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Finset.{u1} α) => Set.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.{u1} α) (Set.{u1} α) (MulOneClass.toMul.{u1} (Finset.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (MulOneClass.toMul.{u1} (Set.{u1} α) (Set.mulOneClass.{u1} α _inst_3)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3) (MonoidHom.monoidHomClass.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)))) (Finset.coeMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (CoeTC.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.instCoeTCFinsetSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.coe_coe_monoid_hom Finset.coe_coeMonoidHomₓ'. -/
@[simp, to_additive]
theorem coe_coeMonoidHom : (coeMonoidHom : Finset α → Set α) = coe :=
  rfl
#align finset.coe_coe_monoid_hom Finset.coe_coeMonoidHom
#align finset.coe_coe_add_monoid_hom Finset.coe_coeAddMonoidHom

/- warning: finset.coe_monoid_hom_apply -> Finset.coeMonoidHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (fun (_x : MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) => (Finset.{u1} α) -> (Set.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.coeMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulOneClass.{u1} α] (s : Finset.{u1} α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Finset.{u1} α) => Set.{u1} α) s) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Finset.{u1} α) => Set.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.{u1} α) (Set.{u1} α) (MulOneClass.toMul.{u1} (Finset.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3)) (MulOneClass.toMul.{u1} (Set.{u1} α) (Set.mulOneClass.{u1} α _inst_3)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)) (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3) (MonoidHom.monoidHomClass.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.mulOneClass.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) (Set.mulOneClass.{u1} α _inst_3)))) (Finset.coeMonoidHom.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_3) s) (Finset.toSet.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.coe_monoid_hom_apply Finset.coeMonoidHom_applyₓ'. -/
@[simp, to_additive]
theorem coeMonoidHom_apply (s : Finset α) : coeMonoidHom s = s :=
  rfl
#align finset.coe_monoid_hom_apply Finset.coeMonoidHom_apply
#align finset.coe_add_monoid_hom_apply Finset.coeAddMonoidHom_apply

#print Finset.imageMonoidHom /-
/-- Lift a `monoid_hom` to `finset` via `image`. -/
@[to_additive "Lift an `add_monoid_hom` to `finset` via `image`", simps]
def imageMonoidHom [MulOneClass β] [MonoidHomClass F α β] (f : F) : Finset α →* Finset β :=
  { imageMulHom f, imageOneHom f with }
#align finset.image_monoid_hom Finset.imageMonoidHom
#align finset.image_add_monoid_hom Finset.imageAddMonoidHom
-/

end MulOneClass

section Monoid

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

/- warning: finset.coe_pow -> Finset.coe_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] (s : Finset.{u1} α) (n : Nat), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n)) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] (s : Finset.{u1} α) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n)) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.toSet.{u1} α s) n)
Case conversion may be inaccurate. Consider using '#align finset.coe_pow Finset.coe_powₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s ^ n : Set α) :=
  by
  change ↑(npowRec n s) = _
  induction' n with n ih
  · rw [npowRec, pow_zero, coe_one]
  · rw [npowRec, pow_succ, coe_mul, ih]
#align finset.coe_pow Finset.coe_pow
#align finset.coe_nsmul Finset.coe_nsmul

#print Finset.monoid /-
/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_monoid` under pointwise operations if `α` is. "]
protected def monoid : Monoid (Finset α) :=
  coe_injective.Monoid _ coe_one coe_mul coe_pow
#align finset.monoid Finset.monoid
#align finset.add_monoid Finset.addMonoid
-/

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

/- warning: finset.pow_mem_pow -> Finset.pow_mem_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (n : Nat), Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_3)) a n) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (n : Nat), Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_3)) a n) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n))
Case conversion may be inaccurate. Consider using '#align finset.pow_mem_pow Finset.pow_mem_powₓ'. -/
@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_mul ha (pow_mem_pow _)
#align finset.pow_mem_pow Finset.pow_mem_pow
#align finset.nsmul_mem_nsmul Finset.nsmul_mem_nsmul

/- warning: finset.pow_subset_pow -> Finset.pow_subset_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (forall (n : Nat), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) t n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) -> (forall (n : Nat), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) t n))
Case conversion may be inaccurate. Consider using '#align finset.pow_subset_pow Finset.pow_subset_powₓ'. -/
@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zero]
    exact subset.rfl
  | n + 1 => by
    rw [pow_succ]
    exact mul_subset_mul hst (pow_subset_pow _)
#align finset.pow_subset_pow Finset.pow_subset_pow
#align finset.nsmul_subset_nsmul Finset.nsmul_subset_nsmul

/- warning: finset.pow_subset_pow_of_one_mem -> Finset.pow_subset_pow_of_one_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {m : Nat} {n : Nat}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))))) s) -> (LE.le.{0} Nat Nat.hasLe m n) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s m) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {m : Nat} {n : Nat}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_3))) s) -> (LE.le.{0} Nat instLENat m n) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s m) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n))
Case conversion may be inaccurate. Consider using '#align finset.pow_subset_pow_of_one_mem Finset.pow_subset_pow_of_one_memₓ'. -/
@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n :=
  by
  refine' Nat.le_induction _ (fun n h ih => _) _
  · exact subset.rfl
  · rw [pow_succ]
    exact ih.trans (subset_mul_right _ hs)
#align finset.pow_subset_pow_of_one_mem Finset.pow_subset_pow_of_one_mem
#align finset.nsmul_subset_nsmul_of_zero_mem Finset.nsmul_subset_nsmul_of_zero_mem

/- warning: finset.coe_list_prod -> Finset.coe_list_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] (s : List.{u1} (Finset.{u1} α)), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (List.prod.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) s)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (List.map.{u1, u1} (Finset.{u1} α) (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] (s : List.{u1} (Finset.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (List.prod.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (Finset.one.{u1} α (Monoid.toOne.{u1} α _inst_3)) s)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (Set.one.{u1} α (Monoid.toOne.{u1} α _inst_3)) (List.map.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Finset.toSet.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align finset.coe_list_prod Finset.coe_list_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_list_prod (s : List (Finset α)) : (↑s.Prod : Set α) = (s.map coe).Prod :=
  map_list_prod (coeMonoidHom : Finset α →* Set α) _
#align finset.coe_list_prod Finset.coe_list_prod
#align finset.coe_list_sum Finset.coe_list_sum

/- warning: finset.mem_prod_list_of_fn -> Finset.mem_prod_list_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {n : Nat} {a : α} {s : (Fin n) -> (Finset.{u1} α)}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (List.prod.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (List.ofFn.{u1} (Finset.{u1} α) n s))) (Exists.{succ u1} (forall (i : Fin n), coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (s i)) (fun (f : forall (i : Fin n), coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (s i)) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (List.ofFn.{u1} α n (fun (i : Fin n) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (s i)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (s i)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (s i)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (s i)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (s i)))))) (f i)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {n : Nat} {a : α} {s : (Fin n) -> (Finset.{u1} α)}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (List.prod.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))) (Finset.one.{u1} α (Monoid.toOne.{u1} α _inst_3)) (List.ofFn.{u1} (Finset.{u1} α) n s))) (Exists.{succ u1} (forall (i : Fin n), Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (s i))) (fun (f : forall (i : Fin n), Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (s i))) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Monoid.toOne.{u1} α _inst_3) (List.ofFn.{u1} α n (fun (i : Fin n) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (s i)) (f i)))) a))
Case conversion may be inaccurate. Consider using '#align finset.mem_prod_list_of_fn Finset.mem_prod_list_ofFnₓ'. -/
@[to_additive]
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Finset α} :
    a ∈ (List.ofFn s).Prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).Prod = a :=
  by
  rw [← mem_coe, coe_list_prod, List.map_ofFn, Set.mem_prod_list_ofFn]
  rfl
#align finset.mem_prod_list_of_fn Finset.mem_prod_list_ofFn
#align finset.mem_sum_list_of_fn Finset.mem_sum_list_ofFn

/- warning: finset.mem_pow -> Finset.mem_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {a : α} {n : Nat}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n)) (Exists.{succ u1} ((Fin n) -> (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s)) (fun (f : (Fin n) -> (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s)) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (List.ofFn.{u1} α n (fun (i : Fin n) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) (f i)))) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} {a : α} {n : Nat}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s n)) (Exists.{succ u1} ((Fin n) -> (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) (fun (f : (Fin n) -> (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s))) => Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (Monoid.toOne.{u1} α _inst_3) (List.ofFn.{u1} α n (fun (i : Fin n) => Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (f i)))) a))
Case conversion may be inaccurate. Consider using '#align finset.mem_pow Finset.mem_powₓ'. -/
@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => ↑(f i)).Prod = a :=
  by
  simp_rw [← mem_coe, coe_pow, Set.mem_pow]
  rfl
#align finset.mem_pow Finset.mem_pow
#align finset.mem_nsmul Finset.mem_nsmul

/- warning: finset.empty_pow -> Finset.empty_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Finset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) n) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Finset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)) n) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align finset.empty_pow Finset.empty_powₓ'. -/
@[simp, to_additive]
theorem empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ, empty_mul]
#align finset.empty_pow Finset.empty_pow
#align finset.empty_nsmul Finset.empty_nsmul

/- warning: finset.mul_univ_of_one_mem -> Finset.mul_univ_of_one_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} [_inst_4 : Fintype.{u1} α], (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))))) s) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s (Finset.univ.{u1} α _inst_4)) (Finset.univ.{u1} α _inst_4))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {s : Finset.{u1} α} [_inst_4 : Fintype.{u1} α], (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_3))) s) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) s (Finset.univ.{u1} α _inst_4)) (Finset.univ.{u1} α _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.mul_univ_of_one_mem Finset.mul_univ_of_one_memₓ'. -/
@[to_additive]
theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩
#align finset.mul_univ_of_one_mem Finset.mul_univ_of_one_mem
#align finset.add_univ_of_zero_mem Finset.add_univ_of_zero_mem

/- warning: finset.univ_mul_of_one_mem -> Finset.univ_mul_of_one_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {t : Finset.{u1} α} [_inst_4 : Fintype.{u1} α], (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3))))) t) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.univ.{u1} α _inst_4) t) (Finset.univ.{u1} α _inst_4))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {t : Finset.{u1} α} [_inst_4 : Fintype.{u1} α], (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_3))) t) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.univ.{u1} α _inst_4) t) (Finset.univ.{u1} α _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.univ_mul_of_one_mem Finset.univ_mul_of_one_memₓ'. -/
@[to_additive]
theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩
#align finset.univ_mul_of_one_mem Finset.univ_mul_of_one_mem
#align finset.univ_add_of_zero_mem Finset.univ_add_of_zero_mem

/- warning: finset.univ_mul_univ -> Finset.univ_mul_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] [_inst_4 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.univ.{u1} α _inst_4) (Finset.univ.{u1} α _inst_4)) (Finset.univ.{u1} α _inst_4)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] [_inst_4 : Fintype.{u1} α], Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.univ.{u1} α _inst_4) (Finset.univ.{u1} α _inst_4)) (Finset.univ.{u1} α _inst_4)
Case conversion may be inaccurate. Consider using '#align finset.univ_mul_univ Finset.univ_mul_univₓ'. -/
@[simp, to_additive]
theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align finset.univ_mul_univ Finset.univ_mul_univ
#align finset.univ_add_univ Finset.univ_add_univ

/- warning: finset.univ_pow -> Finset.univ_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {n : Nat} [_inst_4 : Fintype.{u1} α], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Finset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.univ.{u1} α _inst_4) n) (Finset.univ.{u1} α _inst_4))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Monoid.{u1} α] {n : Nat} [_inst_4 : Fintype.{u1} α], (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Finset.{u1} α) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Nat (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Nat (Finset.npow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Monoid.toOne.{u1} α _inst_3) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_3)))) (Finset.univ.{u1} α _inst_4) n) (Finset.univ.{u1} α _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.univ_pow Finset.univ_powₓ'. -/
@[simp, to_additive nsmul_univ]
theorem univ_pow [Fintype α] (hn : n ≠ 0) : (univ : Finset α) ^ n = univ :=
  coe_injective <| by rw [coe_pow, coe_univ, Set.univ_pow hn]
#align finset.univ_pow Finset.univ_pow
#align finset.nsmul_univ Finset.nsmul_univ

#print IsUnit.finset /-
@[to_additive]
protected theorem IsUnit.finset : IsUnit a → IsUnit ({a} : Finset α) :=
  IsUnit.map (singletonMonoidHom : α →* Finset α)
#align is_unit.finset IsUnit.finset
#align is_add_unit.finset IsAddUnit.finset
-/

end Monoid

section CommMonoid

variable [CommMonoid α]

#print Finset.commMonoid /-
/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "]
protected def commMonoid : CommMonoid (Finset α) :=
  coe_injective.CommMonoid _ coe_one coe_mul coe_pow
#align finset.comm_monoid Finset.commMonoid
#align finset.add_comm_monoid Finset.addCommMonoid
-/

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

#print Finset.coe_prod /-
@[simp, norm_cast, to_additive]
theorem coe_prod {ι : Type _} (s : Finset ι) (f : ι → Finset α) :
    (↑(∏ i in s, f i) : Set α) = ∏ i in s, f i :=
  map_prod (coeMonoidHom : Finset α →* Set α) _ _
#align finset.coe_prod Finset.coe_prod
#align finset.coe_sum Finset.coe_sum
-/

end CommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Finset α}

/- warning: finset.coe_zpow -> Finset.coe_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : DivisionMonoid.{u1} α] (s : Finset.{u1} α) (n : Int), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Int (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Int (Finset.zpow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) s n)) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Int (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Int (Set.ZPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) (DivInvMonoid.toHasInv.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) n)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : DivisionMonoid.{u1} α] (s : Finset.{u1} α) (n : Int), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (HPow.hPow.{u1, 0, u1} (Finset.{u1} α) Int (Finset.{u1} α) (instHPow.{u1, 0} (Finset.{u1} α) Int (Finset.zpow.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_3))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_3))))) s n)) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Int (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Int (Set.ZPow.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_3))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_3))))) (Finset.toSet.{u1} α s) n)
Case conversion may be inaccurate. Consider using '#align finset.coe_zpow Finset.coe_zpowₓ'. -/
@[simp, to_additive]
theorem coe_zpow (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s ^ n : Set α)
  | Int.ofNat n => coe_pow _ _
  | Int.negSucc n => by
    refine' (coe_inv _).trans _
    convert congr_arg Inv.inv (coe_pow _ _)
#align finset.coe_zpow Finset.coe_zpow
#align finset.coe_zsmul Finset.coe_zsmul

/- warning: finset.mul_eq_one_iff -> Finset.mul_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : DivisionMonoid.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))))) s t) (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3))))))))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (Eq.{succ u1} (Finset.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (And (Eq.{succ u1} (Finset.{u1} α) t (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3))))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : DivisionMonoid.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3)))))) s t) (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_3))))))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (Eq.{succ u1} (Finset.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (And (Eq.{succ u1} (Finset.{u1} α) t (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_3))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_3))))))))))
Case conversion may be inaccurate. Consider using '#align finset.mul_eq_one_iff Finset.mul_eq_one_iffₓ'. -/
@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]
#align finset.mul_eq_one_iff Finset.mul_eq_one_iff
#align finset.add_eq_zero_iff Finset.add_eq_zero_iff

#print Finset.divisionMonoid /-
/-- `finset α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`finset α` is a subtraction monoid under pointwise operations if\n`α` is."]
protected def divisionMonoid : DivisionMonoid (Finset α) :=
  coe_injective.DivisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow
#align finset.division_monoid Finset.divisionMonoid
#align finset.subtraction_monoid Finset.subtractionMonoid
-/

#print Finset.isUnit_iff /-
@[simp, to_additive]
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a :=
  by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset
#align finset.is_unit_iff Finset.isUnit_iff
#align finset.is_add_unit_iff Finset.isAddUnit_iff
-/

#print Finset.isUnit_coe /-
@[simp, to_additive]
theorem isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [is_unit_iff, Set.isUnit_iff, coe_eq_singleton]
#align finset.is_unit_coe Finset.isUnit_coe
#align finset.is_add_unit_coe Finset.isAddUnit_coe
-/

end DivisionMonoid

#print Finset.divisionCommMonoid /-
/-- `finset α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionCommMonoid
      "`finset α` is a commutative subtraction monoid under\npointwise operations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Finset α) :=
  coe_injective.DivisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow
#align finset.division_comm_monoid Finset.divisionCommMonoid
#align finset.subtraction_comm_monoid Finset.subtractionCommMonoid
-/

#print Finset.distribNeg /-
/-- `finset α` has distributive negation if `α` has. -/
protected def distribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Finset α) :=
  coe_injective.HasDistribNeg _ coe_neg coe_mul
#align finset.has_distrib_neg Finset.distribNeg
-/

scoped[Pointwise]
  attribute [instance]
    Finset.divisionMonoid Finset.subtractionMonoid Finset.divisionCommMonoid Finset.subtractionCommMonoid Finset.distribNeg

section Distrib

variable [Distrib α] (s t u : Finset α)

/-!
Note that `finset α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.

```lean
-- {10, 16, 18, 20, 8, 9}
#eval {1, 2} * ({3, 4} + {5, 6} : finset ℕ)

-- {10, 11, 12, 13, 14, 15, 16, 18, 20, 8, 9}
#eval ({1, 2} : finset ℕ) * {3, 4} + {1, 2} * {5, 6}
```
-/


/- warning: finset.mul_add_subset -> Finset.mul_add_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Distrib.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (u : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasMul.{u1} α _inst_3))) s (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasAdd.{u1} α _inst_3))) t u)) (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasAdd.{u1} α _inst_3))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasMul.{u1} α _inst_3))) s t) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasMul.{u1} α _inst_3))) s u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Distrib.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (u : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toMul.{u1} α _inst_3))) s (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toAdd.{u1} α _inst_3))) t u)) (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toAdd.{u1} α _inst_3))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toMul.{u1} α _inst_3))) s t) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toMul.{u1} α _inst_3))) s u))
Case conversion may be inaccurate. Consider using '#align finset.mul_add_subset Finset.mul_add_subsetₓ'. -/
theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image₂_distrib_subset_left mul_add
#align finset.mul_add_subset Finset.mul_add_subset

/- warning: finset.add_mul_subset -> Finset.add_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Distrib.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (u : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasMul.{u1} α _inst_3))) (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasAdd.{u1} α _inst_3))) s t) u) (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasAdd.{u1} α _inst_3))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasMul.{u1} α _inst_3))) s u) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toHasMul.{u1} α _inst_3))) t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Distrib.{u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (u : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toMul.{u1} α _inst_3))) (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toAdd.{u1} α _inst_3))) s t) u) (HAdd.hAdd.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHAdd.{u1} (Finset.{u1} α) (Finset.add.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toAdd.{u1} α _inst_3))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toMul.{u1} α _inst_3))) s u) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Distrib.toMul.{u1} α _inst_3))) t u))
Case conversion may be inaccurate. Consider using '#align finset.add_mul_subset Finset.add_mul_subsetₓ'. -/
theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image₂_distrib_subset_right add_mul
#align finset.add_mul_subset Finset.add_mul_subset

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Finset α}

/-! Note that `finset` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/


/- warning: finset.mul_zero_subset -> Finset.mul_zero_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasMul.{u1} α _inst_3))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3)))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toMul.{u1} α _inst_3))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align finset.mul_zero_subset Finset.mul_zero_subsetₓ'. -/
theorem mul_zero_subset (s : Finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]
#align finset.mul_zero_subset Finset.mul_zero_subset

/- warning: finset.zero_mul_subset -> Finset.zero_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasMul.{u1} α _inst_3))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3))))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toMul.{u1} α _inst_3))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3)))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3))))
Case conversion may be inaccurate. Consider using '#align finset.zero_mul_subset Finset.zero_mul_subsetₓ'. -/
theorem zero_mul_subset (s : Finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]
#align finset.zero_mul_subset Finset.zero_mul_subset

/- warning: finset.nonempty.mul_zero -> Finset.Nonempty.mul_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasMul.{u1} α _inst_3))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3)))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toMul.{u1} α _inst_3))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3)))))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.mul_zero Finset.Nonempty.mul_zeroₓ'. -/
theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
#align finset.nonempty.mul_zero Finset.Nonempty.mul_zero

/- warning: finset.nonempty.zero_mul -> Finset.Nonempty.zero_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toHasMul.{u1} α _inst_3))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3))))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_3))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : MulZeroClass.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulZeroClass.toMul.{u1} α _inst_3))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3)))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_3)))))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.zero_mul Finset.Nonempty.zero_mulₓ'. -/
theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
#align finset.nonempty.zero_mul Finset.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] [DivisionMonoid β] [MonoidHomClass F α β] (f : F) {s t : Finset α} {a b : α}

/-! Note that `finset` is not a `group` because `s / s ≠ 1` in general. -/


/- warning: finset.one_mem_div_iff -> Finset.one_mem_div_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))))) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) s t)) (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))))) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) s t)) (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finset.one_mem_div_iff Finset.one_mem_div_iffₓ'. -/
@[simp, to_additive]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  rw [← mem_coe, ← disjoint_coe, coe_div, Set.one_mem_div_iff]
#align finset.one_mem_div_iff Finset.one_mem_div_iff
#align finset.zero_mem_sub_iff Finset.zero_mem_sub_iff

/- warning: finset.not_one_mem_div_iff -> Finset.not_one_mem_div_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))))) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) s t))) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))))) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) s t))) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.not_one_mem_div_iff Finset.not_one_mem_div_iffₓ'. -/
@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align finset.not_one_mem_div_iff Finset.not_one_mem_div_iff
#align finset.not_zero_mem_sub_iff Finset.not_zero_mem_sub_iff

/- warning: finset.nonempty.one_mem_div -> Finset.Nonempty.one_mem_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))))) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) s s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))))) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) s s))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.one_mem_div Finset.Nonempty.one_mem_divₓ'. -/
@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩
#align finset.nonempty.one_mem_div Finset.Nonempty.one_mem_div
#align finset.nonempty.zero_mem_sub Finset.Nonempty.zero_mem_sub

#print Finset.isUnit_singleton /-
@[to_additive]
theorem isUnit_singleton (a : α) : IsUnit ({a} : Finset α) :=
  (Group.isUnit a).Finset
#align finset.is_unit_singleton Finset.isUnit_singleton
#align finset.is_add_unit_singleton Finset.isAddUnit_singleton
-/

#print Finset.isUnit_iff_singleton /-
@[simp]
theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [is_unit_iff, Group.isUnit, and_true_iff]
#align finset.is_unit_iff_singleton Finset.isUnit_iff_singleton
-/

/- warning: finset.image_mul_left -> Finset.image_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a b) t) (Finset.preimage.{u1, u1} α α t (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) b) (Function.Injective.injOn.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a)) (mul_right_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (LeftCancelSemigroup.toIsLeftCancelMul.{u1} α (LeftCancelMonoid.toLeftCancelSemigroup.{u1} α (CancelMonoid.toLeftCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_3)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a)) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a b) t) (Finset.preimage.{u1, u1} α α t (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) a) b) (Function.Injective.injOn.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.Group.Defs._hyg.2622 : α) (x._@.Mathlib.Algebra.Group.Defs._hyg.2624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) x._@.Mathlib.Algebra.Group.Defs._hyg.2622 x._@.Mathlib.Algebra.Group.Defs._hyg.2624) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) a)) (mul_right_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (IsCancelMul.toIsLeftCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_3))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) a)) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) a) b) (Finset.toSet.{u1} α t))))
Case conversion may be inaccurate. Consider using '#align finset.image_mul_left Finset.image_mul_leftₓ'. -/
@[simp, to_additive]
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) ((mul_right_injective _).InjOn _) :=
  coe_injective <| by simp
#align finset.image_mul_left Finset.image_mul_left
#align finset.image_add_left Finset.image_add_left

/- warning: finset.image_mul_right -> Finset.image_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x b) t) (Finset.preimage.{u1, u1} α α t (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) b)) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) b)) (mul_left_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (RightCancelSemigroup.toIsRightCancelMul.{u1} α (RightCancelMonoid.toRightCancelSemigroup.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_3)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) b)) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) b)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x b) t) (Finset.preimage.{u1, u1} α α t (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) b)) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) b)) (mul_left_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (IsCancelMul.toIsRightCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_3))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) b)) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) b)) (Finset.toSet.{u1} α t))))
Case conversion may be inaccurate. Consider using '#align finset.image_mul_right Finset.image_mul_rightₓ'. -/
@[simp, to_additive]
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) ((mul_left_injective _).InjOn _) :=
  coe_injective <| by simp
#align finset.image_mul_right Finset.image_mul_right
#align finset.image_add_right Finset.image_add_right

/- warning: finset.image_mul_left' -> Finset.image_mul_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) a) b) t) (Finset.preimage.{u1, u1} α α t (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a b) (Function.Injective.injOn.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a) (mul_right_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (LeftCancelSemigroup.toIsLeftCancelMul.{u1} α (LeftCancelMonoid.toLeftCancelSemigroup.{u1} α (CancelMonoid.toLeftCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_3)))) a) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) a) b) t) (Finset.preimage.{u1, u1} α α t (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a b) (Function.Injective.injOn.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.Group.Defs._hyg.2622 : α) (x._@.Mathlib.Algebra.Group.Defs._hyg.2624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) x._@.Mathlib.Algebra.Group.Defs._hyg.2622 x._@.Mathlib.Algebra.Group.Defs._hyg.2624) a) (mul_right_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (IsCancelMul.toIsLeftCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_3))) a) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) a b) (Finset.toSet.{u1} α t))))
Case conversion may be inaccurate. Consider using '#align finset.image_mul_left' Finset.image_mul_left'ₓ'. -/
@[to_additive]
theorem image_mul_left' :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) ((mul_right_injective _).InjOn _) := by
  simp
#align finset.image_mul_left' Finset.image_mul_left'
#align finset.image_add_left' Finset.image_add_left'

/- warning: finset.image_mul_right' -> Finset.image_mul_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)) b)) t) (Finset.preimage.{u1, u1} α α t (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x b) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) x b) (mul_left_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (RightCancelSemigroup.toIsRightCancelMul.{u1} α (RightCancelMonoid.toRightCancelSemigroup.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_3)))) b) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : Group.{u1} α] {t : Finset.{u1} α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_3)))) b)) t) (Finset.preimage.{u1, u1} α α t (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x b) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) x b) (mul_left_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (IsCancelMul.toIsRightCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_3))) b) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_3))))) _x b) (Finset.toSet.{u1} α t))))
Case conversion may be inaccurate. Consider using '#align finset.image_mul_right' Finset.image_mul_right'ₓ'. -/
@[to_additive]
theorem image_mul_right' :
    image (· * b⁻¹) t = preimage t (· * b) ((mul_left_injective _).InjOn _) := by simp
#align finset.image_mul_right' Finset.image_mul_right'
#align finset.image_add_right' Finset.image_add_right'

/- warning: finset.image_div -> Finset.image_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u3} β] [_inst_3 : Group.{u2} α] [_inst_4 : DivisionMonoid.{u3} β] [_inst_5 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))] (f : F) {s : Finset.{u2} α} {t : Finset.{u2} α}, Eq.{succ u3} (Finset.{u3} β) (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4))) _inst_5))) f) (HDiv.hDiv.{u2, u2, u2} (Finset.{u2} α) (Finset.{u2} α) (Finset.{u2} α) (instHDiv.{u2} (Finset.{u2} α) (Finset.div.{u2} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) s t)) (HDiv.hDiv.{u3, u3, u3} (Finset.{u3} β) (Finset.{u3} β) (Finset.{u3} β) (instHDiv.{u3} (Finset.{u3} β) (Finset.div.{u3} β (fun (a : β) (b : β) => _inst_2 a b) (DivInvMonoid.toHasDiv.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4))) _inst_5))) f) s) (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_2 a b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4))) _inst_5))) f) t))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u3} β] [_inst_3 : Group.{u2} α] [_inst_4 : DivisionMonoid.{u3} β] [_inst_5 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))] (f : F) {s : Finset.{u2} α} {t : Finset.{u2} α}, Eq.{succ u3} (Finset.{u3} β) (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_2 a b) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4))) _inst_5)) f) (HDiv.hDiv.{u2, u2, u2} (Finset.{u2} α) (Finset.{u2} α) (Finset.{u2} α) (instHDiv.{u2} (Finset.{u2} α) (Finset.div.{u2} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) s t)) (HDiv.hDiv.{u3, u3, u3} (Finset.{u3} β) (Finset.{u3} β) (Finset.{u3} β) (instHDiv.{u3} (Finset.{u3} β) (Finset.div.{u3} β (fun (a : β) (b : β) => _inst_2 a b) (DivInvMonoid.toDiv.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_2 a b) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4))) _inst_5)) f) s) (Finset.image.{u2, u3} α β (fun (a : β) (b : β) => _inst_2 a b) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_3))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_4))) _inst_5)) f) t))
Case conversion may be inaccurate. Consider using '#align finset.image_div Finset.image_divₓ'. -/
theorem image_div : (s / t).image (f : α → β) = s.image f / t.image f :=
  image_image₂_distrib <| map_div f
#align finset.image_div Finset.image_div

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Finset α}

/- warning: finset.div_zero_subset -> Finset.div_zero_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_3)))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (GroupWithZero.toDiv.{u1} α _inst_3))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))
Case conversion may be inaccurate. Consider using '#align finset.div_zero_subset Finset.div_zero_subsetₓ'. -/
theorem div_zero_subset (s : Finset α) : s / 0 ⊆ 0 := by simp [subset_iff, mem_div]
#align finset.div_zero_subset Finset.div_zero_subset

/- warning: finset.zero_div_subset -> Finset.zero_div_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_3)))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] (s : Finset.{u1} α), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (GroupWithZero.toDiv.{u1} α _inst_3))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))
Case conversion may be inaccurate. Consider using '#align finset.zero_div_subset Finset.zero_div_subsetₓ'. -/
theorem zero_div_subset (s : Finset α) : 0 / s ⊆ 0 := by simp [subset_iff, mem_div]
#align finset.zero_div_subset Finset.zero_div_subset

/- warning: finset.nonempty.div_zero -> Finset.Nonempty.div_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_3)))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (GroupWithZero.toDiv.{u1} α _inst_3))) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.div_zero Finset.Nonempty.div_zeroₓ'. -/
theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
#align finset.nonempty.div_zero Finset.Nonempty.div_zero

/- warning: finset.nonempty.zero_div -> Finset.Nonempty.zero_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_3)))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_3 : GroupWithZero.{u1} α] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u1} (Finset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHDiv.{u1} (Finset.{u1} α) (Finset.div.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (GroupWithZero.toDiv.{u1} α _inst_3))) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))) s) (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_3))))))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.zero_div Finset.Nonempty.zero_divₓ'. -/
theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
#align finset.nonempty.zero_div Finset.Nonempty.zero_div

end GroupWithZero

end Instances

section Group

variable [Group α] {s t : Finset α} {a b : α}

/- warning: finset.preimage_mul_left_singleton -> Finset.preimage_mul_left_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) (Function.Injective.injOn.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) (mul_right_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (LeftCancelSemigroup.toIsLeftCancelMul.{u1} α (LeftCancelMonoid.toLeftCancelSemigroup.{u1} α (CancelMonoid.toLeftCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_1)))) a) (Set.preimage.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b) ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.9365 : α) (x._@.Mathlib.Data.Finset.Pointwise._hyg.9367 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Finset.Pointwise._hyg.9365 x._@.Mathlib.Data.Finset.Pointwise._hyg.9367) a) (Function.Injective.injOn.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.Group.Defs._hyg.2622 : α) (x._@.Mathlib.Algebra.Group.Defs._hyg.2624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Group.Defs._hyg.2622 x._@.Mathlib.Algebra.Group.Defs._hyg.2624) a) (mul_right_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (IsCancelMul.toIsLeftCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_1))) a) (Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.9365 : α) (x._@.Mathlib.Data.Finset.Pointwise._hyg.9367 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Finset.Pointwise._hyg.9365 x._@.Mathlib.Data.Finset.Pointwise._hyg.9367) a) (Finset.toSet.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b))
Case conversion may be inaccurate. Consider using '#align finset.preimage_mul_left_singleton Finset.preimage_mul_left_singletonₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_singleton :
    preimage {b} ((· * ·) a) ((mul_right_injective _).InjOn _) = {a⁻¹ * b} := by
  classical rw [← image_mul_left', image_singleton]
#align finset.preimage_mul_left_singleton Finset.preimage_mul_left_singleton
#align finset.preimage_add_left_singleton Finset.preimage_add_left_singleton

/- warning: finset.preimage_mul_right_singleton -> Finset.preimage_mul_right_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x a) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x a) (mul_left_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (RightCancelSemigroup.toIsRightCancelMul.{u1} α (RightCancelMonoid.toRightCancelSemigroup.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_1)))) a) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x a) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x a) (mul_left_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (IsCancelMul.toIsRightCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_1))) a) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x a) (Finset.toSet.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)))
Case conversion may be inaccurate. Consider using '#align finset.preimage_mul_right_singleton Finset.preimage_mul_right_singletonₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_singleton :
    preimage {b} (· * a) ((mul_left_injective _).InjOn _) = {b * a⁻¹} := by
  classical rw [← image_mul_right', image_singleton]
#align finset.preimage_mul_right_singleton Finset.preimage_mul_right_singleton
#align finset.preimage_add_right_singleton Finset.preimage_add_right_singleton

/- warning: finset.preimage_mul_left_one -> Finset.preimage_mul_left_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) (Function.Injective.injOn.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) (mul_right_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (LeftCancelSemigroup.toIsLeftCancelMul.{u1} α (LeftCancelMonoid.toLeftCancelSemigroup.{u1} α (CancelMonoid.toLeftCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_1)))) a) (Set.preimage.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.9549 : α) (x._@.Mathlib.Data.Finset.Pointwise._hyg.9551 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Finset.Pointwise._hyg.9549 x._@.Mathlib.Data.Finset.Pointwise._hyg.9551) a) (Function.Injective.injOn.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.Group.Defs._hyg.2622 : α) (x._@.Mathlib.Algebra.Group.Defs._hyg.2624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Group.Defs._hyg.2622 x._@.Mathlib.Algebra.Group.Defs._hyg.2624) a) (mul_right_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (IsCancelMul.toIsLeftCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_1))) a) (Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.9549 : α) (x._@.Mathlib.Data.Finset.Pointwise._hyg.9551 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Finset.Pointwise._hyg.9549 x._@.Mathlib.Data.Finset.Pointwise._hyg.9551) a) (Finset.toSet.{u1} α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align finset.preimage_mul_left_one Finset.preimage_mul_left_oneₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_one : preimage 1 ((· * ·) a) ((mul_right_injective _).InjOn _) = {a⁻¹} :=
  by classical rw [← image_mul_left', image_one, mul_one]
#align finset.preimage_mul_left_one Finset.preimage_mul_left_one
#align finset.preimage_add_left_zero Finset.preimage_add_left_zero

/- warning: finset.preimage_mul_right_one -> Finset.preimage_mul_right_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x b) (mul_left_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (RightCancelSemigroup.toIsRightCancelMul.{u1} α (RightCancelMonoid.toRightCancelSemigroup.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_1)))) b) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x b) (mul_left_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (IsCancelMul.toIsRightCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_1))) b) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) (Finset.toSet.{u1} α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align finset.preimage_mul_right_one Finset.preimage_mul_right_oneₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_one : preimage 1 (· * b) ((mul_left_injective _).InjOn _) = {b⁻¹} := by
  classical rw [← image_mul_right', image_one, one_mul]
#align finset.preimage_mul_right_one Finset.preimage_mul_right_one
#align finset.preimage_add_right_zero Finset.preimage_add_right_zero

/- warning: finset.preimage_mul_left_one' -> Finset.preimage_mul_left_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (Function.Injective.injOn.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (mul_right_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (LeftCancelSemigroup.toIsLeftCancelMul.{u1} α (LeftCancelMonoid.toLeftCancelSemigroup.{u1} α (CancelMonoid.toLeftCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) (Set.preimage.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.9718 : α) (x._@.Mathlib.Data.Finset.Pointwise._hyg.9720 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Finset.Pointwise._hyg.9718 x._@.Mathlib.Data.Finset.Pointwise._hyg.9720) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (Function.Injective.injOn.{u1, u1} α α ((fun (x._@.Mathlib.Algebra.Group.Defs._hyg.2622 : α) (x._@.Mathlib.Algebra.Group.Defs._hyg.2624 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Algebra.Group.Defs._hyg.2622 x._@.Mathlib.Algebra.Group.Defs._hyg.2624) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (mul_right_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (IsCancelMul.toIsLeftCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_1))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.9718 : α) (x._@.Mathlib.Data.Finset.Pointwise._hyg.9720 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Finset.Pointwise._hyg.9718 x._@.Mathlib.Data.Finset.Pointwise._hyg.9720) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) (Finset.toSet.{u1} α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align finset.preimage_mul_left_one' Finset.preimage_mul_left_one'ₓ'. -/
@[to_additive]
theorem preimage_mul_left_one' : preimage 1 ((· * ·) a⁻¹) ((mul_right_injective _).InjOn _) = {a} :=
  by rw [preimage_mul_left_one, inv_inv]
#align finset.preimage_mul_left_one' Finset.preimage_mul_left_one'
#align finset.preimage_add_left_zero' Finset.preimage_add_left_zero'

/- warning: finset.preimage_mul_right_one' -> Finset.preimage_mul_right_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (mul_left_injective.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (RightCancelSemigroup.toIsRightCancelMul.{u1} α (RightCancelMonoid.toRightCancelSemigroup.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (Group.toCancelMonoid.{u1} α _inst_1)))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (OfNat.mk.{u1} (Finset.{u1} α) 1 (One.one.{u1} (Finset.{u1} α) (Finset.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Finset.{u1} α) (Finset.preimage.{u1, u1} α α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (Function.Injective.injOn.{u1, u1} α α (fun (x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (mul_left_injective.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (IsCancelMul.toIsRightCancelMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (CancelMonoid.toIsCancelMul.{u1} α (Group.toCancelMonoid.{u1} α _inst_1))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (Finset.toSet.{u1} α (OfNat.ofNat.{u1} (Finset.{u1} α) 1 (One.toOfNat1.{u1} (Finset.{u1} α) (Finset.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))))))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)
Case conversion may be inaccurate. Consider using '#align finset.preimage_mul_right_one' Finset.preimage_mul_right_one'ₓ'. -/
@[to_additive]
theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) ((mul_left_injective _).InjOn _) = {b} := by
  rw [preimage_mul_right_one, inv_inv]
#align finset.preimage_mul_right_one' Finset.preimage_mul_right_one'
#align finset.preimage_add_right_zero' Finset.preimage_add_right_zero'

end Group

/-! ### Scalar addition/multiplication of finsets -/


section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

#print Finset.smul /-
/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and\n`t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def smul : SMul (Finset α) (Finset β) :=
  ⟨image₂ (· • ·)⟩
#align finset.has_smul Finset.smul
#align finset.has_vadd Finset.vadd
-/

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.smul_def /-
@[to_additive]
theorem smul_def : s • t = (s ×ˢ t).image fun p : α × β => p.1 • p.2 :=
  rfl
#align finset.smul_def Finset.smul_def
#align finset.vadd_def Finset.vadd_def
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.image_smul_product /-
@[to_additive]
theorem image_smul_product : ((s ×ˢ t).image fun x : α × β => x.fst • x.snd) = s • t :=
  rfl
#align finset.image_smul_product Finset.image_smul_product
#align finset.image_vadd_product Finset.image_vadd_product
-/

#print Finset.mem_smul /-
@[to_additive]
theorem mem_smul {x : β} : x ∈ s • t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y • z = x :=
  mem_image₂
#align finset.mem_smul Finset.mem_smul
#align finset.mem_vadd Finset.mem_vadd
-/

/- warning: finset.coe_smul -> Finset.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s t)) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{succ u1} (Set.{u1} β) (Finset.toSet.{u1} β (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s t)) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_2)) (Finset.toSet.{u2} α s) (Finset.toSet.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.coe_smul Finset.coe_smulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_smul (s : Finset α) (t : Finset β) : (↑(s • t) : Set β) = (s : Set α) • t :=
  coe_image₂ _ _ _
#align finset.coe_smul Finset.coe_smul
#align finset.coe_vadd Finset.coe_vadd

/- warning: finset.smul_mem_smul -> Finset.smul_mem_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {s : Finset.{u1} α} {t : Finset.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (SMul.smul.{u1, u2} α β _inst_2 a b) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {s : Finset.{u2} α} {t : Finset.{u1} β} {a : α} {b : β}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_2) a b) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s t))
Case conversion may be inaccurate. Consider using '#align finset.smul_mem_smul Finset.smul_mem_smulₓ'. -/
@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image₂_of_mem
#align finset.smul_mem_smul Finset.smul_mem_smul
#align finset.vadd_mem_vadd Finset.vadd_mem_vadd

#print Finset.smul_card_le /-
@[to_additive]
theorem smul_card_le : (s • t).card ≤ s.card • t.card :=
  card_image₂_le _ _ _
#align finset.smul_card_le Finset.smul_card_le
#align finset.vadd_card_le Finset.vadd_card_le
-/

#print Finset.empty_smul /-
@[simp, to_additive]
theorem empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ :=
  image₂_empty_left
#align finset.empty_smul Finset.empty_smul
#align finset.empty_vadd Finset.empty_vadd
-/

/- warning: finset.smul_empty -> Finset.smul_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] (s : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] (s : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))
Case conversion may be inaccurate. Consider using '#align finset.smul_empty Finset.smul_emptyₓ'. -/
@[simp, to_additive]
theorem smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ :=
  image₂_empty_right
#align finset.smul_empty Finset.smul_empty
#align finset.vadd_empty Finset.vadd_empty

#print Finset.smul_eq_empty /-
@[simp, to_additive]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.smul_eq_empty Finset.smul_eq_empty
#align finset.vadd_eq_empty Finset.vadd_eq_empty
-/

#print Finset.smul_nonempty_iff /-
@[simp, to_additive]
theorem smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.smul_nonempty_iff Finset.smul_nonempty_iff
#align finset.vadd_nonempty_iff Finset.vadd_nonempty_iff
-/

/- warning: finset.nonempty.smul -> Finset.Nonempty.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u1} α s) -> (Finset.Nonempty.{u2} β t) -> (Finset.Nonempty.{u2} β (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{u2} α s) -> (Finset.Nonempty.{u1} β t) -> (Finset.Nonempty.{u1} β (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.smul Finset.Nonempty.smulₓ'. -/
@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.smul Finset.Nonempty.smul
#align finset.nonempty.vadd Finset.Nonempty.vadd

#print Finset.Nonempty.of_smul_left /-
@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_smul_left Finset.Nonempty.of_smul_left
#align finset.nonempty.of_vadd_left Finset.Nonempty.of_vadd_left
-/

#print Finset.Nonempty.of_smul_right /-
@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_smul_right Finset.Nonempty.of_smul_right
#align finset.nonempty.of_vadd_right Finset.Nonempty.of_vadd_right
-/

#print Finset.smul_singleton /-
@[to_additive]
theorem smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) :=
  image₂_singleton_right
#align finset.smul_singleton Finset.smul_singleton
#align finset.vadd_singleton Finset.vadd_singleton
-/

#print Finset.singleton_smul_singleton /-
@[to_additive]
theorem singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton
#align finset.singleton_smul_singleton Finset.singleton_smul_singleton
#align finset.singleton_vadd_singleton Finset.singleton_vadd_singleton
-/

/- warning: finset.smul_subset_smul -> Finset.smul_subset_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₁ t₁) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t₁ t₂) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₁ t₁) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.smul_subset_smul Finset.smul_subset_smulₓ'. -/
@[to_additive, mono]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image₂_subset
#align finset.smul_subset_smul Finset.smul_subset_smul
#align finset.vadd_subset_vadd Finset.vadd_subset_vadd

#print Finset.smul_subset_smul_left /-
@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image₂_subset_left
#align finset.smul_subset_smul_left Finset.smul_subset_smul_left
#align finset.vadd_subset_vadd_left Finset.vadd_subset_vadd_left
-/

/- warning: finset.smul_subset_smul_right -> Finset.smul_subset_smul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₁ t) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₁ t) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₂ t))
Case conversion may be inaccurate. Consider using '#align finset.smul_subset_smul_right Finset.smul_subset_smul_rightₓ'. -/
@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image₂_subset_right
#align finset.smul_subset_smul_right Finset.smul_subset_smul_right
#align finset.vadd_subset_vadd_right Finset.vadd_subset_vadd_right

#print Finset.smul_subset_iff /-
@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image₂_subset_iff
#align finset.smul_subset_iff Finset.smul_subset_iff
#align finset.vadd_subset_iff Finset.vadd_subset_iff
-/

attribute [mono] vadd_subset_vadd

/- warning: finset.union_smul -> Finset.union_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u1} α], Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂) t) (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₁ t) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u2} α], Eq.{succ u1} (Finset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂) t) (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₁ t) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₂ t))
Case conversion may be inaccurate. Consider using '#align finset.union_smul Finset.union_smulₓ'. -/
@[to_additive]
theorem union_smul [DecidableEq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image₂_union_left
#align finset.union_smul Finset.union_smul
#align finset.union_vadd Finset.union_vadd

#print Finset.smul_union /-
@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image₂_union_right
#align finset.smul_union Finset.smul_union
#align finset.vadd_union Finset.vadd_union
-/

/- warning: finset.inter_smul_subset -> Finset.inter_smul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u1} α], HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂) t) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₁ t) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u2} α], HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂) t) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₁ t) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s₂ t))
Case conversion may be inaccurate. Consider using '#align finset.inter_smul_subset Finset.inter_smul_subsetₓ'. -/
@[to_additive]
theorem inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image₂_inter_subset_left
#align finset.inter_smul_subset Finset.inter_smul_subset
#align finset.inter_vadd_subset Finset.inter_vadd_subset

#print Finset.smul_inter_subset /-
@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image₂_inter_subset_right
#align finset.smul_inter_subset Finset.smul_inter_subset
#align finset.vadd_inter_subset Finset.vadd_inter_subset
-/

/- warning: finset.subset_smul -> Finset.subset_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] {u : Finset.{u2} β} {s : Set.{u1} α} {t : Set.{u2} β}, (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) u) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_2) s t)) -> (Exists.{succ u1} (Finset.{u1} α) (fun (s' : Finset.{u1} α) => Exists.{succ u2} (Finset.{u2} β) (fun (t' : Finset.{u2} β) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s') s) (And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t') t) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) u (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s' t'))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] {u : Finset.{u1} β} {s : Set.{u2} α} {t : Set.{u1} β}, (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Finset.toSet.{u1} β u) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_2)) s t)) -> (Exists.{succ u2} (Finset.{u2} α) (fun (s' : Finset.{u2} α) => Exists.{succ u1} (Finset.{u1} β) (fun (t' : Finset.{u1} β) => And (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α s') s) (And (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Finset.toSet.{u1} β t') t) (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) u (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s' t'))))))
Case conversion may be inaccurate. Consider using '#align finset.subset_smul Finset.subset_smulₓ'. -/
/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive
      "If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two\nfinsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
theorem subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α)(t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
  subset_image₂
#align finset.subset_smul Finset.subset_smul
#align finset.subset_vadd Finset.subset_vadd

end SMul

/-! ### Scalar subtraction of finsets -/


section VSub

variable [DecidableEq α] [VSub α β] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

include α

/- warning: finset.has_vsub -> Finset.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β], VSub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α], VSub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β)
Case conversion may be inaccurate. Consider using '#align finset.has_vsub Finset.vsubₓ'. -/
/-- The pointwise product of two finsets `s` and `t`: `s -ᵥ t = {x -ᵥ y | x ∈ s, y ∈ t}`. -/
protected def vsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩
#align finset.has_vsub Finset.vsub

scoped[Pointwise] attribute [instance] Finset.vsub

/- warning: finset.vsub_def -> Finset.vsub_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) (Finset.image₂.{u2, u2, u1} β β α (fun (a : α) (b : α) => _inst_1 a b) (VSub.vsub.{u1, u2} α β _inst_2) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t) (Finset.image₂.{u1, u1, u2} β β α (fun (a : α) (b : α) => _inst_2 a b) (fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.11576 : β) (x._@.Mathlib.Data.Finset.Pointwise._hyg.11578 : β) => VSub.vsub.{u2, u1} α β _inst_1 x._@.Mathlib.Data.Finset.Pointwise._hyg.11576 x._@.Mathlib.Data.Finset.Pointwise._hyg.11578) s t)
Case conversion may be inaccurate. Consider using '#align finset.vsub_def Finset.vsub_defₓ'. -/
theorem vsub_def : s -ᵥ t = image₂ (· -ᵥ ·) s t :=
  rfl
#align finset.vsub_def Finset.vsub_def

/- warning: finset.image_vsub_product -> Finset.image_vsub_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, Eq.{succ u1} (Finset.{u1} α) (Finset.image₂.{u2, u2, u1} β β α (fun (a : α) (b : α) => _inst_1 a b) (VSub.vsub.{u1, u2} α β _inst_2) s t) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, Eq.{succ u2} (Finset.{u2} α) (Finset.image₂.{u1, u1, u2} β β α (fun (a : α) (b : α) => _inst_2 a b) (fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.11628 : β) (x._@.Mathlib.Data.Finset.Pointwise._hyg.11630 : β) => VSub.vsub.{u2, u1} α β _inst_1 x._@.Mathlib.Data.Finset.Pointwise._hyg.11628 x._@.Mathlib.Data.Finset.Pointwise._hyg.11630) s t) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)
Case conversion may be inaccurate. Consider using '#align finset.image_vsub_product Finset.image_vsub_productₓ'. -/
@[simp]
theorem image_vsub_product : image₂ (· -ᵥ ·) s t = s -ᵥ t :=
  rfl
#align finset.image_vsub_product Finset.image_vsub_product

/- warning: finset.mem_vsub -> Finset.mem_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (Exists.{succ u2} β (fun (b : β) => Exists.{succ u2} β (fun (c : β) => And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) (And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c t) (Eq.{succ u1} α (VSub.vsub.{u1, u2} α β _inst_2 b c) a)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β} {a : α}, Iff (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Exists.{succ u1} β (fun (b : β) => Exists.{succ u1} β (fun (c : β) => And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s) (And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) c t) (Eq.{succ u2} α (VSub.vsub.{u2, u1} α β _inst_1 b c) a)))))
Case conversion may be inaccurate. Consider using '#align finset.mem_vsub Finset.mem_vsubₓ'. -/
theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b c, b ∈ s ∧ c ∈ t ∧ b -ᵥ c = a :=
  mem_image₂
#align finset.mem_vsub Finset.mem_vsub

/- warning: finset.coe_vsub -> Finset.coe_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] (s : Finset.{u2} β) (t : Finset.{u2} β), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_2) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u2} β) (t : Finset.{u2} β), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Finset.toSet.{u2} β s) (Finset.toSet.{u2} β t))
Case conversion may be inaccurate. Consider using '#align finset.coe_vsub Finset.coe_vsubₓ'. -/
@[simp, norm_cast]
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _
#align finset.coe_vsub Finset.coe_vsub

/- warning: finset.vsub_mem_vsub -> Finset.vsub_mem_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β} {b : β} {c : β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (VSub.vsub.{u1, u2} α β _inst_2 b c) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u2} β} {t : Finset.{u2} β} {b : β} {c : β}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b s) -> (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c t) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (VSub.vsub.{u1, u2} α β _inst_1 b c) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t))
Case conversion may be inaccurate. Consider using '#align finset.vsub_mem_vsub Finset.vsub_mem_vsubₓ'. -/
theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t :=
  mem_image₂_of_mem
#align finset.vsub_mem_vsub Finset.vsub_mem_vsub

/- warning: finset.vsub_card_le -> Finset.vsub_card_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u2} β s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, LE.le.{0} Nat instLENat (Finset.card.{u2} α (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} β s) (Finset.card.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.vsub_card_le Finset.vsub_card_leₓ'. -/
theorem vsub_card_le : (s -ᵥ t : Finset α).card ≤ s.card * t.card :=
  card_image₂_le _ _ _
#align finset.vsub_card_le Finset.vsub_card_le

/- warning: finset.empty_vsub -> Finset.empty_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] (t : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β)) t) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] (t : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.instEmptyCollectionFinset.{u2} β)) t) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.empty_vsub Finset.empty_vsubₓ'. -/
@[simp]
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left
#align finset.empty_vsub Finset.empty_vsub

/- warning: finset.vsub_empty -> Finset.vsub_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] (s : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.instEmptyCollectionFinset.{u2} β))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.vsub_empty Finset.vsub_emptyₓ'. -/
@[simp]
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right
#align finset.vsub_empty Finset.vsub_empty

/- warning: finset.vsub_eq_empty -> Finset.vsub_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, Iff (Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Or (Eq.{succ u2} (Finset.{u2} β) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (Eq.{succ u2} (Finset.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, Iff (Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) (Or (Eq.{succ u1} (Finset.{u1} β) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))) (Eq.{succ u1} (Finset.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))))
Case conversion may be inaccurate. Consider using '#align finset.vsub_eq_empty Finset.vsub_eq_emptyₓ'. -/
@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff
#align finset.vsub_eq_empty Finset.vsub_eq_empty

/- warning: finset.vsub_nonempty -> Finset.vsub_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, Iff (Finset.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) (And (Finset.Nonempty.{u2} β s) (Finset.Nonempty.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, Iff (Finset.Nonempty.{u2} α (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)) (And (Finset.Nonempty.{u1} β s) (Finset.Nonempty.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.vsub_nonempty Finset.vsub_nonemptyₓ'. -/
@[simp]
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff
#align finset.vsub_nonempty Finset.vsub_nonempty

/- warning: finset.nonempty.vsub -> Finset.Nonempty.vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (Finset.Nonempty.{u2} β t) -> (Finset.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u2} β} {t : Finset.{u2} β}, (Finset.Nonempty.{u2} β s) -> (Finset.Nonempty.{u2} β t) -> (Finset.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.vsub Finset.Nonempty.vsubₓ'. -/
theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Finset α).Nonempty :=
  Nonempty.image₂
#align finset.nonempty.vsub Finset.Nonempty.vsub

/- warning: finset.nonempty.of_vsub_left -> Finset.Nonempty.of_vsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, (Finset.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) -> (Finset.Nonempty.{u2} β s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, (Finset.Nonempty.{u2} α (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)) -> (Finset.Nonempty.{u1} β s)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.of_vsub_left Finset.Nonempty.of_vsub_leftₓ'. -/
theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left
#align finset.nonempty.of_vsub_left Finset.Nonempty.of_vsub_left

/- warning: finset.nonempty.of_vsub_right -> Finset.Nonempty.of_vsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β}, (Finset.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t)) -> (Finset.Nonempty.{u2} β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β}, (Finset.Nonempty.{u2} α (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t)) -> (Finset.Nonempty.{u1} β t)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.of_vsub_right Finset.Nonempty.of_vsub_rightₓ'. -/
theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right
#align finset.nonempty.of_vsub_right Finset.Nonempty.of_vsub_right

/- warning: finset.vsub_singleton -> Finset.vsub_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} (b : β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_1 a b) (fun (_x : β) => VSub.vsub.{u1, u2} α β _inst_2 _x b) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} (b : β), Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_2 a b) (fun (_x : β) => VSub.vsub.{u2, u1} α β _inst_1 _x b) s)
Case conversion may be inaccurate. Consider using '#align finset.vsub_singleton Finset.vsub_singletonₓ'. -/
@[simp]
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right
#align finset.vsub_singleton Finset.vsub_singleton

/- warning: finset.singleton_vsub -> Finset.singleton_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {t : Finset.{u2} β} (a : β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) a) t) (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_1 a b) (VSub.vsub.{u1, u2} α β _inst_2 a) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {t : Finset.{u1} β} (a : β), Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) a) t) (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_2 a b) ((fun (x._@.Mathlib.Data.Finset.Pointwise._hyg.12365 : β) (x._@.Mathlib.Data.Finset.Pointwise._hyg.12367 : β) => VSub.vsub.{u2, u1} α β _inst_1 x._@.Mathlib.Data.Finset.Pointwise._hyg.12365 x._@.Mathlib.Data.Finset.Pointwise._hyg.12367) a) t)
Case conversion may be inaccurate. Consider using '#align finset.singleton_vsub Finset.singleton_vsubₓ'. -/
theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image ((· -ᵥ ·) a) :=
  image₂_singleton_left
#align finset.singleton_vsub Finset.singleton_vsub

/- warning: finset.singleton_vsub_singleton -> Finset.singleton_vsub_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] (a : β) (b : β), Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) a) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) (VSub.vsub.{u1, u2} α β _inst_2 a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] (a : β) (b : β), Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) a) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) (VSub.vsub.{u2, u1} α β _inst_1 a b))
Case conversion may be inaccurate. Consider using '#align finset.singleton_vsub_singleton Finset.singleton_vsub_singletonₓ'. -/
@[simp]
theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton
#align finset.singleton_vsub_singleton Finset.singleton_vsub_singleton

/- warning: finset.vsub_subset_vsub -> Finset.vsub_subset_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₁ t₁) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₂ t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₁ t₁) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.vsub_subset_vsub Finset.vsub_subset_vsubₓ'. -/
@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image₂_subset
#align finset.vsub_subset_vsub Finset.vsub_subset_vsub

/- warning: finset.vsub_subset_vsub_left -> Finset.vsub_subset_vsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t₁) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u2} β} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t₁) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.vsub_subset_vsub_left Finset.vsub_subset_vsub_leftₓ'. -/
theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image₂_subset_left
#align finset.vsub_subset_vsub_left Finset.vsub_subset_vsub_left

/- warning: finset.vsub_subset_vsub_right -> Finset.vsub_subset_vsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {t : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₁ t) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {t : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₁ t) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₂ t))
Case conversion may be inaccurate. Consider using '#align finset.vsub_subset_vsub_right Finset.vsub_subset_vsub_rightₓ'. -/
theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image₂_subset_right
#align finset.vsub_subset_vsub_right Finset.vsub_subset_vsub_right

/- warning: finset.vsub_subset_iff -> Finset.vsub_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t : Finset.{u2} β} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t) u) (forall (x : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (VSub.vsub.{u1, u2} α β _inst_2 x y) u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t : Finset.{u1} β} {u : Finset.{u2} α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t) u) (forall (x : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y t) -> (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (VSub.vsub.{u2, u1} α β _inst_1 x y) u)))
Case conversion may be inaccurate. Consider using '#align finset.vsub_subset_iff Finset.vsub_subset_iffₓ'. -/
theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image₂_subset_iff
#align finset.vsub_subset_iff Finset.vsub_subset_iff

section

variable [DecidableEq β]

/- warning: finset.union_vsub -> Finset.union_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u2} β], Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) t) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₁ t) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s₁ : Finset.{u1} β} {s₂ : Finset.{u1} β} {t : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u1} β], Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) t) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₁ t) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₂ t))
Case conversion may be inaccurate. Consider using '#align finset.union_vsub Finset.union_vsubₓ'. -/
theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image₂_union_left
#align finset.union_vsub Finset.union_vsub

/- warning: finset.vsub_union -> Finset.vsub_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u2} β], Eq.{succ u1} (Finset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) t₁ t₂)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t₁) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u1} β], Eq.{succ u2} (Finset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b)) t₁ t₂)) (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t₁) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.vsub_union Finset.vsub_unionₓ'. -/
theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image₂_union_right
#align finset.vsub_union Finset.vsub_union

/- warning: finset.inter_vsub_subset -> Finset.inter_vsub_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s₁ : Finset.{u2} β} {s₂ : Finset.{u2} β} {t : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u2} β], HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) t) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₁ t) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s₁ : Finset.{u1} β} {s₂ : Finset.{u1} β} {t : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u1} β], HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b)) s₁ s₂) t) (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₁ t) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s₂ t))
Case conversion may be inaccurate. Consider using '#align finset.inter_vsub_subset Finset.inter_vsub_subsetₓ'. -/
theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image₂_inter_subset_left
#align finset.inter_vsub_subset Finset.inter_vsub_subset

/- warning: finset.vsub_inter_subset -> Finset.vsub_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {s : Finset.{u2} β} {t₁ : Finset.{u2} β} {t₂ : Finset.{u2} β} [_inst_3 : DecidableEq.{succ u2} β], HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_3 a b)) t₁ t₂)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t₁) (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u1} β} {t₁ : Finset.{u1} β} {t₂ : Finset.{u1} β} [_inst_3 : DecidableEq.{succ u1} β], HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_3 a b)) t₁ t₂)) (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t₁) (VSub.vsub.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.vsub.{u2, u1} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.vsub_inter_subset Finset.vsub_inter_subsetₓ'. -/
theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image₂_inter_subset_right
#align finset.vsub_inter_subset Finset.vsub_inter_subset

end

/- warning: finset.subset_vsub -> Finset.subset_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : VSub.{u1, u2} α β] {u : Finset.{u1} α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) u) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_2) s t)) -> (Exists.{succ u2} (Finset.{u2} β) (fun (s' : Finset.{u2} β) => Exists.{succ u2} (Finset.{u2} β) (fun (t' : Finset.{u2} β) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) s') s) (And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t') t) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) u (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) _inst_2) s' t'))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] [_inst_2 : DecidableEq.{succ u1} α] {u : Finset.{u1} α} {s : Set.{u2} β} {t : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α u) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)) -> (Exists.{succ u2} (Finset.{u2} β) (fun (s' : Finset.{u2} β) => Exists.{succ u2} (Finset.{u2} β) (fun (t' : Finset.{u2} β) => And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Finset.toSet.{u2} β s') s) (And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Finset.toSet.{u2} β t') t) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) u (VSub.vsub.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.vsub.{u1, u2} α β _inst_1 (fun (a : α) (b : α) => _inst_2 a b)) s' t'))))))
Case conversion may be inaccurate. Consider using '#align finset.subset_vsub Finset.subset_vsubₓ'. -/
/-- If a finset `u` is contained in the pointwise subtraction of two sets `s -ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' -ᵥ t'`. -/
theorem subset_vsub {s t : Set β} :
    ↑u ⊆ s -ᵥ t → ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
  subset_image₂
#align finset.subset_vsub Finset.subset_vsub

end VSub

open Pointwise

/-! ### Translation/scaling of finsets -/


section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t u : Finset β} {a : α} {b : β}

#print Finset.smulFinset /-
/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive "The translation of a finset `s` by a vector `a`:\n`a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def smulFinset : SMul α (Finset β) :=
  ⟨fun a => image <| (· • ·) a⟩
#align finset.has_smul_finset Finset.smulFinset
#align finset.has_vadd_finset Finset.vaddFinset
-/

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset

#print Finset.smul_finset_def /-
@[to_additive]
theorem smul_finset_def : a • s = s.image ((· • ·) a) :=
  rfl
#align finset.smul_finset_def Finset.smul_finset_def
#align finset.vadd_finset_def Finset.vadd_finset_def
-/

#print Finset.image_smul /-
@[to_additive]
theorem image_smul : (s.image fun x => a • x) = a • s :=
  rfl
#align finset.image_smul Finset.image_smul
#align finset.image_vadd Finset.image_vadd
-/

#print Finset.mem_smul_finset /-
@[to_additive]
theorem mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, and_assoc, mem_image, exists_prop, Prod.exists, mem_product]
#align finset.mem_smul_finset Finset.mem_smul_finset
#align finset.mem_vadd_finset Finset.mem_vadd_finset
-/

#print Finset.coe_smul_finset /-
@[simp, norm_cast, to_additive]
theorem coe_smul_finset (a : α) (s : Finset β) : (↑(a • s) : Set β) = a • s :=
  coe_image
#align finset.coe_smul_finset Finset.coe_smul_finset
#align finset.coe_vadd_finset Finset.coe_vadd_finset
-/

#print Finset.smul_finset_mem_smul_finset /-
@[to_additive]
theorem smul_finset_mem_smul_finset : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align finset.smul_finset_mem_smul_finset Finset.smul_finset_mem_smul_finset
#align finset.vadd_finset_mem_vadd_finset Finset.vadd_finset_mem_vadd_finset
-/

#print Finset.smul_finset_card_le /-
@[to_additive]
theorem smul_finset_card_le : (a • s).card ≤ s.card :=
  card_image_le
#align finset.smul_finset_card_le Finset.smul_finset_card_le
#align finset.vadd_finset_card_le Finset.vadd_finset_card_le
-/

#print Finset.smul_finset_empty /-
@[simp, to_additive]
theorem smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ :=
  image_empty _
#align finset.smul_finset_empty Finset.smul_finset_empty
#align finset.vadd_finset_empty Finset.vadd_finset_empty
-/

#print Finset.smul_finset_eq_empty /-
@[simp, to_additive]
theorem smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align finset.smul_finset_eq_empty Finset.smul_finset_eq_empty
#align finset.vadd_finset_eq_empty Finset.vadd_finset_eq_empty
-/

#print Finset.smul_finset_nonempty /-
@[simp, to_additive]
theorem smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  Nonempty.image_iff _
#align finset.smul_finset_nonempty Finset.smul_finset_nonempty
#align finset.vadd_finset_nonempty Finset.vadd_finset_nonempty
-/

#print Finset.Nonempty.smul_finset /-
@[to_additive]
theorem Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _
#align finset.nonempty.smul_finset Finset.Nonempty.smul_finset
#align finset.nonempty.vadd_finset Finset.Nonempty.vadd_finset
-/

#print Finset.singleton_smul /-
@[simp, to_additive]
theorem singleton_smul (a : α) : ({a} : Finset α) • t = a • t :=
  image₂_singleton_left
#align finset.singleton_smul Finset.singleton_smul
#align finset.singleton_vadd Finset.singleton_vadd
-/

#print Finset.smul_finset_subset_smul_finset /-
@[to_additive, mono]
theorem smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t :=
  image_subset_image
#align finset.smul_finset_subset_smul_finset Finset.smul_finset_subset_smul_finset
#align finset.vadd_finset_subset_vadd_finset Finset.vadd_finset_subset_vadd_finset
-/

attribute [mono] vadd_finset_subset_vadd_finset

#print Finset.smul_finset_singleton /-
@[simp, to_additive]
theorem smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} :=
  image_singleton _ _
#align finset.smul_finset_singleton Finset.smul_finset_singleton
#align finset.vadd_finset_singleton Finset.vadd_finset_singleton
-/

#print Finset.smul_finset_union /-
@[to_additive]
theorem smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ :=
  image_union _ _
#align finset.smul_finset_union Finset.smul_finset_union
#align finset.vadd_finset_union Finset.vadd_finset_union
-/

#print Finset.smul_finset_inter_subset /-
@[to_additive]
theorem smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ a • s₂ :=
  image_inter_subset _ _ _
#align finset.smul_finset_inter_subset Finset.smul_finset_inter_subset
#align finset.vadd_finset_inter_subset Finset.vadd_finset_inter_subset
-/

/- warning: finset.bUnion_smul_finset -> Finset.bunionᵢ_smul_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : SMul.{u1, u2} α β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u2} (Finset.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s (fun (_x : α) => SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) _x t)) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : SMul.{u2, u1} α β] (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{succ u1} (Finset.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s (fun (_x : α) => HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) _x t)) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) _inst_2)) s t)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_smul_finset Finset.bunionᵢ_smul_finsetₓ'. -/
@[simp]
theorem bunionᵢ_smul_finset (s : Finset α) (t : Finset β) : s.bunionᵢ (· • t) = s • t :=
  bunionᵢ_image_left
#align finset.bUnion_smul_finset Finset.bunionᵢ_smul_finset

end SMul

open Pointwise

section Instances

variable [DecidableEq γ]

#print Finset.smulCommClass_finset /-
@[to_additive]
instance smulCommClass_finset [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Finset γ) :=
  ⟨fun _ _ => Commute.finset_image <| smul_comm _ _⟩
#align finset.smul_comm_class_finset Finset.smulCommClass_finset
#align finset.vadd_comm_class_finset Finset.vaddCommClass_finset
-/

#print Finset.smulCommClass_finset' /-
@[to_additive]
instance smulCommClass_finset' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_comm]⟩
#align finset.smul_comm_class_finset' Finset.smulCommClass_finset'
#align finset.vadd_comm_class_finset' Finset.vaddCommClass_finset'
-/

#print Finset.smulCommClass_finset'' /-
@[to_additive]
instance smulCommClass_finset'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) β (Finset γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _
#align finset.smul_comm_class_finset'' Finset.smulCommClass_finset''
#align finset.vadd_comm_class_finset'' Finset.vaddCommClass_finset''
-/

#print Finset.smulCommClass /-
@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) (Finset β) (Finset γ) :=
  ⟨fun s t u => coe_injective <| by simp_rw [coe_smul, smul_comm]⟩
#align finset.smul_comm_class Finset.smulCommClass
#align finset.vadd_comm_class Finset.vaddCommClass
-/

#print Finset.isScalarTower /-
@[to_additive]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc]⟩
#align finset.is_scalar_tower Finset.isScalarTower
#align finset.vadd_assoc_class Finset.vaddAssocClass
-/

variable [DecidableEq β]

#print Finset.isScalarTower' /-
@[to_additive]
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩
#align finset.is_scalar_tower' Finset.isScalarTower'
#align finset.vadd_assoc_class' Finset.vaddAssocClass'
-/

#print Finset.isScalarTower'' /-
@[to_additive]
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩
#align finset.is_scalar_tower'' Finset.isScalarTower''
#align finset.vadd_assoc_class'' Finset.vaddAssocClass''
-/

#print Finset.isCentralScalar /-
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Finset β) :=
  ⟨fun a s => coe_injective <| by simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩
#align finset.is_central_scalar Finset.isCentralScalar
-/

#print Finset.mulAction /-
/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`finset α` on `finset β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action\nof `finset α` on `finset β`"]
protected def mulAction [DecidableEq α] [Monoid α] [MulAction α β] : MulAction (Finset α) (Finset β)
    where
  mul_smul _ _ _ := image₂_assoc mul_smul
  one_smul s := image₂_singleton_left.trans <| by simp_rw [one_smul, image_id']
#align finset.mul_action Finset.mulAction
#align finset.add_action Finset.addAction
-/

#print Finset.mulActionFinset /-
/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `finset β`.
-/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action\non `finset β`."]
protected def mulActionFinset [Monoid α] [MulAction α β] : MulAction α (Finset β) :=
  coe_injective.MulAction _ coe_smul_finset
#align finset.mul_action_finset Finset.mulActionFinset
#align finset.add_action_finset Finset.addActionFinset
-/

scoped[Pointwise]
  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

#print Finset.distribMulActionFinset /-
/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `finset β`. -/
protected def distribMulActionFinset [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Finset β) :=
  Function.Injective.distribMulAction ⟨coe, coe_zero, coe_add⟩ coe_injective coe_smul_finset
#align finset.distrib_mul_action_finset Finset.distribMulActionFinset
-/

#print Finset.mulDistribMulActionFinset /-
/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mulDistribMulActionFinset [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Finset β) :=
  Function.Injective.mulDistribMulAction ⟨coe, coe_one, coe_mul⟩ coe_injective coe_smul_finset
#align finset.mul_distrib_mul_action_finset Finset.mulDistribMulActionFinset
-/

scoped[Pointwise]
  attribute [instance] Finset.distribMulActionFinset Finset.mulDistribMulActionFinset

instance [DecidableEq α] [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Finset α) :=
  coe_injective.NoZeroDivisors _ coe_zero coe_mul

instance [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Finset α) (Finset β) :=
  ⟨fun s t h => by
    by_contra' H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_smul_left.subset_zero_iff, ← hst.of_smul_right.subset_zero_iff, not_subset,
      mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    have := subset_of_eq h
    exact
      (eq_zero_or_eq_zero_of_smul_eq_zero <| mem_zero.1 <| this <| smul_mem_smul hs ht).elim ha hb⟩

#print Finset.noZeroSMulDivisors_finset /-
instance noZeroSMulDivisors_finset [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Finset β) :=
  coe_injective.NoZeroSMulDivisors _ coe_zero coe_smul_finset
#align finset.no_zero_smul_divisors_finset Finset.noZeroSMulDivisors_finset
-/

end Instances

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] [DecidableEq α] (s t : Finset α) (a : α)

/- warning: finset.pairwise_disjoint_smul_iff -> Finset.pairwiseDisjoint_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Set.{u1} α} {t : Finset.{u1} α}, Iff (Set.PairwiseDisjoint.{u1, u1} (Finset.{u1} α) α (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (fun (_x : α) => SMul.smul.{u1, u1} α (Finset.{u1} α) (Finset.smulFinset.{u1, u1} α α (fun (a : α) (b : α) => _inst_2 a b) (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) _x t)) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Set.prod.{u1, u1} α α s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] {s : Set.{u1} α} {t : Finset.{u1} α}, Iff (Set.PairwiseDisjoint.{u1, u1} (Finset.{u1} α) α (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (fun (_x : α) => HSMul.hSMul.{u1, u1, u1} α (Finset.{u1} α) (Finset.{u1} α) (instHSMul.{u1, u1} α (Finset.{u1} α) (Finset.smulFinset.{u1, u1} α α (fun (a : α) (b : α) => _inst_2 a b) (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1))))) _x t)) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Set.prod.{u1, u1} α α s (Finset.toSet.{u1} α t)))
Case conversion may be inaccurate. Consider using '#align finset.pairwise_disjoint_smul_iff Finset.pairwiseDisjoint_smul_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem pairwiseDisjoint_smul_iff {s : Set α} {t : Finset α} :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 := by
  simp_rw [← pairwise_disjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]
#align finset.pairwise_disjoint_smul_iff Finset.pairwiseDisjoint_smul_iff
#align finset.pairwise_disjoint_vadd_iff Finset.pairwiseDisjoint_vadd_iff

/- warning: finset.card_singleton_mul -> Finset.card_singleton_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (t : Finset.{u1} α) (a : α), Eq.{1} Nat (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t)) (Finset.card.{u1} α t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (t : Finset.{u1} α) (a : α), Eq.{1} Nat (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t)) (Finset.card.{u1} α t)
Case conversion may be inaccurate. Consider using '#align finset.card_singleton_mul Finset.card_singleton_mulₓ'. -/
@[simp, to_additive]
theorem card_singleton_mul : ({a} * t).card = t.card :=
  card_image₂_singleton_left _ <| mul_right_injective _
#align finset.card_singleton_mul Finset.card_singleton_mul
#align finset.card_singleton_add Finset.card_singleton_add

/- warning: finset.singleton_mul_inter -> Finset.singleton_mul_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (a : α), Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) s) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (a : α), Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) s) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t))
Case conversion may be inaccurate. Consider using '#align finset.singleton_mul_inter Finset.singleton_mul_interₓ'. -/
@[to_additive]
theorem singleton_mul_inter : {a} * (s ∩ t) = {a} * s ∩ ({a} * t) :=
  image₂_singleton_inter _ _ <| mul_right_injective _
#align finset.singleton_mul_inter Finset.singleton_mul_inter
#align finset.singleton_add_inter Finset.singleton_add_inter

/- warning: finset.card_le_card_mul_left -> Finset.card_le_card_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (t : Finset.{u1} α) {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α t) (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (t : Finset.{u1} α) {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (LE.le.{0} Nat instLENat (Finset.card.{u1} α t) (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s t)))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_mul_left Finset.card_le_card_mul_leftₓ'. -/
@[to_additive]
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : t.card ≤ (s * t).card :=
  card_le_card_image₂_left _ hs mul_right_injective
#align finset.card_le_card_mul_left Finset.card_le_card_mul_left
#align finset.card_le_card_add_left Finset.card_le_card_add_left

end LeftCancelSemigroup

section

variable [RightCancelSemigroup α] [DecidableEq α] (s t : Finset α) (a : α)

/- warning: finset.card_mul_singleton -> Finset.card_mul_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : RightCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α), Eq.{1} Nat (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a))) (Finset.card.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : RightCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (a : α), Eq.{1} Nat (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a))) (Finset.card.{u1} α s)
Case conversion may be inaccurate. Consider using '#align finset.card_mul_singleton Finset.card_mul_singletonₓ'. -/
@[simp, to_additive]
theorem card_mul_singleton : (s * {a}).card = s.card :=
  card_image₂_singleton_right _ <| mul_left_injective _
#align finset.card_mul_singleton Finset.card_mul_singleton
#align finset.card_add_singleton Finset.card_add_singleton

/- warning: finset.inter_mul_singleton -> Finset.inter_mul_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : RightCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (a : α), Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) t (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : RightCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (a : α), Eq.{succ u1} (Finset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) t (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)))
Case conversion may be inaccurate. Consider using '#align finset.inter_mul_singleton Finset.inter_mul_singletonₓ'. -/
@[to_additive]
theorem inter_mul_singleton : s ∩ t * {a} = s * {a} ∩ (t * {a}) :=
  image₂_inter_singleton _ _ <| mul_left_injective _
#align finset.inter_mul_singleton Finset.inter_mul_singleton
#align finset.inter_add_singleton Finset.inter_add_singleton

/- warning: finset.card_le_card_mul_right -> Finset.card_le_card_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : RightCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) {t : Finset.{u1} α}, (Finset.Nonempty.{u1} α t) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toHasMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : RightCancelSemigroup.{u1} α] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) {t : Finset.{u1} α}, (Finset.Nonempty.{u1} α t) -> (LE.le.{0} Nat instLENat (Finset.card.{u1} α s) (Finset.card.{u1} α (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (Semigroup.toMul.{u1} α (RightCancelSemigroup.toSemigroup.{u1} α _inst_1)))) s t)))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_mul_right Finset.card_le_card_mul_rightₓ'. -/
@[to_additive]
theorem card_le_card_mul_right {t : Finset α} (ht : t.Nonempty) : s.card ≤ (s * t).card :=
  card_le_card_image₂_right _ ht mul_left_injective
#align finset.card_le_card_mul_right Finset.card_le_card_mul_right
#align finset.card_le_card_add_right Finset.card_le_card_add_right

end

open Pointwise

section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

#print Finset.smul_mem_smul_finset_iff /-
@[simp, to_additive]
theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
  (MulAction.injective _).mem_finset_image
#align finset.smul_mem_smul_finset_iff Finset.smul_mem_smul_finset_iff
#align finset.vadd_mem_vadd_finset_iff Finset.vadd_mem_vadd_finset_iff
-/

/- warning: finset.inv_smul_mem_iff -> Finset.inv_smul_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) a) b) s) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) a s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) a) b) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3))) a s))
Case conversion may be inaccurate. Consider using '#align finset.inv_smul_mem_iff Finset.inv_smul_mem_iffₓ'. -/
@[to_additive]
theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]
#align finset.inv_smul_mem_iff Finset.inv_smul_mem_iff
#align finset.neg_vadd_mem_iff Finset.neg_vadd_mem_iff

/- warning: finset.mem_inv_smul_finset_iff -> Finset.mem_inv_smul_finset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) a) s)) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3) a b) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) a) s)) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) a b) s)
Case conversion may be inaccurate. Consider using '#align finset.mem_inv_smul_finset_iff Finset.mem_inv_smul_finset_iffₓ'. -/
@[to_additive]
theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]
#align finset.mem_inv_smul_finset_iff Finset.mem_inv_smul_finset_iff
#align finset.mem_neg_vadd_finset_iff Finset.mem_neg_vadd_finset_iff

#print Finset.smul_finset_subset_smul_finset_iff /-
@[simp, to_additive]
theorem smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
  image_subset_image_iff <| MulAction.injective _
#align finset.smul_finset_subset_smul_finset_iff Finset.smul_finset_subset_smul_finset_iff
#align finset.vadd_finset_subset_vadd_finset_iff Finset.vadd_finset_subset_vadd_finset_iff
-/

/- warning: finset.smul_finset_subset_iff -> Finset.smul_finset_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) a s) t) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) a) t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3))) a s) t) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) s (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) a) t))
Case conversion may be inaccurate. Consider using '#align finset.smul_finset_subset_iff Finset.smul_finset_subset_iffₓ'. -/
@[to_additive]
theorem smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  by
  simp_rw [← coe_subset]
  push_cast
  exact Set.set_smul_subset_iff
#align finset.smul_finset_subset_iff Finset.smul_finset_subset_iff
#align finset.vadd_finset_subset_iff Finset.vadd_finset_subset_iff

/- warning: finset.subset_smul_finset_iff -> Finset.subset_smul_finset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) a t)) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) a) s) t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : Group.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) s (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3))) a t)) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)) _inst_3))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))) a) s) t)
Case conversion may be inaccurate. Consider using '#align finset.subset_smul_finset_iff Finset.subset_smul_finset_iffₓ'. -/
@[to_additive]
theorem subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_set_smul_iff
#align finset.subset_smul_finset_iff Finset.subset_smul_finset_iff
#align finset.subset_vadd_finset_iff Finset.subset_vadd_finset_iff

end Group

section GroupWithZero

variable [DecidableEq β] [GroupWithZero α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

/- warning: finset.smul_mem_smul_finset_iff₀ -> Finset.smul_mem_smul_finset_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3) a b) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a s)) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : GroupWithZero.{u2} α] [_inst_3 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))] {s : Finset.{u1} β} {a : α} {b : β}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))))) -> (Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3)) a b) (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) a s)) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b s))
Case conversion may be inaccurate. Consider using '#align finset.smul_mem_smul_finset_iff₀ Finset.smul_mem_smul_finset_iff₀ₓ'. -/
@[simp]
theorem smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
  smul_mem_smul_finset_iff (Units.mk0 a ha)
#align finset.smul_mem_smul_finset_iff₀ Finset.smul_mem_smul_finset_iff₀

/- warning: finset.inv_smul_mem_iff₀ -> Finset.inv_smul_mem_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_2)) a) b) s) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : GroupWithZero.{u2} α] [_inst_3 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))] {s : Finset.{u1} β} {a : α} {b : β}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))))) -> (Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3)) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_2) a) b) s) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) a s)))
Case conversion may be inaccurate. Consider using '#align finset.inv_smul_mem_iff₀ Finset.inv_smul_mem_iff₀ₓ'. -/
theorem inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
  show _ ↔ _ ∈ Units.mk0 a ha • _ from inv_smul_mem_iff
#align finset.inv_smul_mem_iff₀ Finset.inv_smul_mem_iff₀

/- warning: finset.mem_inv_smul_finset_iff₀ -> Finset.mem_inv_smul_finset_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {s : Finset.{u2} β} {a : α} {b : β}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_2)) a) s)) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3) a b) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : GroupWithZero.{u2} α] [_inst_3 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))] {s : Finset.{u1} β} {a : α} {b : β}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))))) -> (Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_2) a) s)) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3)) a b) s))
Case conversion may be inaccurate. Consider using '#align finset.mem_inv_smul_finset_iff₀ Finset.mem_inv_smul_finset_iff₀ₓ'. -/
theorem mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_finset_iff
#align finset.mem_inv_smul_finset_iff₀ Finset.mem_inv_smul_finset_iff₀

/- warning: finset.smul_finset_subset_smul_finset_iff₀ -> Finset.smul_finset_subset_smul_finset_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a s) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a t)) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : GroupWithZero.{u2} α] [_inst_3 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))] {s : Finset.{u1} β} {t : Finset.{u1} β} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))))) -> (Iff (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) a s) (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) a t)) (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) s t))
Case conversion may be inaccurate. Consider using '#align finset.smul_finset_subset_smul_finset_iff₀ Finset.smul_finset_subset_smul_finset_iff₀ₓ'. -/
@[simp]
theorem smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_smul_finset_iff
#align finset.smul_finset_subset_smul_finset_iff₀ Finset.smul_finset_subset_smul_finset_iff₀

/- warning: finset.smul_finset_subset_iff₀ -> Finset.smul_finset_subset_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a s) t) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_2)) a) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : GroupWithZero.{u2} α] [_inst_3 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))] {s : Finset.{u1} β} {t : Finset.{u1} β} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))))) -> (Iff (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) a s) t) (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) s (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_2) a) t)))
Case conversion may be inaccurate. Consider using '#align finset.smul_finset_subset_iff₀ Finset.smul_finset_subset_iff₀ₓ'. -/
theorem smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from smul_finset_subset_iff
#align finset.smul_finset_subset_iff₀ Finset.smul_finset_subset_iff₀

/- warning: finset.subset_smul_finset_iff₀ -> Finset.subset_smul_finset_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {s : Finset.{u2} β} {t : Finset.{u2} β} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) s (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a t)) (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_2)) a) s) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : GroupWithZero.{u2} α] [_inst_3 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))] {s : Finset.{u1} β} {t : Finset.{u1} β} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2))))) -> (Iff (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) s (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) a t)) (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_2)) _inst_3))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_2) a) s) t))
Case conversion may be inaccurate. Consider using '#align finset.subset_smul_finset_iff₀ Finset.subset_smul_finset_iff₀ₓ'. -/
theorem subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_smul_finset_iff
#align finset.subset_smul_finset_iff₀ Finset.subset_smul_finset_iff₀

/- warning: finset.smul_univ₀ -> Finset.smul_univ₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] [_inst_4 : Fintype.{u2} β] {s : Finset.{u1} α}, (Not (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (OfNat.mk.{u1} (Finset.{u1} α) 0 (Zero.zero.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))))) -> (Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) s (Finset.univ.{u2} β _inst_4)) (Finset.univ.{u2} β _inst_4))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] [_inst_4 : Fintype.{u2} β] {s : Finset.{u1} α}, (Not (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s (OfNat.ofNat.{u1} (Finset.{u1} α) 0 (Zero.toOfNat0.{u1} (Finset.{u1} α) (Finset.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))))) -> (Eq.{succ u2} (Finset.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3))) s (Finset.univ.{u2} β _inst_4)) (Finset.univ.{u2} β _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.smul_univ₀ Finset.smul_univ₀ₓ'. -/
theorem smul_univ₀ [Fintype β] {s : Finset α} (hs : ¬s ⊆ 0) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    rw [← coe_subset] at hs
    push_cast at hs⊢
    exact Set.smul_univ₀ hs
#align finset.smul_univ₀ Finset.smul_univ₀

/- warning: finset.smul_finset_univ₀ -> Finset.smul_finset_univ₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {a : α} [_inst_4 : Fintype.{u2} β], (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)))))))) -> (Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3)) a (Finset.univ.{u2} β _inst_4)) (Finset.univ.{u2} β _inst_4))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : GroupWithZero.{u1} α] [_inst_3 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))] {a : α} [_inst_4 : Fintype.{u2} β], (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2))))) -> (Eq.{succ u2} (Finset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (MulAction.toSMul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_2)) _inst_3))) a (Finset.univ.{u2} β _inst_4)) (Finset.univ.{u2} β _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.smul_finset_univ₀ Finset.smul_finset_univ₀ₓ'. -/
theorem smul_finset_univ₀ [Fintype β] (ha : a ≠ 0) : a • (univ : Finset β) = univ :=
  coe_injective <| by
    push_cast
    exact Set.smul_set_univ₀ ha
#align finset.smul_finset_univ₀ Finset.smul_finset_univ₀

end GroupWithZero

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] [DecidableEq β] {s : Finset α} {t : Finset β}

/-!
Note that we have neither `smul_with_zero α (finset β)` nor `smul_with_zero (finset α) (finset β)`
because `0 * ∅ ≠ 0`.
-/


/- warning: finset.smul_zero_subset -> Finset.smul_zero_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : SMulWithZero.{u1, u2} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u2} β] (s : Finset.{u1} α), HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))) s (OfNat.ofNat.{u2} (Finset.{u2} β) 0 (OfNat.mk.{u2} (Finset.{u2} β) 0 (Zero.zero.{u2} (Finset.{u2} β) (Finset.zero.{u2} β _inst_2))))) (OfNat.ofNat.{u2} (Finset.{u2} β) 0 (OfNat.mk.{u2} (Finset.{u2} β) 0 (Zero.zero.{u2} (Finset.{u2} β) (Finset.zero.{u2} β _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u2} α] [_inst_2 : Zero.{u1} β] [_inst_3 : SMulWithZero.{u2, u1} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u1} β] (s : Finset.{u2} α), HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) s (OfNat.ofNat.{u1} (Finset.{u1} β) 0 (Zero.toOfNat0.{u1} (Finset.{u1} β) (Finset.zero.{u1} β _inst_2)))) (OfNat.ofNat.{u1} (Finset.{u1} β) 0 (Zero.toOfNat0.{u1} (Finset.{u1} β) (Finset.zero.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align finset.smul_zero_subset Finset.smul_zero_subsetₓ'. -/
theorem smul_zero_subset (s : Finset α) : s • (0 : Finset β) ⊆ 0 := by simp [subset_iff, mem_smul]
#align finset.smul_zero_subset Finset.smul_zero_subset

#print Finset.zero_smul_subset /-
theorem zero_smul_subset (t : Finset β) : (0 : Finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]
#align finset.zero_smul_subset Finset.zero_smul_subset
-/

/- warning: finset.nonempty.smul_zero -> Finset.Nonempty.smul_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : SMulWithZero.{u1, u2} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u2} β] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))) s (OfNat.ofNat.{u2} (Finset.{u2} β) 0 (OfNat.mk.{u2} (Finset.{u2} β) 0 (Zero.zero.{u2} (Finset.{u2} β) (Finset.zero.{u2} β _inst_2))))) (OfNat.ofNat.{u2} (Finset.{u2} β) 0 (OfNat.mk.{u2} (Finset.{u2} β) 0 (Zero.zero.{u2} (Finset.{u2} β) (Finset.zero.{u2} β _inst_2)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u2} α] [_inst_2 : Zero.{u1} β] [_inst_3 : SMulWithZero.{u2, u1} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u1} β] {s : Finset.{u2} α}, (Finset.Nonempty.{u2} α s) -> (Eq.{succ u1} (Finset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) s (OfNat.ofNat.{u1} (Finset.{u1} β) 0 (Zero.toOfNat0.{u1} (Finset.{u1} β) (Finset.zero.{u1} β _inst_2)))) (OfNat.ofNat.{u1} (Finset.{u1} β) 0 (Zero.toOfNat0.{u1} (Finset.{u1} β) (Finset.zero.{u1} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.smul_zero Finset.Nonempty.smul_zeroₓ'. -/
theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
#align finset.nonempty.smul_zero Finset.Nonempty.smul_zero

#print Finset.Nonempty.zero_smul /-
theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
#align finset.nonempty.zero_smul Finset.Nonempty.zero_smul
-/

#print Finset.zero_smul_finset /-
/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_finset {s : Finset β} (h : s.Nonempty) : (0 : α) • s = (0 : Finset β) :=
  coe_injective <| by simpa using @Set.zero_smul_set α _ _ _ _ _ h
#align finset.zero_smul_finset Finset.zero_smul_finset
-/

#print Finset.zero_smul_finset_subset /-
theorem zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => mem_zero.2 <| zero_smul α x
#align finset.zero_smul_finset_subset Finset.zero_smul_finset_subset
-/

#print Finset.zero_mem_smul_finset /-
theorem zero_mem_smul_finset {t : Finset β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  mem_smul_finset.2 ⟨0, h, smul_zero _⟩
#align finset.zero_mem_smul_finset Finset.zero_mem_smul_finset
-/

variable [NoZeroSMulDivisors α β] {a : α}

#print Finset.zero_mem_smul_iff /-
theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty :=
  by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]
  rfl
#align finset.zero_mem_smul_iff Finset.zero_mem_smul_iff
-/

/- warning: finset.zero_mem_smul_finset_iff -> Finset.zero_mem_smul_finset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : SMulWithZero.{u1, u2} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u2} β] {t : Finset.{u2} β} [_inst_5 : NoZeroSMulDivisors.{u1, u2} α β _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))) -> (Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))) a t)) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u2} α] [_inst_2 : Zero.{u1} β] [_inst_3 : SMulWithZero.{u2, u1} α β _inst_1 _inst_2] [_inst_4 : DecidableEq.{succ u1} β] {t : Finset.{u1} β} [_inst_5 : NoZeroSMulDivisors.{u2, u1} α β _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_1))) -> (Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2)) (HSMul.hSMul.{u2, u1, u1} α (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} α (Finset.{u1} β) (Finset.smulFinset.{u2, u1} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) a t)) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2)) t))
Case conversion may be inaccurate. Consider using '#align finset.zero_mem_smul_finset_iff Finset.zero_mem_smul_finset_iffₓ'. -/
theorem zero_mem_smul_finset_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
  by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff ha, mem_coe]
  infer_instance
#align finset.zero_mem_smul_finset_iff Finset.zero_mem_smul_finset_iff

end SMulWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] [DecidableEq β] (a : α) (s : Finset α)
  (t : Finset β)

/- warning: finset.smul_finset_neg -> Finset.smul_finset_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] [_inst_4 : DecidableEq.{succ u2} β] (a : α) (t : Finset.{u2} β), Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) a (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) t)) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] [_inst_4 : DecidableEq.{succ u2} β] (a : α) (t : Finset.{u2} β), Eq.{succ u2} (Finset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) a (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) t)) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) a t))
Case conversion may be inaccurate. Consider using '#align finset.smul_finset_neg Finset.smul_finset_negₓ'. -/
@[simp]
theorem smul_finset_neg : a • -t = -(a • t) := by
  simp only [← image_smul, ← image_neg, Function.comp, image_image, smul_neg]
#align finset.smul_finset_neg Finset.smul_finset_neg

/- warning: finset.smul_neg -> Finset.smul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] [_inst_4 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) s (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) t)) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] [_inst_4 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u2} (Finset.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) s (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) t)) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) (HSMul.hSMul.{u1, u2, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) s t))
Case conversion may be inaccurate. Consider using '#align finset.smul_neg Finset.smul_negₓ'. -/
@[simp]
protected theorem smul_neg : s • -t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image_image₂_right_comm smul_neg
#align finset.smul_neg Finset.smul_neg

end Monoid

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] [DecidableEq β] {s : Finset α} {t : Finset β}
  {a : α}

/- warning: finset.neg_smul_finset -> Finset.neg_smul_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] [_inst_4 : DecidableEq.{succ u2} β] {t : Finset.{u2} β} {a : α}, Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) a) t) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_2)))) (SMul.smul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] [_inst_4 : DecidableEq.{succ u2} β] {t : Finset.{u2} β} {a : α}, Eq.{succ u2} (Finset.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3)))))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) a) t) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2)))))) (HSMul.hSMul.{u1, u2, u2} α (Finset.{u2} β) (Finset.{u2} β) (instHSMul.{u1, u2} α (Finset.{u2} β) (Finset.smulFinset.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3)))))) a t))
Case conversion may be inaccurate. Consider using '#align finset.neg_smul_finset Finset.neg_smul_finsetₓ'. -/
@[simp]
theorem neg_smul_finset : -a • t = -(a • t) := by
  simp only [← image_smul, ← image_neg, image_image, neg_smul]
#align finset.neg_smul_finset Finset.neg_smul_finset

/- warning: finset.neg_smul -> Finset.neg_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] [_inst_4 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : Finset.{u2} β} [_inst_5 : DecidableEq.{succ u1} α], Eq.{succ u2} (Finset.{u2} β) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) (Neg.neg.{u1} (Finset.{u1} α) (Finset.neg.{u1} α (fun (a : α) (b : α) => _inst_5 a b) (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (NonAssocRing.toAddGroupWithOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) s) t) (Neg.neg.{u2} (Finset.{u2} β) (Finset.neg.{u2} β (fun (a : β) (b : β) => _inst_4 a b) (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_2)))) (SMul.smul.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.smul.{u1, u2} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Ring.{u2} α] [_inst_2 : AddCommGroup.{u1} β] [_inst_3 : Module.{u2, u1} α β (Ring.toSemiring.{u2} α _inst_1) (AddCommGroup.toAddCommMonoid.{u1} β _inst_2)] [_inst_4 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : Finset.{u1} β} [_inst_5 : DecidableEq.{succ u2} α], Eq.{succ u1} (Finset.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u2, u1} α β (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_1))) (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_1)) (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2))))) (Module.toMulActionWithZero.{u2, u1} α β (Ring.toSemiring.{u2} α _inst_1) (AddCommGroup.toAddCommMonoid.{u1} β _inst_2) _inst_3)))))) (Neg.neg.{u2} (Finset.{u2} α) (Finset.neg.{u2} α (fun (a : α) (b : α) => _inst_5 a b) (Ring.toNeg.{u2} α _inst_1)) s) t) (Neg.neg.{u1} (Finset.{u1} β) (Finset.neg.{u1} β (fun (a : β) (b : β) => _inst_4 a b) (NegZeroClass.toNeg.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2)))))) (HSMul.hSMul.{u2, u1, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.{u1} β) (instHSMul.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.smul.{u2, u1} α β (fun (a : β) (b : β) => _inst_4 a b) (SMulZeroClass.toSMul.{u2, u1} α β (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} α β (MonoidWithZero.toZero.{u2} α (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_1))) (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} α β (Semiring.toMonoidWithZero.{u2} α (Ring.toSemiring.{u2} α _inst_1)) (NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β _inst_2))))) (Module.toMulActionWithZero.{u2, u1} α β (Ring.toSemiring.{u2} α _inst_1) (AddCommGroup.toAddCommMonoid.{u1} β _inst_2) _inst_3)))))) s t))
Case conversion may be inaccurate. Consider using '#align finset.neg_smul Finset.neg_smulₓ'. -/
@[simp]
protected theorem neg_smul [DecidableEq α] : -s • t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image₂_image_left_comm neg_smul
#align finset.neg_smul Finset.neg_smul

end Ring

end Finset

