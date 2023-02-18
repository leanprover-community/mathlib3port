/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.pointwise.basic
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Hom.Units
import Mathbin.Data.Set.Lattice
import Mathbin.Data.Nat.Order.Basic

/-!
# Pointwise operations of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/


library_note "pointwise nat action"/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/


open Function

variable {F α β γ : Type _}

namespace Set

/-! ### `0`/`1` as sets -/


section One

variable [One α] {s : Set α} {a : α}

#print Set.one /-
/-- The set `1 : set α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `0 : set α` is defined as `{0}` in locale `pointwise`."]
protected def one : One (Set α) :=
  ⟨{1}⟩
#align set.has_one Set.one
#align set.has_zero Set.zero
-/

scoped[Pointwise] attribute [instance] Set.one Set.zero

#print Set.singleton_one /-
@[to_additive]
theorem singleton_one : ({1} : Set α) = 1 :=
  rfl
#align set.singleton_one Set.singleton_one
#align set.singleton_zero Set.singleton_zero
-/

#print Set.mem_one /-
@[simp, to_additive]
theorem mem_one : a ∈ (1 : Set α) ↔ a = 1 :=
  Iff.rfl
#align set.mem_one Set.mem_one
#align set.mem_zero Set.mem_zero
-/

#print Set.one_mem_one /-
@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Set α) :=
  Eq.refl _
#align set.one_mem_one Set.one_mem_one
#align set.zero_mem_zero Set.zero_mem_zero
-/

#print Set.one_subset /-
@[simp, to_additive]
theorem one_subset : 1 ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff
#align set.one_subset Set.one_subset
#align set.zero_subset Set.zero_subset
-/

#print Set.one_nonempty /-
@[to_additive]
theorem one_nonempty : (1 : Set α).Nonempty :=
  ⟨1, rfl⟩
#align set.one_nonempty Set.one_nonempty
#align set.zero_nonempty Set.zero_nonempty
-/

#print Set.image_one /-
@[simp, to_additive]
theorem image_one {f : α → β} : f '' 1 = {f 1} :=
  image_singleton
#align set.image_one Set.image_one
#align set.image_zero Set.image_zero
-/

#print Set.subset_one_iff_eq /-
@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff_eq
#align set.subset_one_iff_eq Set.subset_one_iff_eq
#align set.subset_zero_iff_eq Set.subset_zero_iff_eq
-/

#print Set.Nonempty.subset_one_iff /-
@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff
#align set.nonempty.subset_one_iff Set.Nonempty.subset_one_iff
#align set.nonempty.subset_zero_iff Set.Nonempty.subset_zero_iff
-/

#print Set.singletonOneHom /-
/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singletonOneHom : OneHom α (Set α) :=
  ⟨singleton, singleton_one⟩
#align set.singleton_one_hom Set.singletonOneHom
#align set.singleton_zero_hom Set.singletonZeroHom
-/

#print Set.coe_singletonOneHom /-
@[simp, to_additive]
theorem coe_singletonOneHom : (singletonOneHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_one_hom Set.coe_singletonOneHom
#align set.coe_singleton_zero_hom Set.coe_singletonZeroHom
-/

end One

/-! ### Set negation/inversion -/


section Inv

#print Set.inv /-
/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`. It i
equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
      "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale\n`pointwise`. It is equal to `{-x | x ∈ s}`, see `set.image_neg`."]
protected def inv [Inv α] : Inv (Set α) :=
  ⟨preimage Inv.inv⟩
#align set.has_inv Set.inv
#align set.has_neg Set.neg
-/

scoped[Pointwise] attribute [instance] Set.inv Set.neg

section Inv

variable {ι : Sort _} [Inv α] {s t : Set α} {a : α}

#print Set.mem_inv /-
@[simp, to_additive]
theorem mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s :=
  Iff.rfl
#align set.mem_inv Set.mem_inv
#align set.mem_neg Set.mem_neg
-/

#print Set.inv_preimage /-
@[simp, to_additive]
theorem inv_preimage : Inv.inv ⁻¹' s = s⁻¹ :=
  rfl
#align set.inv_preimage Set.inv_preimage
#align set.neg_preimage Set.neg_preimage
-/

#print Set.inv_empty /-
@[simp, to_additive]
theorem inv_empty : (∅ : Set α)⁻¹ = ∅ :=
  rfl
#align set.inv_empty Set.inv_empty
#align set.neg_empty Set.neg_empty
-/

#print Set.inv_univ /-
@[simp, to_additive]
theorem inv_univ : (univ : Set α)⁻¹ = univ :=
  rfl
#align set.inv_univ Set.inv_univ
#align set.neg_univ Set.neg_univ
-/

/- warning: set.inter_inv -> Set.inter_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Inv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Inv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align set.inter_inv Set.inter_invₓ'. -/
@[simp, to_additive]
theorem inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ :=
  preimage_inter
#align set.inter_inv Set.inter_inv
#align set.inter_neg Set.inter_neg

/- warning: set.union_inv -> Set.union_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Inv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Inv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align set.union_inv Set.union_invₓ'. -/
@[simp, to_additive]
theorem union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ :=
  preimage_union
#align set.union_inv Set.union_inv
#align set.union_neg Set.union_neg

/- warning: set.Inter_inv -> Set.interᵢ_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Inv.{u1} α] (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Inv.{u2} α] (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Inv.inv.{u2} (Set.{u2} α) (Set.inv.{u2} α _inst_1) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Inv.inv.{u2} (Set.{u2} α) (Set.inv.{u2} α _inst_1) (s i)))
Case conversion may be inaccurate. Consider using '#align set.Inter_inv Set.interᵢ_invₓ'. -/
@[simp, to_additive]
theorem interᵢ_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_interᵢ
#align set.Inter_inv Set.interᵢ_inv
#align set.Inter_neg Set.interᵢ_neg

/- warning: set.Union_inv -> Set.unionᵢ_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Inv.{u1} α] (s : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (s i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Inv.{u2} α] (s : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Inv.inv.{u2} (Set.{u2} α) (Set.inv.{u2} α _inst_1) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Inv.inv.{u2} (Set.{u2} α) (Set.inv.{u2} α _inst_1) (s i)))
Case conversion may be inaccurate. Consider using '#align set.Union_inv Set.unionᵢ_invₓ'. -/
@[simp, to_additive]
theorem unionᵢ_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_unionᵢ
#align set.Union_inv Set.unionᵢ_inv
#align set.Union_neg Set.unionᵢ_neg

/- warning: set.compl_inv -> Set.compl_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Inv.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Inv.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align set.compl_inv Set.compl_invₓ'. -/
@[simp, to_additive]
theorem compl_inv : (sᶜ)⁻¹ = s⁻¹ᶜ :=
  preimage_compl
#align set.compl_inv Set.compl_inv
#align set.compl_neg Set.compl_neg

end Inv

section InvolutiveInv

variable [InvolutiveInv α] {s t : Set α} {a : α}

/- warning: set.inv_mem_inv -> Set.inv_mem_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1) a) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1) a) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align set.inv_mem_inv Set.inv_mem_invₓ'. -/
@[to_additive]
theorem inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]
#align set.inv_mem_inv Set.inv_mem_inv
#align set.neg_mem_neg Set.neg_mem_neg

/- warning: set.nonempty_inv -> Set.nonempty_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s)) (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s)) (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty_inv Set.nonempty_invₓ'. -/
@[simp, to_additive]
theorem nonempty_inv : s⁻¹.Nonempty ↔ s.Nonempty :=
  inv_involutive.Surjective.nonempty_preimage
#align set.nonempty_inv Set.nonempty_inv
#align set.nonempty_neg Set.nonempty_neg

/- warning: set.nonempty.inv -> Set.Nonempty.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.nonempty.inv Set.Nonempty.invₓ'. -/
@[to_additive]
theorem Nonempty.inv (h : s.Nonempty) : s⁻¹.Nonempty :=
  nonempty_inv.2 h
#align set.nonempty.inv Set.Nonempty.inv
#align set.nonempty.neg Set.Nonempty.neg

/- warning: set.image_inv -> Set.image_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s)
Case conversion may be inaccurate. Consider using '#align set.image_inv Set.image_invₓ'. -/
@[simp, to_additive]
theorem image_inv : Inv.inv '' s = s⁻¹ :=
  congr_fun (image_eq_preimage_of_inverse inv_involutive.LeftInverse inv_involutive.RightInverse) _
#align set.image_inv Set.image_inv
#align set.image_neg Set.image_neg

@[simp, to_additive]
instance : InvolutiveInv (Set α) where
  inv := Inv.inv
  inv_inv s := by simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id']

/- warning: set.inv_subset_inv -> Set.inv_subset_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.inv_subset_inv Set.inv_subset_invₓ'. -/
@[simp, to_additive]
theorem inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
  (Equiv.inv α).Surjective.preimage_subset_preimage_iff
#align set.inv_subset_inv Set.inv_subset_inv
#align set.neg_subset_neg Set.neg_subset_neg

/- warning: set.inv_subset -> Set.inv_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) t))
Case conversion may be inaccurate. Consider using '#align set.inv_subset Set.inv_subsetₓ'. -/
@[to_additive]
theorem inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by rw [← inv_subset_inv, inv_inv]
#align set.inv_subset Set.inv_subset
#align set.neg_subset Set.neg_subset

/- warning: set.inv_singleton -> Set.inv_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] (a : α), Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] (a : α), Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1) a))
Case conversion may be inaccurate. Consider using '#align set.inv_singleton Set.inv_singletonₓ'. -/
@[simp, to_additive]
theorem inv_singleton (a : α) : ({a} : Set α)⁻¹ = {a⁻¹} := by rw [← image_inv, image_singleton]
#align set.inv_singleton Set.inv_singleton
#align set.neg_singleton Set.neg_singleton

/- warning: set.inv_insert -> Set.inv_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] (a : α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) (Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1) a) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] (a : α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) (Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1) a) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align set.inv_insert Set.inv_insertₓ'. -/
@[simp, to_additive]
theorem inv_insert (a : α) (s : Set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ := by
  rw [insert_eq, union_inv, inv_singleton, insert_eq]
#align set.inv_insert Set.inv_insert
#align set.neg_insert Set.neg_insert

/- warning: set.inv_range -> Set.inv_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {ι : Sort.{u2}} {f : ι -> α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) (Set.range.{u1, u2} α ι f)) (Set.range.{u1, u2} α ι (fun (i : ι) => Inv.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1) (f i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {ι : Sort.{u2}} {f : ι -> α}, Eq.{succ u1} (Set.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) (Set.range.{u1, u2} α ι f)) (Set.range.{u1, u2} α ι (fun (i : ι) => Inv.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1) (f i)))
Case conversion may be inaccurate. Consider using '#align set.inv_range Set.inv_rangeₓ'. -/
@[to_additive]
theorem inv_range {ι : Sort _} {f : ι → α} : (range f)⁻¹ = range fun i => (f i)⁻¹ :=
  by
  rw [← image_inv]
  exact (range_comp _ _).symm
#align set.inv_range Set.inv_range
#align set.neg_range Set.neg_range

open MulOpposite

/- warning: set.image_op_inv -> Set.image_op_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} (MulOpposite.{u1} α)) (Set.image.{u1, u1} α (MulOpposite.{u1} α) (MulOpposite.op.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1)) s)) (Inv.inv.{u1} (Set.{u1} (MulOpposite.{u1} α)) (Set.inv.{u1} (MulOpposite.{u1} α) (MulOpposite.hasInv.{u1} α (InvolutiveInv.toHasInv.{u1} α _inst_1))) (Set.image.{u1, u1} α (MulOpposite.{u1} α) (MulOpposite.op.{u1} α) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InvolutiveInv.{u1} α] {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} (MulOpposite.{u1} α)) (Set.image.{u1, u1} α (MulOpposite.{u1} α) (MulOpposite.op.{u1} α) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1)) s)) (Inv.inv.{u1} (Set.{u1} (MulOpposite.{u1} α)) (Set.inv.{u1} (MulOpposite.{u1} α) (MulOpposite.instInvMulOpposite.{u1} α (InvolutiveInv.toInv.{u1} α _inst_1))) (Set.image.{u1, u1} α (MulOpposite.{u1} α) (MulOpposite.op.{u1} α) s))
Case conversion may be inaccurate. Consider using '#align set.image_op_inv Set.image_op_invₓ'. -/
@[to_additive]
theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← image_inv, Function.Semiconj.set_image op_inv s]
#align set.image_op_inv Set.image_op_inv
#align set.image_op_neg Set.image_op_neg

end InvolutiveInv

end Inv

open Pointwise

/-! ### Set addition/multiplication -/


section Mul

variable {ι : Sort _} {κ : ι → Sort _} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

#print Set.mul /-
/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive
      "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def mul : Mul (Set α) :=
  ⟨image2 (· * ·)⟩
#align set.has_mul Set.mul
#align set.has_add Set.add
-/

scoped[Pointwise] attribute [instance] Set.mul Set.add

#print Set.image2_mul /-
@[simp, to_additive]
theorem image2_mul : image2 Mul.mul s t = s * t :=
  rfl
#align set.image2_mul Set.image2_mul
#align set.image2_add Set.image2_add
-/

#print Set.mem_mul /-
@[to_additive]
theorem mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a :=
  Iff.rfl
#align set.mem_mul Set.mem_mul
#align set.mem_add Set.mem_add
-/

#print Set.mul_mem_mul /-
@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image2_of_mem
#align set.mul_mem_mul Set.mul_mem_mul
#align set.add_mem_add Set.add_mem_add
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.image_mul_prod /-
@[to_additive add_image_prod]
theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t :=
  image_prod _
#align set.image_mul_prod Set.image_mul_prod
#align set.add_image_prod Set.add_image_prod
-/

#print Set.empty_mul /-
@[simp, to_additive]
theorem empty_mul : ∅ * s = ∅ :=
  image2_empty_left
#align set.empty_mul Set.empty_mul
#align set.empty_add Set.empty_add
-/

#print Set.mul_empty /-
@[simp, to_additive]
theorem mul_empty : s * ∅ = ∅ :=
  image2_empty_right
#align set.mul_empty Set.mul_empty
#align set.add_empty Set.add_empty
-/

#print Set.mul_eq_empty /-
@[simp, to_additive]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.mul_eq_empty Set.mul_eq_empty
#align set.add_eq_empty Set.add_eq_empty
-/

#print Set.mul_nonempty /-
@[simp, to_additive]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.mul_nonempty Set.mul_nonempty
#align set.add_nonempty Set.add_nonempty
-/

#print Set.Nonempty.mul /-
@[to_additive]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image2
#align set.nonempty.mul Set.Nonempty.mul
#align set.nonempty.add Set.Nonempty.add
-/

#print Set.Nonempty.of_mul_left /-
@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_mul_left Set.Nonempty.of_mul_left
#align set.nonempty.of_add_left Set.Nonempty.of_add_left
-/

#print Set.Nonempty.of_mul_right /-
@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_mul_right Set.Nonempty.of_mul_right
#align set.nonempty.of_add_right Set.Nonempty.of_add_right
-/

#print Set.mul_singleton /-
@[simp, to_additive]
theorem mul_singleton : s * {b} = (· * b) '' s :=
  image2_singleton_right
#align set.mul_singleton Set.mul_singleton
#align set.add_singleton Set.add_singleton
-/

#print Set.singleton_mul /-
@[simp, to_additive]
theorem singleton_mul : {a} * t = (· * ·) a '' t :=
  image2_singleton_left
#align set.singleton_mul Set.singleton_mul
#align set.singleton_add Set.singleton_add
-/

#print Set.singleton_mul_singleton /-
@[simp, to_additive]
theorem singleton_mul_singleton : ({a} : Set α) * {b} = {a * b} :=
  image2_singleton
#align set.singleton_mul_singleton Set.singleton_mul_singleton
#align set.singleton_add_singleton Set.singleton_add_singleton
-/

#print Set.mul_subset_mul /-
@[to_additive, mono]
theorem mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ :=
  image2_subset
#align set.mul_subset_mul Set.mul_subset_mul
#align set.add_subset_add Set.add_subset_add
-/

#print Set.mul_subset_mul_left /-
@[to_additive]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image2_subset_left
#align set.mul_subset_mul_left Set.mul_subset_mul_left
#align set.add_subset_add_left Set.add_subset_add_left
-/

#print Set.mul_subset_mul_right /-
@[to_additive]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image2_subset_right
#align set.mul_subset_mul_right Set.mul_subset_mul_right
#align set.add_subset_add_right Set.add_subset_add_right
-/

#print Set.mul_subset_iff /-
@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image2_subset_iff
#align set.mul_subset_iff Set.mul_subset_iff
#align set.add_subset_iff Set.add_subset_iff
-/

attribute [mono] add_subset_add

/- warning: set.union_mul -> Set.union_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₁ t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₁ t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_mul Set.union_mulₓ'. -/
@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image2_union_left
#align set.union_mul Set.union_mul
#align set.union_add Set.union_add

/- warning: set.mul_union -> Set.mul_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₁) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₁) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₂))
Case conversion may be inaccurate. Consider using '#align set.mul_union Set.mul_unionₓ'. -/
@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image2_union_right
#align set.mul_union Set.mul_union
#align set.add_union Set.add_union

/- warning: set.inter_mul_subset -> Set.inter_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₁ t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₁ t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.inter_mul_subset Set.inter_mul_subsetₓ'. -/
@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image2_inter_subset_left
#align set.inter_mul_subset Set.inter_mul_subset
#align set.inter_add_subset Set.inter_add_subset

/- warning: set.mul_inter_subset -> Set.mul_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₁) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₁) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s t₂))
Case conversion may be inaccurate. Consider using '#align set.mul_inter_subset Set.mul_inter_subsetₓ'. -/
@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image2_inter_subset_right
#align set.mul_inter_subset Set.mul_inter_subset
#align set.add_inter_subset Set.add_inter_subset

#print Set.unionᵢ_mul_left_image /-
@[to_additive]
theorem unionᵢ_mul_left_image : (⋃ a ∈ s, (· * ·) a '' t) = s * t :=
  unionᵢ_image_left _
#align set.Union_mul_left_image Set.unionᵢ_mul_left_image
#align set.Union_add_left_image Set.unionᵢ_add_left_image
-/

#print Set.unionᵢ_mul_right_image /-
@[to_additive]
theorem unionᵢ_mul_right_image : (⋃ a ∈ t, (· * a) '' s) = s * t :=
  unionᵢ_image_right _
#align set.Union_mul_right_image Set.unionᵢ_mul_right_image
#align set.Union_add_right_image Set.unionᵢ_add_right_image
-/

/- warning: set.Union_mul -> Set.unionᵢ_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Mul.{u1} α] (s : ι -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Mul.{u2} α] (s : ι -> (Set.{u2} α)) (t : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Union_mul Set.unionᵢ_mulₓ'. -/
@[to_additive]
theorem unionᵢ_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_unionᵢ_left _ _ _
#align set.Union_mul Set.unionᵢ_mul
#align set.Union_add Set.unionᵢ_add

/- warning: set.mul_Union -> Set.mul_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Mul.{u1} α] (s : Set.{u1} α) (t : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Mul.{u2} α] (s : Set.{u2} α) (t : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) s (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.mul_Union Set.mul_unionᵢₓ'. -/
@[to_additive]
theorem mul_unionᵢ (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_unionᵢ_right _ _ _
#align set.mul_Union Set.mul_unionᵢ
#align set.add_Union Set.add_unionᵢ

/- warning: set.Union₂_mul -> Set.unionᵢ₂_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Mul.{u1} α] (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Mul.{u3} α] (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), Eq.{succ u3} (Set.{u3} α) (HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Union₂_mul Set.unionᵢ₂_mulₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem unionᵢ₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_unionᵢ₂_left _ _ _
#align set.Union₂_mul Set.unionᵢ₂_mul
#align set.Union₂_add Set.unionᵢ₂_add

/- warning: set.mul_Union₂ -> Set.mul_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Mul.{u1} α] (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Mul.{u3} α] (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) s (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.mul_Union₂ Set.mul_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_unionᵢ₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_unionᵢ₂_right _ _ _
#align set.mul_Union₂ Set.mul_unionᵢ₂
#align set.add_Union₂ Set.add_unionᵢ₂

/- warning: set.Inter_mul_subset -> Set.interᵢ_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Mul.{u1} α] (s : ι -> (Set.{u1} α)) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Mul.{u2} α] (s : ι -> (Set.{u2} α)) (t : Set.{u2} α), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Inter_mul_subset Set.interᵢ_mul_subsetₓ'. -/
@[to_additive]
theorem interᵢ_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  image2_interᵢ_subset_left _ _ _
#align set.Inter_mul_subset Set.interᵢ_mul_subset
#align set.Inter_add_subset Set.interᵢ_add_subset

/- warning: set.mul_Inter_subset -> Set.mul_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Mul.{u1} α] (s : Set.{u1} α) (t : ι -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Mul.{u2} α] (s : Set.{u2} α) (t : ι -> (Set.{u2} α)), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) s (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => HMul.hMul.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHMul.{u2} (Set.{u2} α) (Set.mul.{u2} α _inst_1)) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.mul_Inter_subset Set.mul_interᵢ_subsetₓ'. -/
@[to_additive]
theorem mul_interᵢ_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_interᵢ_subset_right _ _ _
#align set.mul_Inter_subset Set.mul_interᵢ_subset
#align set.add_Inter_subset Set.add_interᵢ_subset

/- warning: set.Inter₂_mul_subset -> Set.interᵢ₂_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Mul.{u1} α] (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Mul.{u3} α] (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_mul_subset Set.interᵢ₂_mul_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem interᵢ₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_interᵢ₂_subset_left _ _ _
#align set.Inter₂_mul_subset Set.interᵢ₂_mul_subset
#align set.Inter₂_add_subset Set.interᵢ₂_add_subset

/- warning: set.mul_Inter₂_subset -> Set.mul_interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Mul.{u1} α] (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α _inst_1)) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Mul.{u3} α] (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) s (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HMul.hMul.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHMul.{u3} (Set.{u3} α) (Set.mul.{u3} α _inst_1)) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.mul_Inter₂_subset Set.mul_interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem mul_interᵢ₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_interᵢ₂_subset_right _ _ _
#align set.mul_Inter₂_subset Set.mul_interᵢ₂_subset
#align set.add_Inter₂_subset Set.add_interᵢ₂_subset

#print Set.singletonMulHom /-
/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singletonMulHom : α →ₙ* Set α :=
  ⟨singleton, fun a b => singleton_mul_singleton.symm⟩
#align set.singleton_mul_hom Set.singletonMulHom
#align set.singleton_add_hom Set.singletonAddHom
-/

#print Set.coe_singletonMulHom /-
@[simp, to_additive]
theorem coe_singletonMulHom : (singletonMulHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_mul_hom Set.coe_singletonMulHom
#align set.coe_singleton_add_hom Set.coe_singletonAddHom
-/

#print Set.singletonMulHom_apply /-
@[simp, to_additive]
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl
#align set.singleton_mul_hom_apply Set.singletonMulHom_apply
#align set.singleton_add_hom_apply Set.singletonAddHom_apply
-/

open MulOpposite

#print Set.image_op_mul /-
@[simp, to_additive]
theorem image_op_mul : op '' (s * t) = op '' t * op '' s :=
  image_image2_antidistrib op_mul
#align set.image_op_mul Set.image_op_mul
#align set.image_op_add Set.image_op_add
-/

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort _} {κ : ι → Sort _} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

#print Set.div /-
/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive
      "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in\nlocale `pointwise`."]
protected def div : Div (Set α) :=
  ⟨image2 (· / ·)⟩
#align set.has_div Set.div
#align set.has_sub Set.sub
-/

scoped[Pointwise] attribute [instance] Set.div Set.sub

#print Set.image2_div /-
@[simp, to_additive]
theorem image2_div : image2 Div.div s t = s / t :=
  rfl
#align set.image2_div Set.image2_div
#align set.image2_sub Set.image2_sub
-/

#print Set.mem_div /-
@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a :=
  Iff.rfl
#align set.mem_div Set.mem_div
#align set.mem_sub Set.mem_sub
-/

#print Set.div_mem_div /-
@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image2_of_mem
#align set.div_mem_div Set.div_mem_div
#align set.sub_mem_sub Set.sub_mem_sub
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.image_div_prod /-
@[to_additive add_image_prod]
theorem image_div_prod : (fun x : α × α => x.fst / x.snd) '' s ×ˢ t = s / t :=
  image_prod _
#align set.image_div_prod Set.image_div_prod
#align set.sub_image_prod Set.sub_image_prod
-/

#print Set.empty_div /-
@[simp, to_additive]
theorem empty_div : ∅ / s = ∅ :=
  image2_empty_left
#align set.empty_div Set.empty_div
#align set.empty_sub Set.empty_sub
-/

#print Set.div_empty /-
@[simp, to_additive]
theorem div_empty : s / ∅ = ∅ :=
  image2_empty_right
#align set.div_empty Set.div_empty
#align set.sub_empty Set.sub_empty
-/

#print Set.div_eq_empty /-
@[simp, to_additive]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.div_eq_empty Set.div_eq_empty
#align set.sub_eq_empty Set.sub_eq_empty
-/

#print Set.div_nonempty /-
@[simp, to_additive]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.div_nonempty Set.div_nonempty
#align set.sub_nonempty Set.sub_nonempty
-/

#print Set.Nonempty.div /-
@[to_additive]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image2
#align set.nonempty.div Set.Nonempty.div
#align set.nonempty.sub Set.Nonempty.sub
-/

#print Set.Nonempty.of_div_left /-
@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_div_left Set.Nonempty.of_div_left
#align set.nonempty.of_sub_left Set.Nonempty.of_sub_left
-/

#print Set.Nonempty.of_div_right /-
@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_div_right Set.Nonempty.of_div_right
#align set.nonempty.of_sub_right Set.Nonempty.of_sub_right
-/

#print Set.div_singleton /-
@[simp, to_additive]
theorem div_singleton : s / {b} = (· / b) '' s :=
  image2_singleton_right
#align set.div_singleton Set.div_singleton
#align set.sub_singleton Set.sub_singleton
-/

#print Set.singleton_div /-
@[simp, to_additive]
theorem singleton_div : {a} / t = (· / ·) a '' t :=
  image2_singleton_left
#align set.singleton_div Set.singleton_div
#align set.singleton_sub Set.singleton_sub
-/

#print Set.singleton_div_singleton /-
@[simp, to_additive]
theorem singleton_div_singleton : ({a} : Set α) / {b} = {a / b} :=
  image2_singleton
#align set.singleton_div_singleton Set.singleton_div_singleton
#align set.singleton_sub_singleton Set.singleton_sub_singleton
-/

#print Set.div_subset_div /-
@[to_additive, mono]
theorem div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ :=
  image2_subset
#align set.div_subset_div Set.div_subset_div
#align set.sub_subset_sub Set.sub_subset_sub
-/

#print Set.div_subset_div_left /-
@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image2_subset_left
#align set.div_subset_div_left Set.div_subset_div_left
#align set.sub_subset_sub_left Set.sub_subset_sub_left
-/

#print Set.div_subset_div_right /-
@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image2_subset_right
#align set.div_subset_div_right Set.div_subset_div_right
#align set.sub_subset_sub_right Set.sub_subset_sub_right
-/

#print Set.div_subset_iff /-
@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image2_subset_iff
#align set.div_subset_iff Set.div_subset_iff
#align set.sub_subset_iff Set.sub_subset_iff
-/

attribute [mono] sub_subset_sub

/- warning: set.union_div -> Set.union_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₁ t) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₁ t) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_div Set.union_divₓ'. -/
@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image2_union_left
#align set.union_div Set.union_div
#align set.union_sub Set.union_sub

/- warning: set.div_union -> Set.div_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₁) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₁) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₂))
Case conversion may be inaccurate. Consider using '#align set.div_union Set.div_unionₓ'. -/
@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image2_union_right
#align set.div_union Set.div_union
#align set.sub_union Set.sub_union

/- warning: set.inter_div_subset -> Set.inter_div_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₁ t) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₁ t) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.inter_div_subset Set.inter_div_subsetₓ'. -/
@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image2_inter_subset_left
#align set.inter_div_subset Set.inter_div_subset
#align set.inter_sub_subset Set.inter_sub_subset

/- warning: set.div_inter_subset -> Set.div_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₁) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Div.{u1} α] {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₁) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s t₂))
Case conversion may be inaccurate. Consider using '#align set.div_inter_subset Set.div_inter_subsetₓ'. -/
@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image2_inter_subset_right
#align set.div_inter_subset Set.div_inter_subset
#align set.sub_inter_subset Set.sub_inter_subset

#print Set.unionᵢ_div_left_image /-
@[to_additive]
theorem unionᵢ_div_left_image : (⋃ a ∈ s, (· / ·) a '' t) = s / t :=
  unionᵢ_image_left _
#align set.Union_div_left_image Set.unionᵢ_div_left_image
#align set.Union_sub_left_image Set.unionᵢ_sub_left_image
-/

#print Set.unionᵢ_div_right_image /-
@[to_additive]
theorem unionᵢ_div_right_image : (⋃ a ∈ t, (· / a) '' s) = s / t :=
  unionᵢ_image_right _
#align set.Union_div_right_image Set.unionᵢ_div_right_image
#align set.Union_sub_right_image Set.unionᵢ_sub_right_image
-/

/- warning: set.Union_div -> Set.unionᵢ_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Div.{u1} α] (s : ι -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Div.{u2} α] (s : ι -> (Set.{u2} α)) (t : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Union_div Set.unionᵢ_divₓ'. -/
@[to_additive]
theorem unionᵢ_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_unionᵢ_left _ _ _
#align set.Union_div Set.unionᵢ_div
#align set.Union_sub Set.unionᵢ_sub

/- warning: set.div_Union -> Set.div_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Div.{u1} α] (s : Set.{u1} α) (t : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Div.{u2} α] (s : Set.{u2} α) (t : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) s (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.div_Union Set.div_unionᵢₓ'. -/
@[to_additive]
theorem div_unionᵢ (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_unionᵢ_right _ _ _
#align set.div_Union Set.div_unionᵢ
#align set.sub_Union Set.sub_unionᵢ

/- warning: set.Union₂_div -> Set.unionᵢ₂_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Div.{u1} α] (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Div.{u3} α] (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), Eq.{succ u3} (Set.{u3} α) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Union₂_div Set.unionᵢ₂_divₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem unionᵢ₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_unionᵢ₂_left _ _ _
#align set.Union₂_div Set.unionᵢ₂_div
#align set.Union₂_sub Set.unionᵢ₂_sub

/- warning: set.div_Union₂ -> Set.div_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Div.{u1} α] (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Div.{u3} α] (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), Eq.{succ u3} (Set.{u3} α) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) s (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.div_Union₂ Set.div_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_unionᵢ₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_unionᵢ₂_right _ _ _
#align set.div_Union₂ Set.div_unionᵢ₂
#align set.sub_Union₂ Set.sub_unionᵢ₂

/- warning: set.Inter_div_subset -> Set.interᵢ_div_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Div.{u1} α] (s : ι -> (Set.{u1} α)) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Div.{u2} α] (s : ι -> (Set.{u2} α)) (t : Set.{u2} α), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Inter_div_subset Set.interᵢ_div_subsetₓ'. -/
@[to_additive]
theorem interᵢ_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_interᵢ_subset_left _ _ _
#align set.Inter_div_subset Set.interᵢ_div_subset
#align set.Inter_sub_subset Set.interᵢ_sub_subset

/- warning: set.div_Inter_subset -> Set.div_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : Div.{u1} α] (s : Set.{u1} α) (t : ι -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (t i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : Div.{u2} α] (s : Set.{u2} α) (t : ι -> (Set.{u2} α)), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) s (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α _inst_1)) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.div_Inter_subset Set.div_interᵢ_subsetₓ'. -/
@[to_additive]
theorem div_interᵢ_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_interᵢ_subset_right _ _ _
#align set.div_Inter_subset Set.div_interᵢ_subset
#align set.sub_Inter_subset Set.sub_interᵢ_subset

/- warning: set.Inter₂_div_subset -> Set.interᵢ₂_div_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Div.{u1} α] (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Div.{u3} α] (s : forall (i : ι), (κ i) -> (Set.{u3} α)) (t : Set.{u3} α), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_div_subset Set.interᵢ₂_div_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem interᵢ₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_interᵢ₂_subset_left _ _ _
#align set.Inter₂_div_subset Set.interᵢ₂_div_subset
#align set.Inter₂_sub_subset Set.interᵢ₂_sub_subset

/- warning: set.div_Inter₂_subset -> Set.div_interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : Div.{u1} α] (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u1} α)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => Set.interᵢ.{u1, u3} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α _inst_1)) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : Div.{u3} α] (s : Set.{u3} α) (t : forall (i : ι), (κ i) -> (Set.{u3} α)), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) s (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => HDiv.hDiv.{u3, u3, u3} (Set.{u3} α) (Set.{u3} α) (Set.{u3} α) (instHDiv.{u3} (Set.{u3} α) (Set.div.{u3} α _inst_1)) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.div_Inter₂_subset Set.div_interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem div_interᵢ₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_interᵢ₂_subset_right _ _ _
#align set.div_Inter₂_subset Set.div_interᵢ₂_subset
#align set.sub_Inter₂_subset Set.sub_interᵢ₂_subset

end Div

open Pointwise

#print Set.NSMul /-
/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action].-/
protected def NSMul [Zero α] [Add α] : SMul ℕ (Set α) :=
  ⟨nsmulRec⟩
#align set.has_nsmul Set.NSMul
-/

#print Set.NPow /-
/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def NPow [One α] [Mul α] : Pow (Set α) ℕ :=
  ⟨fun s n => npowRec n s⟩
#align set.has_npow Set.NPow
#align set.has_nsmul Set.NSMul
-/

#print Set.ZSMul /-
/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def ZSMul [Zero α] [Add α] [Neg α] : SMul ℤ (Set α) :=
  ⟨zsmulRec⟩
#align set.has_zsmul Set.ZSMul
-/

#print Set.ZPow /-
/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive]
protected def ZPow [One α] [Mul α] [Inv α] : Pow (Set α) ℤ :=
  ⟨fun s n => zpowRec n s⟩
#align set.has_zpow Set.ZPow
#align set.has_zsmul Set.ZSMul
-/

scoped[Pointwise] attribute [instance] Set.NSMul Set.NPow Set.ZSMul Set.ZPow

#print Set.semigroup /-
/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [Semigroup α] : Semigroup (Set α) :=
  { Set.mul with mul_assoc := fun _ _ _ => image2_assoc mul_assoc }
#align set.semigroup Set.semigroup
#align set.add_semigroup Set.addSemigroup
-/

#print Set.commSemigroup /-
/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def commSemigroup [CommSemigroup α] : CommSemigroup (Set α) :=
  { Set.semigroup with mul_comm := fun s t => image2_comm mul_comm }
#align set.comm_semigroup Set.commSemigroup
#align set.add_comm_semigroup Set.addCommSemigroup
-/

section MulOneClass

variable [MulOneClass α]

#print Set.mulOneClass /-
/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Set α) :=
  { Set.one,
    Set.mul with
    mul_one := fun s => by simp only [← singleton_one, mul_singleton, mul_one, image_id']
    one_mul := fun s => by simp only [← singleton_one, singleton_mul, one_mul, image_id'] }
#align set.mul_one_class Set.mulOneClass
#align set.add_zero_class Set.addZeroClass
-/

scoped[Pointwise]
  attribute [instance]
    Set.mulOneClass Set.addZeroClass Set.semigroup Set.addSemigroup Set.commSemigroup Set.addCommSemigroup

/- warning: set.subset_mul_left -> Set.subset_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] (s : Set.{u1} α) {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α _inst_1))) s t))
Case conversion may be inaccurate. Consider using '#align set.subset_mul_left Set.subset_mul_leftₓ'. -/
@[to_additive]
theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx =>
  ⟨x, 1, hx, ht, mul_one _⟩
#align set.subset_mul_left Set.subset_mul_left
#align set.subset_add_left Set.subset_add_left

/- warning: set.subset_mul_right -> Set.subset_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] {s : Set.{u1} α} (t : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α _inst_1)))) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α _inst_1))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] {s : Set.{u1} α} (t : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (MulOneClass.toOne.{u1} α _inst_1))) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α _inst_1))) s t))
Case conversion may be inaccurate. Consider using '#align set.subset_mul_right Set.subset_mul_rightₓ'. -/
@[to_additive]
theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, x, hs, hx, one_mul _⟩
#align set.subset_mul_right Set.subset_mul_right
#align set.subset_add_right Set.subset_add_right

#print Set.singletonMonoidHom /-
/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singletonMonoidHom : α →* Set α :=
  { singletonMulHom, singletonOneHom with }
#align set.singleton_monoid_hom Set.singletonMonoidHom
#align set.singleton_add_monoid_hom Set.singletonAddMonoidHom
-/

/- warning: set.coe_singleton_monoid_hom -> Set.coe_singletonMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α], Eq.{succ u1} ((fun (_x : MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) => α -> (Set.{u1} α)) (Set.singletonMonoidHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) (fun (_x : MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) => α -> (Set.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) (Set.singletonMonoidHom.{u1} α _inst_1)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α], Eq.{succ u1} (forall (a : α), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Set.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Set.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) α (Set.{u1} α) (MulOneClass.toMul.{u1} α _inst_1) (MulOneClass.toMul.{u1} (Set.{u1} α) (Set.mulOneClass.{u1} α _inst_1)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1) (MonoidHom.monoidHomClass.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)))) (Set.singletonMonoidHom.{u1} α _inst_1)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.coe_singleton_monoid_hom Set.coe_singletonMonoidHomₓ'. -/
@[simp, to_additive]
theorem coe_singletonMonoidHom : (singletonMonoidHom : α → Set α) = singleton :=
  rfl
#align set.coe_singleton_monoid_hom Set.coe_singletonMonoidHom
#align set.coe_singleton_add_monoid_hom Set.coe_singletonAddMonoidHom

/- warning: set.singleton_monoid_hom_apply -> Set.singletonMonoidHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] (a : α), Eq.{succ u1} (Set.{u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) (fun (_x : MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) => α -> (Set.{u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) (Set.singletonMonoidHom.{u1} α _inst_1) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulOneClass.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Set.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Set.{u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) α (Set.{u1} α) (MulOneClass.toMul.{u1} α _inst_1) (MulOneClass.toMul.{u1} (Set.{u1} α) (Set.mulOneClass.{u1} α _inst_1)) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)) α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1) (MonoidHom.monoidHomClass.{u1, u1} α (Set.{u1} α) _inst_1 (Set.mulOneClass.{u1} α _inst_1)))) (Set.singletonMonoidHom.{u1} α _inst_1) a) (Singleton.singleton.{u1, u1} α ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => Set.{u1} α) a) (Set.instSingletonSet.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align set.singleton_monoid_hom_apply Set.singletonMonoidHom_applyₓ'. -/
@[simp, to_additive]
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl
#align set.singleton_monoid_hom_apply Set.singletonMonoidHom_apply
#align set.singleton_add_monoid_hom_apply Set.singletonAddMonoidHom_apply

end MulOneClass

section Monoid

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

#print Set.monoid /-
/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : Monoid (Set α) :=
  { Set.semigroup, Set.mulOneClass, Set.NPow with }
#align set.monoid Set.monoid
#align set.add_monoid Set.addMonoid
-/

scoped[Pointwise] attribute [instance] Set.monoid Set.addMonoid

/- warning: set.pow_mem_pow -> Set.pow_mem_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {a : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α _inst_1)) a n) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n))
Case conversion may be inaccurate. Consider using '#align set.pow_mem_pow Set.pow_mem_powₓ'. -/
@[to_additive]
theorem pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
  | 0 => by
    rw [pow_zero]
    exact one_mem_one
  | n + 1 => by
    rw [pow_succ]
    exact mul_mem_mul ha (pow_mem_pow _)
#align set.pow_mem_pow Set.pow_mem_pow
#align set.nsmul_mem_nsmul Set.nsmul_mem_nsmul

/- warning: set.pow_subset_pow -> Set.pow_subset_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) t n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (forall (n : Nat), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) t n))
Case conversion may be inaccurate. Consider using '#align set.pow_subset_pow Set.pow_subset_powₓ'. -/
@[to_additive]
theorem pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
  | 0 => by
    rw [pow_zero]
    exact subset.rfl
  | n + 1 => by
    rw [pow_succ]
    exact mul_subset_mul hst (pow_subset_pow _)
#align set.pow_subset_pow Set.pow_subset_pow
#align set.nsmul_subset_nsmul Set.nsmul_subset_nsmul

/- warning: set.pow_subset_pow_of_one_mem -> Set.pow_subset_pow_of_one_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {m : Nat} {n : Nat}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) s) -> (LE.le.{0} Nat Nat.hasLe m n) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s m) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α} {m : Nat} {n : Nat}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) s) -> (LE.le.{0} Nat instLENat m n) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s m) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s n))
Case conversion may be inaccurate. Consider using '#align set.pow_subset_pow_of_one_mem Set.pow_subset_pow_of_one_memₓ'. -/
@[to_additive]
theorem pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n :=
  by
  refine' Nat.le_induction _ (fun n h ih => _) _
  · exact subset.rfl
  · rw [pow_succ]
    exact ih.trans (subset_mul_right _ hs)
#align set.pow_subset_pow_of_one_mem Set.pow_subset_pow_of_one_mem
#align set.nsmul_subset_nsmul_of_zero_mem Set.nsmul_subset_nsmul_of_zero_mem

/- warning: set.empty_pow -> Set.empty_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Set.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) n) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Set.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) n) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.empty_pow Set.empty_powₓ'. -/
@[simp, to_additive]
theorem empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : Set α) ^ n = ∅ := by
  rw [← tsub_add_cancel_of_le (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn), pow_succ, empty_mul]
#align set.empty_pow Set.empty_pow
#align set.empty_nsmul Set.empty_nsmul

/- warning: set.mul_univ_of_one_mem -> Set.mul_univ_of_one_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s (Set.univ.{u1} α)) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {s : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s (Set.univ.{u1} α)) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.mul_univ_of_one_mem Set.mul_univ_of_one_memₓ'. -/
@[to_additive]
theorem mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩
#align set.mul_univ_of_one_mem Set.mul_univ_of_one_mem
#align set.add_univ_of_zero_mem Set.add_univ_of_zero_mem

/- warning: set.univ_mul_of_one_mem -> Set.univ_mul_of_one_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))))) t) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Set.univ.{u1} α) t) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α _inst_1))) t) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Set.univ.{u1} α) t) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.univ_mul_of_one_mem Set.univ_mul_of_one_memₓ'. -/
@[to_additive]
theorem univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun a => mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩
#align set.univ_mul_of_one_mem Set.univ_mul_of_one_mem
#align set.univ_add_of_zero_mem Set.univ_add_of_zero_mem

/- warning: set.univ_mul_univ -> Set.univ_mul_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Set.univ.{u1} α) (Set.univ.{u1} α)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α], Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Set.univ.{u1} α) (Set.univ.{u1} α)) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.univ_mul_univ Set.univ_mul_univₓ'. -/
@[simp, to_additive]
theorem univ_mul_univ : (univ : Set α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _
#align set.univ_mul_univ Set.univ_mul_univ
#align set.univ_add_univ Set.univ_add_univ

/- warning: set.nsmul_univ -> Set.nsmul_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : AddMonoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Set.{u1} α) (SMul.smul.{0, u1} Nat (Set.{u1} α) (Set.NSMul.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_2)) (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_2))) n (Set.univ.{u1} α)) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : AddMonoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Set.{u1} α) (HSMul.hSMul.{0, u1, u1} Nat (Set.{u1} α) (Set.{u1} α) (instHSMul.{0, u1} Nat (Set.{u1} α) (Set.NSMul.{u1} α (AddMonoid.toZero.{u1} α _inst_2) (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_2)))) n (Set.univ.{u1} α)) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.nsmul_univ Set.nsmul_univₓ'. -/
--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp]
theorem nsmul_univ {α : Type _} [AddMonoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : Set α) = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => one_nsmul _
  | n + 2 => fun _ => by rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ]
#align set.nsmul_univ Set.nsmul_univ

/- warning: set.univ_pow -> Set.univ_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Set.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Set.univ.{u1} α) n) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {n : Nat}, (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Set.{u1} α) (HPow.hPow.{u1, 0, u1} (Set.{u1} α) Nat (Set.{u1} α) (instHPow.{u1, 0} (Set.{u1} α) Nat (Set.NPow.{u1} α (Monoid.toOne.{u1} α _inst_1) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Set.univ.{u1} α) n) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.univ_pow Set.univ_powₓ'. -/
@[simp, to_additive nsmul_univ]
theorem univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : Set α) ^ n = univ
  | 0 => fun h => (h rfl).elim
  | 1 => fun _ => pow_one _
  | n + 2 => fun _ => by rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ]
#align set.univ_pow Set.univ_pow
#align set.nsmul_univ Set.nsmul_univ

#print IsUnit.set /-
@[to_additive]
protected theorem IsUnit.set : IsUnit a → IsUnit ({a} : Set α) :=
  IsUnit.map (singletonMonoidHom : α →* Set α)
#align is_unit.set IsUnit.set
#align is_add_unit.set IsAddUnit.set
-/

end Monoid

#print Set.commMonoid /-
/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def commMonoid [CommMonoid α] : CommMonoid (Set α) :=
  { Set.monoid, Set.commSemigroup with }
#align set.comm_monoid Set.commMonoid
#align set.add_comm_monoid Set.addCommMonoid
-/

scoped[Pointwise] attribute [instance] Set.commMonoid Set.addCommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Set α}

/- warning: set.mul_eq_one_iff -> Set.mul_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) s t) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (And (Eq.{succ u1} (Set.{u1} α) t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionMonoid.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1)))))) s t) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (And (Eq.{succ u1} (Set.{u1} α) t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (DivisionMonoid.toDivInvMonoid.{u1} α _inst_1))))) a b) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align set.mul_eq_one_iff Set.mul_eq_one_iffₓ'. -/
@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 :=
  by
  refine' ⟨fun h => _, _⟩
  · have hst : (s * t).Nonempty := h.symm.subst one_nonempty
    obtain ⟨a, ha⟩ := hst.of_image2_left
    obtain ⟨b, hb⟩ := hst.of_image2_right
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) := fun a b ha hb =>
      h.subset <| mem_image2_of_mem ha hb
    refine' ⟨a, b, _, _, H ha hb⟩ <;> refine' eq_singleton_iff_unique_mem.2 ⟨‹_›, fun x hx => _⟩
    · exact (eq_inv_of_mul_eq_one_left <| H hx hb).trans (inv_eq_of_mul_eq_one_left <| H ha hb)
    · exact (eq_inv_of_mul_eq_one_right <| H ha hx).trans (inv_eq_of_mul_eq_one_right <| H ha hb)
  · rintro ⟨b, c, rfl, rfl, h⟩
    rw [singleton_mul_singleton, h, singleton_one]
#align set.mul_eq_one_iff Set.mul_eq_one_iff
#align set.add_eq_zero_iff Set.add_eq_zero_iff

#print Set.divisionMonoid /-
/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`set α` is a subtraction monoid under pointwise operations if `α` is."]
protected def divisionMonoid : DivisionMonoid (Set α) :=
  { Set.monoid, Set.hasInvolutiveInv, Set.div,
    Set.ZPow with
    mul_inv_rev := fun s t => by
      simp_rw [← image_inv]
      exact image_image2_antidistrib mul_inv_rev
    inv_eq_of_mul := fun s t h =>
      by
      obtain ⟨a, b, rfl, rfl, hab⟩ := Set.mul_eq_one_iff.1 h
      rw [inv_singleton, inv_eq_of_mul_eq_one_right hab]
    div_eq_mul_inv := fun s t => by
      rw [← image_id (s / t), ← image_inv]
      exact image_image2_distrib_right div_eq_mul_inv }
#align set.division_monoid Set.divisionMonoid
#align set.subtraction_monoid Set.subtractionMonoid
-/

#print Set.isUnit_iff /-
@[simp, to_additive]
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a :=
  by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Set.mul_eq_one_iff.1 u.mul_inv
    refine' ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.set
#align set.is_unit_iff Set.isUnit_iff
#align set.is_add_unit_iff Set.isAddUnit_iff
-/

end DivisionMonoid

#print Set.divisionCommMonoid /-
/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive SubtractionCommMonoid
      "`set α` is a commutative subtraction monoid under pointwise\noperations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Set α) :=
  { Set.divisionMonoid, Set.commSemigroup with }
#align set.division_comm_monoid Set.divisionCommMonoid
#align set.subtraction_comm_monoid Set.subtractionCommMonoid
-/

#print Set.hasDistribNeg /-
/-- `set α` has distributive negation if `α` has. -/
protected def hasDistribNeg [Mul α] [HasDistribNeg α] : HasDistribNeg (Set α) :=
  {
    Set.hasInvolutiveNeg with
    neg_mul := fun _ _ => by
      simp_rw [← image_neg]
      exact image2_image_left_comm neg_mul
    mul_neg := fun _ _ => by
      simp_rw [← image_neg]
      exact image_image2_right_comm mul_neg }
#align set.has_distrib_neg Set.hasDistribNeg
-/

scoped[Pointwise]
  attribute [instance]
    Set.divisionMonoid Set.subtractionMonoid Set.divisionCommMonoid Set.subtractionCommMonoid Set.hasDistribNeg

section Distrib

variable [Distrib α] (s t u : Set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/


/- warning: set.mul_add_subset -> Set.mul_add_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Distrib.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toHasMul.{u1} α _inst_1))) s (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toHasAdd.{u1} α _inst_1))) t u)) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toHasAdd.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toHasMul.{u1} α _inst_1))) s t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toHasMul.{u1} α _inst_1))) s u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Distrib.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toMul.{u1} α _inst_1))) s (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toAdd.{u1} α _inst_1))) t u)) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toAdd.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toMul.{u1} α _inst_1))) s t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toMul.{u1} α _inst_1))) s u))
Case conversion may be inaccurate. Consider using '#align set.mul_add_subset Set.mul_add_subsetₓ'. -/
theorem mul_add_subset : s * (t + u) ⊆ s * t + s * u :=
  image2_distrib_subset_left mul_add
#align set.mul_add_subset Set.mul_add_subset

/- warning: set.add_mul_subset -> Set.add_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Distrib.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toHasMul.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toHasAdd.{u1} α _inst_1))) s t) u) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toHasAdd.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toHasMul.{u1} α _inst_1))) s u) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toHasMul.{u1} α _inst_1))) t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Distrib.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toMul.{u1} α _inst_1))) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toAdd.{u1} α _inst_1))) s t) u) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (Distrib.toAdd.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toMul.{u1} α _inst_1))) s u) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Distrib.toMul.{u1} α _inst_1))) t u))
Case conversion may be inaccurate. Consider using '#align set.add_mul_subset Set.add_mul_subsetₓ'. -/
theorem add_mul_subset : (s + t) * u ⊆ s * u + t * u :=
  image2_distrib_subset_right add_mul
#align set.add_mul_subset Set.add_mul_subset

end Distrib

section MulZeroClass

variable [MulZeroClass α] {s t : Set α}

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/


/- warning: set.mul_zero_subset -> Set.mul_zero_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_1))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toMul.{u1} α _inst_1))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align set.mul_zero_subset Set.mul_zero_subsetₓ'. -/
theorem mul_zero_subset (s : Set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
#align set.mul_zero_subset Set.mul_zero_subset

/- warning: set.zero_mul_subset -> Set.zero_mul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_1))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1))))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toMul.{u1} α _inst_1))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1)))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align set.zero_mul_subset Set.zero_mul_subsetₓ'. -/
theorem zero_mul_subset (s : Set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]
#align set.zero_mul_subset Set.zero_mul_subset

/- warning: set.nonempty.mul_zero -> Set.Nonempty.mul_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_1))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toMul.{u1} α _inst_1))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.mul_zero Set.Nonempty.mul_zeroₓ'. -/
theorem Nonempty.mul_zero (hs : s.Nonempty) : s * 0 = 0 :=
  s.mul_zero_subset.antisymm <| by simpa [mem_mul] using hs
#align set.nonempty.mul_zero Set.Nonempty.mul_zero

/- warning: set.nonempty.zero_mul -> Set.Nonempty.zero_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toHasMul.{u1} α _inst_1))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1))))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MulZeroClass.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulZeroClass.toMul.{u1} α _inst_1))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1)))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.zero_mul Set.Nonempty.zero_mulₓ'. -/
theorem Nonempty.zero_mul (hs : s.Nonempty) : 0 * s = 0 :=
  s.zero_mul_subset.antisymm <| by simpa [mem_mul] using hs
#align set.nonempty.zero_mul Set.Nonempty.zero_mul

end MulZeroClass

section Group

variable [Group α] {s t : Set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/


/- warning: set.one_mem_div_iff -> Set.one_mem_div_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s t)) (Not (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s t)) (Not (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t))
Case conversion may be inaccurate. Consider using '#align set.one_mem_div_iff Set.one_mem_div_iffₓ'. -/
@[simp, to_additive]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, Set.Nonempty]
#align set.one_mem_div_iff Set.one_mem_div_iff
#align set.zero_mem_sub_iff Set.zero_mem_sub_iff

/- warning: set.not_one_mem_div_iff -> Set.not_one_mem_div_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s t))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s t))) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t)
Case conversion may be inaccurate. Consider using '#align set.not_one_mem_div_iff Set.not_one_mem_div_iffₓ'. -/
@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left
#align set.not_one_mem_div_iff Set.not_one_mem_div_iff
#align set.not_zero_mem_sub_iff Set.not_zero_mem_sub_iff

/- warning: disjoint.one_not_mem_div_set -> Disjoint.one_not_mem_div_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s t)))
Case conversion may be inaccurate. Consider using '#align disjoint.one_not_mem_div_set Disjoint.one_not_mem_div_setₓ'. -/
alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set
#align disjoint.one_not_mem_div_set Disjoint.one_not_mem_div_set

attribute [to_additive] Disjoint.one_not_mem_div_set

/- warning: set.nonempty.one_mem_div -> Set.Nonempty.one_mem_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) s s))
Case conversion may be inaccurate. Consider using '#align set.nonempty.one_mem_div Set.Nonempty.one_mem_divₓ'. -/
@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, a, ha, ha, div_self' _⟩
#align set.nonempty.one_mem_div Set.Nonempty.one_mem_div
#align set.nonempty.zero_mem_sub Set.Nonempty.zero_mem_sub

#print Set.isUnit_singleton /-
@[to_additive]
theorem isUnit_singleton (a : α) : IsUnit ({a} : Set α) :=
  (Group.isUnit a).Set
#align set.is_unit_singleton Set.isUnit_singleton
#align set.is_add_unit_singleton Set.isAddUnit_singleton
-/

#print Set.isUnit_iff_singleton /-
@[simp, to_additive]
theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [is_unit_iff, Group.isUnit, and_true_iff]
#align set.is_unit_iff_singleton Set.isUnit_iff_singleton
#align set.is_add_unit_iff_singleton Set.isAddUnit_iff_singleton
-/

/- warning: set.image_mul_left -> Set.image_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) t) (Set.preimage.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9146 : α) (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9148 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9146 x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9148) a) t) (Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9166 : α) (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9168 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9166 x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9168) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)) t)
Case conversion may be inaccurate. Consider using '#align set.image_mul_left Set.image_mul_leftₓ'. -/
@[simp, to_additive]
theorem image_mul_left : (· * ·) a '' t = (· * ·) a⁻¹ ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
#align set.image_mul_left Set.image_mul_left
#align set.image_add_left Set.image_add_left

/- warning: set.image_mul_right -> Set.image_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) t) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) t) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) t)
Case conversion may be inaccurate. Consider using '#align set.image_mul_right Set.image_mul_rightₓ'. -/
@[simp, to_additive]
theorem image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t := by
  rw [image_eq_preimage_of_inverse] <;> intro c <;> simp
#align set.image_mul_right Set.image_mul_right
#align set.image_add_right Set.image_add_right

/- warning: set.image_mul_left' -> Set.image_mul_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) t) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) t) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b) t)
Case conversion may be inaccurate. Consider using '#align set.image_mul_left' Set.image_mul_left'ₓ'. -/
@[to_additive]
theorem image_mul_left' : (fun b => a⁻¹ * b) '' t = (fun b => a * b) ⁻¹' t := by simp
#align set.image_mul_left' Set.image_mul_left'
#align set.image_add_left' Set.image_add_left'

/- warning: set.image_mul_right' -> Set.image_mul_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) t) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) t) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) t)
Case conversion may be inaccurate. Consider using '#align set.image_mul_right' Set.image_mul_right'ₓ'. -/
@[to_additive]
theorem image_mul_right' : (· * b⁻¹) '' t = (· * b) ⁻¹' t := by simp
#align set.image_mul_right' Set.image_mul_right'
#align set.image_add_right' Set.image_add_right'

/- warning: set.preimage_mul_left_singleton -> Set.preimage_mul_left_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9475 : α) (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9477 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9475 x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9477) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b))
Case conversion may be inaccurate. Consider using '#align set.preimage_mul_left_singleton Set.preimage_mul_left_singletonₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_singleton : (· * ·) a ⁻¹' {b} = {a⁻¹ * b} := by
  rw [← image_mul_left', image_singleton]
#align set.preimage_mul_left_singleton Set.preimage_mul_left_singleton
#align set.preimage_add_left_singleton Set.preimage_add_left_singleton

/- warning: set.preimage_mul_right_singleton -> Set.preimage_mul_right_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α} {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) b (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a)))
Case conversion may be inaccurate. Consider using '#align set.preimage_mul_right_singleton Set.preimage_mul_right_singletonₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_singleton : (· * a) ⁻¹' {b} = {b * a⁻¹} := by
  rw [← image_mul_right', image_singleton]
#align set.preimage_mul_right_singleton Set.preimage_mul_right_singleton
#align set.preimage_add_right_singleton Set.preimage_add_right_singleton

/- warning: set.preimage_mul_left_one -> Set.preimage_mul_left_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α ((fun (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9648 : α) (x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9650 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9648 x._@.Mathlib.Data.Set.Pointwise.Basic._hyg.9650) a) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align set.preimage_mul_left_one Set.preimage_mul_left_oneₓ'. -/
@[simp, to_additive]
theorem preimage_mul_left_one : (· * ·) a ⁻¹' 1 = {a⁻¹} := by
  rw [← image_mul_left', image_one, mul_one]
#align set.preimage_mul_left_one Set.preimage_mul_left_one
#align set.preimage_add_left_zero Set.preimage_add_left_zero

/- warning: set.preimage_mul_right_one -> Set.preimage_mul_right_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x b) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b))
Case conversion may be inaccurate. Consider using '#align set.preimage_mul_right_one Set.preimage_mul_right_oneₓ'. -/
@[simp, to_additive]
theorem preimage_mul_right_one : (· * b) ⁻¹' 1 = {b⁻¹} := by
  rw [← image_mul_right', image_one, one_mul]
#align set.preimage_mul_right_one Set.preimage_mul_right_one
#align set.preimage_add_right_zero Set.preimage_add_right_zero

/- warning: set.preimage_mul_left_one' -> Set.preimage_mul_left_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {a : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (b : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align set.preimage_mul_left_one' Set.preimage_mul_left_one'ₓ'. -/
@[to_additive]
theorem preimage_mul_left_one' : (fun b => a⁻¹ * b) ⁻¹' 1 = {a} := by simp
#align set.preimage_mul_left_one' Set.preimage_mul_left_one'
#align set.preimage_add_left_zero' Set.preimage_add_left_zero'

/- warning: set.preimage_mul_right_one' -> Set.preimage_mul_right_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {b : α}, Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α α (fun (_x : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) _x (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)
Case conversion may be inaccurate. Consider using '#align set.preimage_mul_right_one' Set.preimage_mul_right_one'ₓ'. -/
@[to_additive]
theorem preimage_mul_right_one' : (· * b⁻¹) ⁻¹' 1 = {b} := by simp
#align set.preimage_mul_right_one' Set.preimage_mul_right_one'
#align set.preimage_add_right_zero' Set.preimage_add_right_zero'

/- warning: set.mul_univ -> Set.mul_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) s (Set.univ.{u1} α)) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) s (Set.univ.{u1} α)) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.mul_univ Set.mul_univₓ'. -/
@[simp, to_additive]
theorem mul_univ (hs : s.Nonempty) : s * (univ : Set α) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩
#align set.mul_univ Set.mul_univ
#align set.add_univ Set.add_univ

/- warning: set.univ_mul -> Set.univ_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (Set.univ.{u1} α) t) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) (Set.univ.{u1} α) t) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.univ_mul Set.univ_mulₓ'. -/
@[simp, to_additive]
theorem univ_mul (ht : t.Nonempty) : (univ : Set α) * t = univ :=
  let ⟨a, ha⟩ := ht
  eq_univ_of_forall fun b => ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩
#align set.univ_mul Set.univ_mul
#align set.univ_add Set.univ_add

end Group

section GroupWithZero

variable [GroupWithZero α] {s t : Set α}

/- warning: set.div_zero_subset -> Set.div_zero_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align set.div_zero_subset Set.div_zero_subsetₓ'. -/
theorem div_zero_subset (s : Set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
#align set.div_zero_subset Set.div_zero_subset

/- warning: set.zero_div_subset -> Set.zero_div_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align set.zero_div_subset Set.zero_div_subsetₓ'. -/
theorem zero_div_subset (s : Set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]
#align set.zero_div_subset Set.zero_div_subset

/- warning: set.nonempty.div_zero -> Set.Nonempty.div_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1))) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.div_zero Set.Nonempty.div_zeroₓ'. -/
theorem Nonempty.div_zero (hs : s.Nonempty) : s / 0 = 0 :=
  s.div_zero_subset.antisymm <| by simpa [mem_div] using hs
#align set.nonempty.div_zero Set.Nonempty.div_zero

/- warning: set.nonempty.zero_div -> Set.Nonempty.zero_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GroupWithZero.{u1} α] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} (Set.{u1} α) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (GroupWithZero.toDiv.{u1} α _inst_1))) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))) s) (OfNat.ofNat.{u1} (Set.{u1} α) 0 (Zero.toOfNat0.{u1} (Set.{u1} α) (Set.zero.{u1} α (MonoidWithZero.toZero.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.zero_div Set.Nonempty.zero_divₓ'. -/
theorem Nonempty.zero_div (hs : s.Nonempty) : 0 / s = 0 :=
  s.zero_div_subset.antisymm <| by simpa [mem_div] using hs
#align set.nonempty.zero_div Set.Nonempty.zero_div

end GroupWithZero

section Mul

variable [Mul α] [Mul β] [MulHomClass F α β] (m : F) {s t : Set α}

include α β

#print Set.image_mul /-
@[to_additive]
theorem image_mul : m '' (s * t) = m '' s * m '' t :=
  image_image2_distrib <| map_mul m
#align set.image_mul Set.image_mul
#align set.image_add Set.image_add
-/

#print Set.preimage_mul_preimage_subset /-
@[to_additive]
theorem preimage_mul_preimage_subset {s t : Set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
  by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm⟩
#align set.preimage_mul_preimage_subset Set.preimage_mul_preimage_subset
#align set.preimage_add_preimage_subset Set.preimage_add_preimage_subset
-/

end Mul

section Group

variable [Group α] [DivisionMonoid β] [MonoidHomClass F α β] (m : F) {s t : Set α}

include α β

/- warning: set.image_div -> Set.image_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : DivisionMonoid.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))] (m : F) {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3))) m) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) s t)) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} β) (Set.{u3} β) (Set.{u3} β) (instHDiv.{u3} (Set.{u3} β) (Set.div.{u3} β (DivInvMonoid.toHasDiv.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3))) m) s) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3))) m) t))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : DivisionMonoid.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))] (m : F) {s : Set.{u2} α} {t : Set.{u2} α}, Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3)) m) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) s t)) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} β) (Set.{u3} β) (Set.{u3} β) (instHDiv.{u3} (Set.{u3} β) (Set.div.{u3} β (DivInvMonoid.toDiv.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (Set.image.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3)) m) s) (Set.image.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3)) m) t))
Case conversion may be inaccurate. Consider using '#align set.image_div Set.image_divₓ'. -/
@[to_additive]
theorem image_div : m '' (s / t) = m '' s / m '' t :=
  image_image2_distrib <| map_div m
#align set.image_div Set.image_div
#align set.image_sub Set.image_sub

/- warning: set.preimage_div_preimage_subset -> Set.preimage_div_preimage_subset is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : DivisionMonoid.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))] (m : F) {s : Set.{u3} β} {t : Set.{u3} β}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Set.preimage.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3))) m) s) (Set.preimage.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3))) m) t)) (Set.preimage.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3))) m) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} β) (Set.{u3} β) (Set.{u3} β) (instHDiv.{u3} (Set.{u3} β) (Set.div.{u3} β (DivInvMonoid.toHasDiv.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) s t))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : DivisionMonoid.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))] (m : F) {s : Set.{u3} β} {t : Set.{u3} β}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (HDiv.hDiv.{u2, u2, u2} (Set.{u2} α) (Set.{u2} α) (Set.{u2} α) (instHDiv.{u2} (Set.{u2} α) (Set.div.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Set.preimage.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3)) m) s) (Set.preimage.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3)) m) t)) (Set.preimage.{u2, u3} α β (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α) => β) _x) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (MulOneClass.toMul.{u3} β (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) (Monoid.toMulOneClass.{u3} β (DivInvMonoid.toMonoid.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2))) _inst_3)) m) (HDiv.hDiv.{u3, u3, u3} (Set.{u3} β) (Set.{u3} β) (Set.{u3} β) (instHDiv.{u3} (Set.{u3} β) (Set.div.{u3} β (DivInvMonoid.toDiv.{u3} β (DivisionMonoid.toDivInvMonoid.{u3} β _inst_2)))) s t))
Case conversion may be inaccurate. Consider using '#align set.preimage_div_preimage_subset Set.preimage_div_preimage_subsetₓ'. -/
@[to_additive]
theorem preimage_div_preimage_subset {s t : Set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) :=
  by
  rintro _ ⟨_, _, _, _, rfl⟩
  exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm⟩
#align set.preimage_div_preimage_subset Set.preimage_div_preimage_subset
#align set.preimage_sub_preimage_subset Set.preimage_sub_preimage_subset

end Group

/- warning: set.bdd_above_mul -> Set.bddAbove_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {A : Set.{u1} α} {B : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1)) A) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1)) B) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) A B))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {A : Set.{u1} α} {B : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1)) A) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1)) B) -> (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) A B))
Case conversion may be inaccurate. Consider using '#align set.bdd_above_mul Set.bddAbove_mulₓ'. -/
@[to_additive]
theorem bddAbove_mul [OrderedCommMonoid α] {A B : Set α} :
    BddAbove A → BddAbove B → BddAbove (A * B) :=
  by
  rintro ⟨bA, hbA⟩ ⟨bB, hbB⟩
  use bA * bB
  rintro x ⟨xa, xb, hxa, hxb, rfl⟩
  exact mul_le_mul' (hbA hxa) (hbB hxb)
#align set.bdd_above_mul Set.bddAbove_mul
#align set.bdd_above_add Set.bddAbove_add

end Set

/-! ### Miscellaneous -/


open Set

open Pointwise

namespace Group

#print Group.card_pow_eq_card_pow_card_univ_aux /-
theorem card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : Monotone f) {B : ℕ} (h2 : ∀ n, f n ≤ B)
    (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) : ∀ k, B ≤ k → f k = f B :=
  by
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1) :=
    by
    contrapose! h2
    suffices ∀ n : ℕ, n ≤ B + 1 → n ≤ f n by exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩
    exact fun n =>
      Nat.rec (fun h => Nat.zero_le (f 0))
        (fun n ih h =>
          lt_of_le_of_lt (ih (n.le_succ.trans h))
            (lt_of_le_of_ne (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h))))
        n
  · obtain ⟨n, hn1, hn2⟩ := key
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n := fun k =>
      Nat.rec ⟨hn2, rfl⟩ (fun k ih => ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k
    replace key : ∀ k : ℕ, n ≤ k → f k = f n := fun k hk =>
      (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2
    exact fun k hk => (key k (hn1.trans hk)).trans (key B hn1).symm
#align group.card_pow_eq_card_pow_card_univ_aux Group.card_pow_eq_card_pow_card_univ_aux
-/

end Group

