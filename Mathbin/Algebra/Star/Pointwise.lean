/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module algebra.star.pointwise
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Set.Finite
import Mathbin.Data.Set.Pointwise.Basic

/-!
# Pointwise star operation on sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the star operation pointwise on sets and provides the basic API.
Besides basic facts about about how the star operation acts on sets (e.g., `(s ∩ t)⋆ = s⋆ ∩ t⋆`),
if `s t : set α`, then under suitable assumption on `α`, it is shown

* `(s + t)⋆ = s⋆ + t⋆`
* `(s * t)⋆ = t⋆ + s⋆`
* `(s⁻¹)⋆ = (s⋆)⁻¹`
-/


namespace Set

open Pointwise

-- mathport name: «expr ⋆»
local postfix:max "⋆" => star

variable {α : Type _} {s t : Set α} {a : α}

#print Set.star /-
/-- The set `(star s : set α)` is defined as `{x | star x ∈ s}` in locale `pointwise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`, see
`set.image_star`. -/
protected def star [Star α] : Star (Set α) :=
  ⟨preimage Star.star⟩
#align set.has_star Set.star
-/

scoped[Pointwise] attribute [instance] Set.star

#print Set.star_empty /-
@[simp]
theorem star_empty [Star α] : (∅ : Set α)⋆ = ∅ :=
  rfl
#align set.star_empty Set.star_empty
-/

#print Set.star_univ /-
@[simp]
theorem star_univ [Star α] : (univ : Set α)⋆ = univ :=
  rfl
#align set.star_univ Set.star_univ
-/

#print Set.nonempty_star /-
@[simp]
theorem nonempty_star [InvolutiveStar α] {s : Set α} : s⋆.Nonempty ↔ s.Nonempty :=
  star_involutive.Surjective.nonempty_preimage
#align set.nonempty_star Set.nonempty_star
-/

#print Set.Nonempty.star /-
theorem Nonempty.star [InvolutiveStar α] {s : Set α} (h : s.Nonempty) : s⋆.Nonempty :=
  nonempty_star.2 h
#align set.nonempty.star Set.Nonempty.star
-/

#print Set.mem_star /-
@[simp]
theorem mem_star [Star α] : a ∈ s⋆ ↔ a⋆ ∈ s :=
  Iff.rfl
#align set.mem_star Set.mem_star
-/

#print Set.star_mem_star /-
theorem star_mem_star [InvolutiveStar α] : a⋆ ∈ s⋆ ↔ a ∈ s := by simp only [mem_star, star_star]
#align set.star_mem_star Set.star_mem_star
-/

#print Set.star_preimage /-
@[simp]
theorem star_preimage [Star α] : Star.star ⁻¹' s = s⋆ :=
  rfl
#align set.star_preimage Set.star_preimage
-/

#print Set.image_star /-
@[simp]
theorem image_star [InvolutiveStar α] : Star.star '' s = s⋆ :=
  by
  simp only [← star_preimage]
  rw [image_eq_preimage_of_inverse] <;> intro <;> simp only [star_star]
#align set.image_star Set.image_star
-/

/- warning: set.inter_star -> Set.inter_star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Star.{u1} α], Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) s) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Star.{u1} α], Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) s) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align set.inter_star Set.inter_starₓ'. -/
@[simp]
theorem inter_star [Star α] : (s ∩ t)⋆ = s⋆ ∩ t⋆ :=
  preimage_inter
#align set.inter_star Set.inter_star

/- warning: set.union_star -> Set.union_star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Star.{u1} α], Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) s) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Star.{u1} α], Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) s) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align set.union_star Set.union_starₓ'. -/
@[simp]
theorem union_star [Star α] : (s ∪ t)⋆ = s⋆ ∪ t⋆ :=
  preimage_union
#align set.union_star Set.union_star

#print Set.interᵢ_star /-
@[simp]
theorem interᵢ_star {ι : Sort _} [Star α] (s : ι → Set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ :=
  preimage_interᵢ
#align set.Inter_star Set.interᵢ_star
-/

#print Set.unionᵢ_star /-
@[simp]
theorem unionᵢ_star {ι : Sort _} [Star α] (s : ι → Set α) : (⋃ i, s i)⋆ = ⋃ i, (s i)⋆ :=
  preimage_unionᵢ
#align set.Union_star Set.unionᵢ_star
-/

/- warning: set.compl_star -> Set.compl_star is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Star.{u1} α], Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Star.{u1} α], Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align set.compl_star Set.compl_starₓ'. -/
@[simp]
theorem compl_star [Star α] : (sᶜ)⋆ = s⋆ᶜ :=
  preimage_compl
#align set.compl_star Set.compl_star

@[simp]
instance [InvolutiveStar α] : InvolutiveStar (Set α)
    where
  unit := Star.star
  star_involutive s := by simp only [← star_preimage, preimage_preimage, star_star, preimage_id']

#print Set.star_subset_star /-
@[simp]
theorem star_subset_star [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t⋆ ↔ s ⊆ t :=
  Equiv.star.Surjective.preimage_subset_preimage_iff
#align set.star_subset_star Set.star_subset_star
-/

#print Set.star_subset /-
theorem star_subset [InvolutiveStar α] {s t : Set α} : s⋆ ⊆ t ↔ s ⊆ t⋆ := by
  rw [← star_subset_star, star_star]
#align set.star_subset Set.star_subset
-/

#print Set.Finite.star /-
theorem Finite.star [InvolutiveStar α] {s : Set α} (hs : s.Finite) : s⋆.Finite :=
  hs.Preimage <| star_injective.InjOn _
#align set.finite.star Set.Finite.star
-/

#print Set.star_singleton /-
theorem star_singleton {β : Type _} [InvolutiveStar β] (x : β) : ({x} : Set β)⋆ = {x⋆} :=
  by
  ext1 y
  rw [mem_star, mem_singleton_iff, mem_singleton_iff, star_eq_iff_star_eq, eq_comm]
#align set.star_singleton Set.star_singleton
-/

/- warning: set.star_mul -> Set.star_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : StarSemigroup.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α _inst_1) _inst_2))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α _inst_1) _inst_2))) t) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α _inst_1) _inst_2))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] [_inst_2 : StarSemigroup.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarSemigroup.toInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α _inst_1) _inst_2))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) s t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarSemigroup.toInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α _inst_1) _inst_2))) t) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarSemigroup.toInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α _inst_1) _inst_2))) s))
Case conversion may be inaccurate. Consider using '#align set.star_mul Set.star_mulₓ'. -/
protected theorem star_mul [Monoid α] [StarSemigroup α] (s t : Set α) : (s * t)⋆ = t⋆ * s⋆ := by
  simp_rw [← image_star, ← image2_mul, image_image2, image2_image_left, image2_image_right,
    star_mul, image2_swap _ s t]
#align set.star_mul Set.star_mul

/- warning: set.star_add -> Set.star_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2))) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) s t)) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2))) s) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α _inst_1 _inst_2))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddMonoid.{u1} α] [_inst_2 : StarAddMonoid.{u1} α _inst_1] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarAddMonoid.toInvolutiveStar.{u1} α _inst_1 _inst_2))) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) s t)) (HAdd.hAdd.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHAdd.{u1} (Set.{u1} α) (Set.add.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_1)))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarAddMonoid.toInvolutiveStar.{u1} α _inst_1 _inst_2))) s) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarAddMonoid.toInvolutiveStar.{u1} α _inst_1 _inst_2))) t))
Case conversion may be inaccurate. Consider using '#align set.star_add Set.star_addₓ'. -/
protected theorem star_add [AddMonoid α] [StarAddMonoid α] (s t : Set α) : (s + t)⋆ = s⋆ + t⋆ := by
  simp_rw [← image_star, ← image2_add, image_image2, image2_image_left, image2_image_right,
    star_add]
#align set.star_add Set.star_add

@[simp]
instance [Star α] [TrivialStar α] : TrivialStar (Set α)
    where star_trivial s := by
    rw [← star_preimage]
    ext1
    simp [star_trivial]

/- warning: set.star_inv -> Set.star_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : StarSemigroup.{u1} α (Monoid.toSemigroup.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_2))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) s)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarSemigroup.toHasInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_2))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] [_inst_2 : StarSemigroup.{u1} α (Monoid.toSemigroup.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarSemigroup.toInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_2))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))) s)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarSemigroup.toInvolutiveStar.{u1} α (Monoid.toSemigroup.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) _inst_2))) s))
Case conversion may be inaccurate. Consider using '#align set.star_inv Set.star_invₓ'. -/
protected theorem star_inv [Group α] [StarSemigroup α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ :=
  by
  ext
  simp only [mem_star, mem_inv, star_inv]
#align set.star_inv Set.star_inv

/- warning: set.star_inv' -> Set.star_inv' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : StarRing.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (StarRing.toStarAddMonoid.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) _inst_2)))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) s)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (DivisionRing.toDivInvMonoid.{u1} α _inst_1))) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toHasStar.{u1} α (StarAddMonoid.toHasInvolutiveStar.{u1} α (AddCommMonoid.toAddMonoid.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))))) (StarRing.toStarAddMonoid.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) _inst_2)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DivisionRing.{u1} α] [_inst_2 : StarRing.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))] (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarAddMonoid.toInvolutiveStar.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (StarRing.toStarAddMonoid.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) _inst_2)))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivisionRing.toInv.{u1} α _inst_1)) s)) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivisionRing.toInv.{u1} α _inst_1)) (Star.star.{u1} (Set.{u1} α) (Set.star.{u1} α (InvolutiveStar.toStar.{u1} α (StarAddMonoid.toInvolutiveStar.{u1} α (AddMonoidWithOne.toAddMonoid.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (Ring.toAddGroupWithOne.{u1} α (DivisionRing.toRing.{u1} α _inst_1)))) (StarRing.toStarAddMonoid.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α (DivisionRing.toRing.{u1} α _inst_1))) _inst_2)))) s))
Case conversion may be inaccurate. Consider using '#align set.star_inv' Set.star_inv'ₓ'. -/
protected theorem star_inv' [DivisionRing α] [StarRing α] (s : Set α) : s⁻¹⋆ = s⋆⁻¹ :=
  by
  ext
  simp only [mem_star, mem_inv, star_inv']
#align set.star_inv' Set.star_inv'

end Set

