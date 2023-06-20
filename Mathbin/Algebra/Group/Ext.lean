/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.group.ext
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group

/-!
# Extensionality lemmas for monoid and group structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove extensionality lemmas for `monoid` and higher algebraic structures with one
binary operation. Extensionality lemmas for structures that are lower in the hierarchy can be found
in `algebra.group.defs`.

## Implementation details

To get equality of `npow` etc, we define a monoid homomorphism between two monoid structures on the
same type, then apply lemmas like `monoid_hom.map_div`, `monoid_hom.map_pow` etc.

## Tags
monoid, group, extensionality
-/


universe u

#print Monoid.ext /-
@[ext, to_additive]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  by
  have h₁ : (@Monoid.toMulOneClass _ m₁).one = (@Monoid.toMulOneClass _ m₂).one :=
    congr_arg (@MulOneClass.one M) (MulOneClass.ext h_mul)
  set f : @MonoidHom M M (@Monoid.toMulOneClass _ m₁) (@Monoid.toMulOneClass _ m₂) :=
    { toFun := id
      map_one' := h₁
      map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : m₁.npow = m₂.npow := by ext n x; exact @MonoidHom.map_pow M M m₁ m₂ f x n
  cases m₁; cases m₂
  congr <;> assumption
#align monoid.ext Monoid.ext
#align add_monoid.ext AddMonoid.ext
-/

#print CommMonoid.toMonoid_injective /-
@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} : Function.Injective (@CommMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align comm_monoid.to_monoid_injective CommMonoid.toMonoid_injective
#align add_comm_monoid.to_add_monoid_injective AddCommMonoid.toAddMonoid_injective
-/

#print CommMonoid.ext /-
@[ext, to_additive]
theorem CommMonoid.ext {M : Type _} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext
#align add_comm_monoid.ext AddCommMonoid.ext
-/

#print LeftCancelMonoid.toMonoid_injective /-
@[to_additive]
theorem LeftCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@LeftCancelMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align left_cancel_monoid.to_monoid_injective LeftCancelMonoid.toMonoid_injective
#align add_left_cancel_monoid.to_add_monoid_injective AddLeftCancelMonoid.toAddMonoid_injective
-/

#print LeftCancelMonoid.ext /-
@[ext, to_additive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align left_cancel_monoid.ext LeftCancelMonoid.ext
#align add_left_cancel_monoid.ext AddLeftCancelMonoid.ext
-/

#print RightCancelMonoid.toMonoid_injective /-
@[to_additive]
theorem RightCancelMonoid.toMonoid_injective {M : Type u} :
    Function.Injective (@RightCancelMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align right_cancel_monoid.to_monoid_injective RightCancelMonoid.toMonoid_injective
#align add_right_cancel_monoid.to_add_monoid_injective AddRightCancelMonoid.toAddMonoid_injective
-/

#print RightCancelMonoid.ext /-
@[ext, to_additive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align right_cancel_monoid.ext RightCancelMonoid.ext
#align add_right_cancel_monoid.ext AddRightCancelMonoid.ext
-/

#print CancelMonoid.toLeftCancelMonoid_injective /-
@[to_additive]
theorem CancelMonoid.toLeftCancelMonoid_injective {M : Type u} :
    Function.Injective (@CancelMonoid.toLeftCancelMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align cancel_monoid.to_left_cancel_monoid_injective CancelMonoid.toLeftCancelMonoid_injective
#align add_cancel_monoid.to_left_cancel_add_monoid_injective AddCancelMonoid.toAddLeftCancelMonoid_injective
-/

#print CancelMonoid.ext /-
@[ext, to_additive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext
#align add_cancel_monoid.ext AddCancelMonoid.ext
-/

#print CancelCommMonoid.toCommMonoid_injective /-
@[to_additive]
theorem CancelCommMonoid.toCommMonoid_injective {M : Type u} :
    Function.Injective (@CancelCommMonoid.toCommMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align cancel_comm_monoid.to_comm_monoid_injective CancelCommMonoid.toCommMonoid_injective
#align add_cancel_comm_monoid.to_add_comm_monoid_injective AddCancelCommMonoid.toAddCommMonoid_injective
-/

#print CancelCommMonoid.ext /-
@[ext, to_additive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext
#align add_cancel_comm_monoid.ext AddCancelCommMonoid.ext
-/

#print DivInvMonoid.ext /-
@[ext, to_additive]
theorem DivInvMonoid.ext {M : Type _} ⦃m₁ m₂ : DivInvMonoid M⦄ (h_mul : m₁.mul = m₂.mul)
    (h_inv : m₁.inv = m₂.inv) : m₁ = m₂ :=
  by
  have h₁ : (@DivInvMonoid.toMonoid _ m₁).one = (@DivInvMonoid.toMonoid _ m₂).one :=
    congr_arg (@Monoid.one M) (Monoid.ext h_mul)
  set f : @MonoidHom M M (by letI := m₁ <;> infer_instance) (by letI := m₂ <;> infer_instance) :=
    { toFun := id
      map_one' := h₁
      map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : (@DivInvMonoid.toMonoid _ m₁).npow = (@DivInvMonoid.toMonoid _ m₂).npow :=
    congr_arg (@Monoid.npow M) (Monoid.ext h_mul)
  have hzpow : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have hdiv : m₁.div = m₂.div := by
    ext a b
    exact @map_div' M M _ m₁ m₂ _ f (congr_fun h_inv) a b
  cases m₁; cases m₂
  congr; exacts [h_mul, h₁, hpow, h_inv, hdiv, hzpow]
#align div_inv_monoid.ext DivInvMonoid.ext
#align sub_neg_monoid.ext SubNegMonoid.ext
-/

#print Group.ext /-
@[ext, to_additive]
theorem Group.ext {G : Type _} ⦃g₁ g₂ : Group G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  by
  set f :=
    @MonoidHom.mk' G G (by letI := g₁ <;> infer_instance) g₂ id fun a b =>
      congr_fun (congr_fun h_mul a) b
  exact
    Group.toDivInvMonoid_injective
      (DivInvMonoid.ext h_mul
        (funext <| @MonoidHom.map_inv G G g₁ (@Group.toDivisionMonoid _ g₂) f))
#align group.ext Group.ext
#align add_group.ext AddGroup.ext
-/

#print CommGroup.ext /-
@[ext, to_additive]
theorem CommGroup.ext {G : Type _} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext
#align add_comm_group.ext AddCommGroup.ext
-/

