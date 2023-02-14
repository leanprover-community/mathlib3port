/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.group.ext
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
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

/- warning: monoid.ext -> Monoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : Monoid.{u1} M}} {{m₂ : Monoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Monoid.mul.{u1} M m₁) (Monoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (Monoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : Monoid.{u1} M}} {{m₂ : Monoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (Monoid.toSemigroup.{u1} M m₁))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (Monoid.toSemigroup.{u1} M m₂)))) -> (Eq.{succ u1} (Monoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align monoid.ext Monoid.extₓ'. -/
@[ext, to_additive]
theorem Monoid.ext {M : Type u} ⦃m₁ m₂ : Monoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  by
  have h₁ : (@Monoid.toMulOneClass _ m₁).one = (@Monoid.toMulOneClass _ m₂).one :=
    congr_arg (@MulOneClass.one M) (MulOneClass.ext h_mul)
  set f : @MonoidHom M M (@Monoid.toMulOneClass _ m₁) (@Monoid.toMulOneClass _ m₂) :=
    { toFun := id
      map_one' := h₁
      map_mul' := fun x y => congr_fun (congr_fun h_mul x) y }
  have hpow : m₁.npow = m₂.npow := by
    ext (n x)
    exact @MonoidHom.map_pow M M m₁ m₂ f x n
  cases m₁
  cases m₂
  congr <;> assumption
#align monoid.ext Monoid.ext
#align add_monoid.ext AddMonoid.ext

#print CommMonoid.toMonoid_injective /-
@[to_additive]
theorem CommMonoid.toMonoid_injective {M : Type u} : Function.Injective (@CommMonoid.toMonoid M) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  congr <;> injection h
#align comm_monoid.to_monoid_injective CommMonoid.toMonoid_injective
#align add_comm_monoid.to_add_monoid_injective AddCommMonoid.toAddMonoid_injective
-/

/- warning: comm_monoid.ext -> CommMonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : CommMonoid.{u1} M}} {{m₂ : CommMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (CommMonoid.mul.{u1} M m₁) (CommMonoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (CommMonoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : CommMonoid.{u1} M}} {{m₂ : CommMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (Monoid.toSemigroup.{u1} M (CommMonoid.toMonoid.{u1} M m₁)))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (Monoid.toSemigroup.{u1} M (CommMonoid.toMonoid.{u1} M m₂))))) -> (Eq.{succ u1} (CommMonoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align comm_monoid.ext CommMonoid.extₓ'. -/
@[ext, to_additive]
theorem CommMonoid.ext {M : Type _} ⦃m₁ m₂ : CommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul
#align comm_monoid.ext CommMonoid.ext
#align add_comm_monoid.ext AddCommMonoid.ext

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

/- warning: left_cancel_monoid.ext -> LeftCancelMonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : LeftCancelMonoid.{u1} M}} {{m₂ : LeftCancelMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (LeftCancelMonoid.mul.{u1} M m₁) (LeftCancelMonoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (LeftCancelMonoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : LeftCancelMonoid.{u1} M}} {{m₂ : LeftCancelMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (LeftCancelSemigroup.toSemigroup.{u1} M (LeftCancelMonoid.toLeftCancelSemigroup.{u1} M m₁)))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (LeftCancelSemigroup.toSemigroup.{u1} M (LeftCancelMonoid.toLeftCancelSemigroup.{u1} M m₂))))) -> (Eq.{succ u1} (LeftCancelMonoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align left_cancel_monoid.ext LeftCancelMonoid.extₓ'. -/
@[ext, to_additive]
theorem LeftCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : LeftCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  LeftCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align left_cancel_monoid.ext LeftCancelMonoid.ext
#align add_left_cancel_monoid.ext AddLeftCancelMonoid.ext

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

/- warning: right_cancel_monoid.ext -> RightCancelMonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : RightCancelMonoid.{u1} M}} {{m₂ : RightCancelMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (RightCancelMonoid.mul.{u1} M m₁) (RightCancelMonoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (RightCancelMonoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : RightCancelMonoid.{u1} M}} {{m₂ : RightCancelMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (RightCancelSemigroup.toSemigroup.{u1} M (RightCancelMonoid.toRightCancelSemigroup.{u1} M m₁)))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (RightCancelSemigroup.toSemigroup.{u1} M (RightCancelMonoid.toRightCancelSemigroup.{u1} M m₂))))) -> (Eq.{succ u1} (RightCancelMonoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align right_cancel_monoid.ext RightCancelMonoid.extₓ'. -/
@[ext, to_additive]
theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul
#align right_cancel_monoid.ext RightCancelMonoid.ext
#align add_right_cancel_monoid.ext AddRightCancelMonoid.ext

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

/- warning: cancel_monoid.ext -> CancelMonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : CancelMonoid.{u1} M}} {{m₂ : CancelMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (CancelMonoid.mul.{u1} M m₁) (CancelMonoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (CancelMonoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : CancelMonoid.{u1} M}} {{m₂ : CancelMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (LeftCancelSemigroup.toSemigroup.{u1} M (LeftCancelMonoid.toLeftCancelSemigroup.{u1} M (CancelMonoid.toLeftCancelMonoid.{u1} M m₁))))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (LeftCancelSemigroup.toSemigroup.{u1} M (LeftCancelMonoid.toLeftCancelSemigroup.{u1} M (CancelMonoid.toLeftCancelMonoid.{u1} M m₂)))))) -> (Eq.{succ u1} (CancelMonoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align cancel_monoid.ext CancelMonoid.extₓ'. -/
@[ext, to_additive]
theorem CancelMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelMonoid.toLeftCancelMonoid_injective <| LeftCancelMonoid.ext h_mul
#align cancel_monoid.ext CancelMonoid.ext
#align add_cancel_monoid.ext AddCancelMonoid.ext

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

/- warning: cancel_comm_monoid.ext -> CancelCommMonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : CancelCommMonoid.{u1} M}} {{m₂ : CancelCommMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (CancelCommMonoid.mul.{u1} M m₁) (CancelCommMonoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (CancelCommMonoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : CancelCommMonoid.{u1} M}} {{m₂ : CancelCommMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (LeftCancelSemigroup.toSemigroup.{u1} M (LeftCancelMonoid.toLeftCancelSemigroup.{u1} M (CancelCommMonoid.toLeftCancelMonoid.{u1} M m₁))))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (LeftCancelSemigroup.toSemigroup.{u1} M (LeftCancelMonoid.toLeftCancelSemigroup.{u1} M (CancelCommMonoid.toLeftCancelMonoid.{u1} M m₂)))))) -> (Eq.{succ u1} (CancelCommMonoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align cancel_comm_monoid.ext CancelCommMonoid.extₓ'. -/
@[ext, to_additive]
theorem CancelCommMonoid.ext {M : Type _} ⦃m₁ m₂ : CancelCommMonoid M⦄ (h_mul : m₁.mul = m₂.mul) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul
#align cancel_comm_monoid.ext CancelCommMonoid.ext
#align add_cancel_comm_monoid.ext AddCancelCommMonoid.ext

/- warning: div_inv_monoid.ext -> DivInvMonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {{m₁ : DivInvMonoid.{u1} M}} {{m₂ : DivInvMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (DivInvMonoid.mul.{u1} M m₁) (DivInvMonoid.mul.{u1} M m₂)) -> (Eq.{succ u1} (M -> M) (DivInvMonoid.inv.{u1} M m₁) (DivInvMonoid.inv.{u1} M m₂)) -> (Eq.{succ u1} (DivInvMonoid.{u1} M) m₁ m₂)
but is expected to have type
  forall {M : Type.{u1}} {{m₁ : DivInvMonoid.{u1} M}} {{m₂ : DivInvMonoid.{u1} M}}, (Eq.{succ u1} (M -> M -> M) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (Monoid.toSemigroup.{u1} M (DivInvMonoid.toMonoid.{u1} M m₁)))) (Mul.mul.{u1} M (Semigroup.toMul.{u1} M (Monoid.toSemigroup.{u1} M (DivInvMonoid.toMonoid.{u1} M m₂))))) -> (Eq.{succ u1} (M -> M) (Inv.inv.{u1} M (DivInvMonoid.toInv.{u1} M m₁)) (Inv.inv.{u1} M (DivInvMonoid.toInv.{u1} M m₂))) -> (Eq.{succ u1} (DivInvMonoid.{u1} M) m₁ m₂)
Case conversion may be inaccurate. Consider using '#align div_inv_monoid.ext DivInvMonoid.extₓ'. -/
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
    ext (m x)
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have hdiv : m₁.div = m₂.div := by
    ext (a b)
    exact @map_div' M M _ m₁ m₂ _ f (congr_fun h_inv) a b
  cases m₁
  cases m₂
  congr
  exacts[h_mul, h₁, hpow, h_inv, hdiv, hzpow]
#align div_inv_monoid.ext DivInvMonoid.ext
#align sub_neg_monoid.ext SubNegMonoid.ext

/- warning: group.ext -> Group.ext is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {{g₁ : Group.{u1} G}} {{g₂ : Group.{u1} G}}, (Eq.{succ u1} (G -> G -> G) (Group.mul.{u1} G g₁) (Group.mul.{u1} G g₂)) -> (Eq.{succ u1} (Group.{u1} G) g₁ g₂)
but is expected to have type
  forall {G : Type.{u1}} {{g₁ : Group.{u1} G}} {{g₂ : Group.{u1} G}}, (Eq.{succ u1} (G -> G -> G) (Mul.mul.{u1} G (Semigroup.toMul.{u1} G (Monoid.toSemigroup.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G g₁))))) (Mul.mul.{u1} G (Semigroup.toMul.{u1} G (Monoid.toSemigroup.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G g₂)))))) -> (Eq.{succ u1} (Group.{u1} G) g₁ g₂)
Case conversion may be inaccurate. Consider using '#align group.ext Group.extₓ'. -/
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

/- warning: comm_group.ext -> CommGroup.ext is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {{g₁ : CommGroup.{u1} G}} {{g₂ : CommGroup.{u1} G}}, (Eq.{succ u1} (G -> G -> G) (CommGroup.mul.{u1} G g₁) (CommGroup.mul.{u1} G g₂)) -> (Eq.{succ u1} (CommGroup.{u1} G) g₁ g₂)
but is expected to have type
  forall {G : Type.{u1}} {{g₁ : CommGroup.{u1} G}} {{g₂ : CommGroup.{u1} G}}, (Eq.{succ u1} (G -> G -> G) (Mul.mul.{u1} G (Semigroup.toMul.{u1} G (Monoid.toSemigroup.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G g₁)))))) (Mul.mul.{u1} G (Semigroup.toMul.{u1} G (Monoid.toSemigroup.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G g₂))))))) -> (Eq.{succ u1} (CommGroup.{u1} G) g₁ g₂)
Case conversion may be inaccurate. Consider using '#align comm_group.ext CommGroup.extₓ'. -/
@[ext, to_additive]
theorem CommGroup.ext {G : Type _} ⦃g₁ g₂ : CommGroup G⦄ (h_mul : g₁.mul = g₂.mul) : g₁ = g₂ :=
  CommGroup.toGroup_injective <| Group.ext h_mul
#align comm_group.ext CommGroup.ext
#align add_comm_group.ext AddCommGroup.ext

