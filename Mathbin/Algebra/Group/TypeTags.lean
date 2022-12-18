/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module algebra.group.type_tags
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Logic.Equiv.Defs
import Mathbin.Data.Finite.Defs

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/832
> Any changes to this file require a corresponding PR to mathlib4.

We define two type tags:

* `additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `additive α`;
* `multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `multiplicative α`.

We also define instances `additive.*` and `multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `order.synonym`.
-/


universe u v

variable {α : Type u} {β : Type v}

#print Additive /-
/-- If `α` carries some multiplicative structure, then `additive α` carries the corresponding
additive structure. -/
def Additive (α : Type _) :=
  α
#align additive Additive
-/

#print Multiplicative /-
/-- If `α` carries some additive structure, then `multiplicative α` carries the corresponding
multiplicative structure. -/
def Multiplicative (α : Type _) :=
  α
#align multiplicative Multiplicative
-/

namespace Additive

#print Additive.ofMul /-
/-- Reinterpret `x : α` as an element of `additive α`. -/
def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun x => rfl, fun x => rfl⟩
#align additive.of_mul Additive.ofMul
-/

#print Additive.toMul /-
/-- Reinterpret `x : additive α` as an element of `α`. -/
def toMul : Additive α ≃ α :=
  ofMul.symm
#align additive.to_mul Additive.toMul
-/

#print Additive.ofMul_symm_eq /-
@[simp]
theorem ofMul_symm_eq : (@ofMul α).symm = to_mul :=
  rfl
#align additive.of_mul_symm_eq Additive.ofMul_symm_eq
-/

#print Additive.toMul_symm_eq /-
@[simp]
theorem toMul_symm_eq : (@toMul α).symm = of_mul :=
  rfl
#align additive.to_mul_symm_eq Additive.toMul_symm_eq
-/

end Additive

namespace Multiplicative

#print Multiplicative.ofAdd /-
/-- Reinterpret `x : α` as an element of `multiplicative α`. -/
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun x => rfl, fun x => rfl⟩
#align multiplicative.of_add Multiplicative.ofAdd
-/

#print Multiplicative.toAdd /-
/-- Reinterpret `x : multiplicative α` as an element of `α`. -/
def toAdd : Multiplicative α ≃ α :=
  ofAdd.symm
#align multiplicative.to_add Multiplicative.toAdd
-/

#print Multiplicative.ofAdd_symm_eq /-
@[simp]
theorem ofAdd_symm_eq : (@ofAdd α).symm = to_add :=
  rfl
#align multiplicative.of_add_symm_eq Multiplicative.ofAdd_symm_eq
-/

#print Multiplicative.toAdd_symm_eq /-
@[simp]
theorem toAdd_symm_eq : (@toAdd α).symm = of_add :=
  rfl
#align multiplicative.to_add_symm_eq Multiplicative.toAdd_symm_eq
-/

end Multiplicative

#print toAdd_ofAdd /-
@[simp]
theorem toAdd_ofAdd (x : α) : (Multiplicative.ofAdd x).toAdd = x :=
  rfl
#align to_add_of_add toAdd_ofAdd
-/

#print ofAdd_toAdd /-
@[simp]
theorem ofAdd_toAdd (x : Multiplicative α) : Multiplicative.ofAdd x.toAdd = x :=
  rfl
#align of_add_to_add ofAdd_toAdd
-/

#print toMul_ofMul /-
@[simp]
theorem toMul_ofMul (x : α) : (Additive.ofMul x).toMul = x :=
  rfl
#align to_mul_of_mul toMul_ofMul
-/

#print ofMul_toMul /-
@[simp]
theorem ofMul_toMul (x : Additive α) : Additive.ofMul x.toMul = x :=
  rfl
#align of_mul_to_mul ofMul_toMul
-/

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨Additive.ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨Multiplicative.ofAdd default⟩

instance [Finite α] : Finite (Additive α) :=
  Finite.of_equiv α (by rfl)

instance [Finite α] : Finite (Multiplicative α) :=
  Finite.of_equiv α (by rfl)

instance [Infinite α] : Infinite (Additive α) := by tauto

instance [Infinite α] : Infinite (Multiplicative α) := by tauto

instance [Nontrivial α] : Nontrivial (Additive α) :=
  Additive.ofMul.Injective.Nontrivial

instance [Nontrivial α] : Nontrivial (Multiplicative α) :=
  Multiplicative.ofAdd.Injective.Nontrivial

instance Additive.hasAdd [Mul α] :
    Add (Additive α) where add x y := Additive.ofMul (x.toMul * y.toMul)
#align additive.has_add Additive.hasAdd

instance [Add α] : Mul (Multiplicative α) where mul x y := Multiplicative.ofAdd (x.toAdd + y.toAdd)

#print ofAdd_add /-
@[simp]
theorem ofAdd_add [Add α] (x y : α) :
    Multiplicative.ofAdd (x + y) = Multiplicative.ofAdd x * Multiplicative.ofAdd y :=
  rfl
#align of_add_add ofAdd_add
-/

#print toAdd_mul /-
@[simp]
theorem toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.toAdd :=
  rfl
#align to_add_mul toAdd_mul
-/

#print ofMul_mul /-
@[simp]
theorem ofMul_mul [Mul α] (x y : α) :
    Additive.ofMul (x * y) = Additive.ofMul x + Additive.ofMul y :=
  rfl
#align of_mul_mul ofMul_mul
-/

#print toMul_add /-
@[simp]
theorem toMul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul :=
  rfl
#align to_mul_add toMul_add
-/

instance [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.hasAdd with add_assoc := @mul_assoc α _ }

instance [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.hasMul with mul_assoc := @add_assoc α _ }

instance [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm _ _ }

instance [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_comm _ _ }

instance [Mul α] [IsLeftCancelMul α] :
    IsLeftCancelAdd (Additive α) where add_left_cancel := @mul_left_cancel α _ _

instance [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) where mul_left_cancel := @add_left_cancel α _ _

instance [Mul α] [IsRightCancelMul α] :
    IsRightCancelAdd (Additive α) where add_right_cancel := @mul_right_cancel α _ _

instance [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) where mul_right_cancel := @add_right_cancel α _ _

instance [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  { Additive.is_left_cancel_add, Additive.is_right_cancel_add with }

instance [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  { Multiplicative.is_left_cancel_mul, Multiplicative.is_right_cancel_mul with }

instance [LeftCancelSemigroup α] : AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.is_left_cancel_add with }

instance [AddLeftCancelSemigroup α] : LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.is_left_cancel_mul with }

instance [RightCancelSemigroup α] : AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.is_right_cancel_add with }

instance [AddRightCancelSemigroup α] : RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.is_right_cancel_mul with }

instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

#print ofMul_one /-
@[simp]
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 :=
  rfl
#align of_mul_one ofMul_one
-/

#print ofMul_eq_zero /-
@[simp]
theorem ofMul_eq_zero {A : Type _} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 :=
  Iff.rfl
#align of_mul_eq_zero ofMul_eq_zero
-/

#print toMul_zero /-
@[simp]
theorem toMul_zero [One α] : (0 : Additive α).toMul = 1 :=
  rfl
#align to_mul_zero toMul_zero
-/

instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

#print ofAdd_zero /-
@[simp]
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl
#align of_add_zero ofAdd_zero
-/

#print ofAdd_eq_one /-
@[simp]
theorem ofAdd_eq_one {A : Type _} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl
#align of_add_eq_one ofAdd_eq_one
-/

#print toAdd_one /-
@[simp]
theorem toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0 :=
  rfl
#align to_add_one toAdd_one
-/

instance [MulOneClass α] : AddZeroClass
      (Additive α) where 
  zero := 0
  add := (· + ·)
  zero_add := one_mul
  add_zero := mul_one

instance [AddZeroClass α] :
    MulOneClass (Multiplicative α) where 
  one := 1
  mul := (· * ·)
  one_mul := zero_add
  mul_one := add_zero

instance [h : Monoid α] : AddMonoid (Additive α) :=
  { Additive.addZeroClass, Additive.addSemigroup with
    zero := 0
    add := (· + ·)
    nsmul := @Monoid.npow α h
    nsmul_zero' := Monoid.npow_zero
    nsmul_succ' := Monoid.npow_succ }

instance [h : AddMonoid α] : Monoid (Multiplicative α) :=
  { Multiplicative.mulOneClass, Multiplicative.semigroup with
    one := 1
    mul := (· * ·)
    npow := @AddMonoid.nsmul α h
    npow_zero' := AddMonoid.nsmul_zero
    npow_succ' := AddMonoid.nsmul_succ }

instance [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with
    zero := 0
    add := (· + ·) }

instance [AddLeftCancelMonoid α] : LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with
    one := 1
    mul := (· * ·) }

instance [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with
    zero := 0
    add := (· + ·) }

instance [AddRightCancelMonoid α] : RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with
    one := 1
    mul := (· * ·) }

instance [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with
    zero := 0
    add := (· + ·) }

instance [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with
    one := 1
    mul := (· * ·) }

instance [Inv α] : Neg (Additive α) :=
  ⟨fun x => Multiplicative.ofAdd x.toMul⁻¹⟩

#print ofMul_inv /-
@[simp]
theorem ofMul_inv [Inv α] (x : α) : Additive.ofMul x⁻¹ = -Additive.ofMul x :=
  rfl
#align of_mul_inv ofMul_inv
-/

#print toMul_neg /-
@[simp]
theorem toMul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹ :=
  rfl
#align to_mul_neg toMul_neg
-/

instance [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => Additive.ofMul (-x.toAdd)⟩

#print ofAdd_neg /-
@[simp]
theorem ofAdd_neg [Neg α] (x : α) : Multiplicative.ofAdd (-x) = (Multiplicative.ofAdd x)⁻¹ :=
  rfl
#align of_add_neg ofAdd_neg
-/

#print toAdd_inv /-
@[simp]
theorem toAdd_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd :=
  rfl
#align to_add_inv toAdd_inv
-/

#print Additive.sub /-
instance Additive.sub [Div α] : Sub (Additive α) where sub x y := Additive.ofMul (x.toMul / y.toMul)
#align additive.has_sub Additive.sub
-/

#print Multiplicative.div /-
instance Multiplicative.div [Sub α] :
    Div (Multiplicative α) where div x y := Multiplicative.ofAdd (x.toAdd - y.toAdd)
#align multiplicative.has_div Multiplicative.div
-/

#print ofAdd_sub /-
@[simp]
theorem ofAdd_sub [Sub α] (x y : α) :
    Multiplicative.ofAdd (x - y) = Multiplicative.ofAdd x / Multiplicative.ofAdd y :=
  rfl
#align of_add_sub ofAdd_sub
-/

#print toAdd_div /-
@[simp]
theorem toAdd_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.toAdd :=
  rfl
#align to_add_div toAdd_div
-/

#print ofMul_div /-
@[simp]
theorem ofMul_div [Div α] (x y : α) :
    Additive.ofMul (x / y) = Additive.ofMul x - Additive.ofMul y :=
  rfl
#align of_mul_div ofMul_div
-/

#print toMul_sub /-
@[simp]
theorem toMul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul :=
  rfl
#align to_mul_sub toMul_sub
-/

instance [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.hasNeg with neg_neg := @inv_inv _ _ }

instance [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.hasInv with inv_inv := @neg_neg _ _ }

instance [DivInvMonoid α] : SubNegMonoid (Additive α) :=
  { Additive.hasNeg, Additive.sub, Additive.addMonoid with
    sub_eq_add_neg := @div_eq_mul_inv α _
    zsmul := @DivInvMonoid.zpow α _
    zsmul_zero' := DivInvMonoid.zpow_zero'
    zsmul_succ' := DivInvMonoid.zpow_succ'
    zsmul_neg' := DivInvMonoid.zpow_neg' }

instance [SubNegMonoid α] : DivInvMonoid (Multiplicative α) :=
  { Multiplicative.hasInv, Multiplicative.div, Multiplicative.monoid with
    div_eq_mul_inv := @sub_eq_add_neg α _
    zpow := @SubNegMonoid.zsmul α _
    zpow_zero' := SubNegMonoid.zsmul_zero'
    zpow_succ' := SubNegMonoid.zsmul_succ'
    zpow_neg' := SubNegMonoid.zsmul_neg' }

instance [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.hasInvolutiveNeg with
    neg_add_rev := @mul_inv_rev _ _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right _ _ }

instance [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.hasInvolutiveInv with
    mul_inv_rev := @neg_add_rev _ _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right _ _ }

instance [DivisionCommMonoid α] : SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance [SubtractionCommMonoid α] : DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with add_left_neg := @mul_left_inv α _ }

instance [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with mul_left_inv := @add_left_neg α _ }

instance [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

instance [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

open Multiplicative (ofAdd)

open Additive (ofMul)

#print AddMonoidHom.toMultiplicative /-
/-- Reinterpret `α →+ β` as `multiplicative α →* multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative [AddZeroClass α] [AddZeroClass β] :
    (α →+ β) ≃
      (Multiplicative α →*
        Multiplicative
          β) where 
  toFun f := ⟨fun a => ofAdd (f a.toAdd), f.2, f.3⟩
  invFun f := ⟨fun a => (f (ofAdd a)).toAdd, f.2, f.3⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align add_monoid_hom.to_multiplicative AddMonoidHom.toMultiplicative
-/

#print MonoidHom.toAdditive /-
/-- Reinterpret `α →* β` as `additive α →+ additive β`. -/
@[simps]
def MonoidHom.toAdditive [MulOneClass α] [MulOneClass β] :
    (α →* β) ≃
      (Additive α →+
        Additive β) where 
  toFun f := ⟨fun a => ofMul (f a.toMul), f.2, f.3⟩
  invFun f := ⟨fun a => (f (ofMul a)).toMul, f.2, f.3⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align monoid_hom.to_additive MonoidHom.toAdditive
-/

#print AddMonoidHom.toMultiplicative' /-
/-- Reinterpret `additive α →+ β` as `α →* multiplicative β`. -/
@[simps]
def AddMonoidHom.toMultiplicative' [MulOneClass α] [AddZeroClass β] :
    (Additive α →+ β) ≃
      (α →*
        Multiplicative
          β) where 
  toFun f := ⟨fun a => ofAdd (f (ofMul a)), f.2, f.3⟩
  invFun f := ⟨fun a => (f a.toMul).toAdd, f.2, f.3⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align add_monoid_hom.to_multiplicative' AddMonoidHom.toMultiplicative'
-/

#print MonoidHom.toAdditive' /-
/-- Reinterpret `α →* multiplicative β` as `additive α →+ β`. -/
@[simps]
def MonoidHom.toAdditive' [MulOneClass α] [AddZeroClass β] :
    (α →* Multiplicative β) ≃ (Additive α →+ β) :=
  AddMonoidHom.toMultiplicative'.symm
#align monoid_hom.to_additive' MonoidHom.toAdditive'
-/

#print AddMonoidHom.toMultiplicative'' /-
/-- Reinterpret `α →+ additive β` as `multiplicative α →* β`. -/
@[simps]
def AddMonoidHom.toMultiplicative'' [AddZeroClass α] [MulOneClass β] :
    (α →+ Additive β) ≃
      (Multiplicative α →*
        β) where 
  toFun f := ⟨fun a => (f a.toAdd).toMul, f.2, f.3⟩
  invFun f := ⟨fun a => ofMul (f (ofAdd a)), f.2, f.3⟩
  left_inv x := by 
    ext
    rfl
  right_inv x := by 
    ext
    rfl
#align add_monoid_hom.to_multiplicative'' AddMonoidHom.toMultiplicative''
-/

#print MonoidHom.toAdditive'' /-
/-- Reinterpret `multiplicative α →* β` as `α →+ additive β`. -/
@[simps]
def MonoidHom.toAdditive'' [AddZeroClass α] [MulOneClass β] :
    (Multiplicative α →* β) ≃ (α →+ Additive β) :=
  AddMonoidHom.toMultiplicative''.symm
#align monoid_hom.to_additive'' MonoidHom.toAdditive''
-/

#print Additive.coeToFun /-
/-- If `α` has some multiplicative structure and coerces to a function,
then `additive α` should also coerce to the same function.

This allows `additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Additive.coeToFun {α : Type _} {β : α → Sort _} [CoeFun α β] :
    CoeFun (Additive α) fun a => β a.toMul :=
  ⟨fun a => coeFn a.toMul⟩
#align additive.has_coe_to_fun Additive.coeToFun
-/

#print Multiplicative.coeToFun /-
/-- If `α` has some additive structure and coerces to a function,
then `multiplicative α` should also coerce to the same function.

This allows `multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
instance Multiplicative.coeToFun {α : Type _} {β : α → Sort _} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β a.toAdd :=
  ⟨fun a => coeFn a.toAdd⟩
#align multiplicative.has_coe_to_fun Multiplicative.coeToFun
-/

