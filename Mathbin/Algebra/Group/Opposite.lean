/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Algebra.Group.InjSurj
import Algebra.Group.Commute.Defs
import Algebra.Group.Equiv.Basic
import Algebra.Opposites
import Data.Int.Cast.Defs

#align_import algebra.group.opposite from "leanprover-community/mathlib"@"0372d31fb681ef40a687506bc5870fd55ebc8bb9"

/-!
# Group structures on the multiplicative and additive opposites

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v

variable (α : Type u)

namespace MulOpposite

/-!
### Additive structures on `αᵐᵒᵖ`
-/


@[to_additive]
instance [NatCast α] : NatCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

@[to_additive]
instance [IntCast α] : IntCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

instance [AddSemigroup α] : AddSemigroup αᵐᵒᵖ :=
  unop_injective.AddSemigroup _ fun x y => rfl

instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.AddLeftCancelSemigroup _ fun x y => rfl

instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.AddRightCancelSemigroup _ fun x y => rfl

instance [AddCommSemigroup α] : AddCommSemigroup αᵐᵒᵖ :=
  unop_injective.AddCommSemigroup _ fun x y => rfl

instance [AddZeroClass α] : AddZeroClass αᵐᵒᵖ :=
  unop_injective.AddZeroClass _ rfl fun x y => rfl

instance [AddMonoid α] : AddMonoid αᵐᵒᵖ :=
  unop_injective.AddMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommMonoid α] : AddCommMonoid αᵐᵒᵖ :=
  unop_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [AddMonoidWithOne α] : AddMonoidWithOne αᵐᵒᵖ :=
  { MulOpposite.addMonoid α, MulOpposite.hasOne α,
    MulOpposite.hasNatCast
      _ with
    natCast_zero := show op ((0 : ℕ) : α) = 0 by rw [Nat.cast_zero, op_zero]
    natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op (n : ℕ) + 1 by simp }

instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α, MulOpposite.addCommMonoid α with }

instance [SubNegMonoid α] : SubNegMonoid αᵐᵒᵖ :=
  unop_injective.SubNegMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroup α] : AddGroup αᵐᵒᵖ :=
  unop_injective.AddGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

instance [AddCommGroup α] : AddCommGroup αᵐᵒᵖ :=
  unop_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroupWithOne α] : AddGroupWithOne αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α,
    MulOpposite.addGroup α with
    intCast := fun n => op n
    intCast_ofNat := fun n => show op ((n : ℤ) : α) = op n by rw [Int.cast_natCast]
    intCast_negSucc := fun n =>
      show op _ = op (-unop (op ((n + 1 : ℕ) : α))) by erw [unop_op, Int.cast_negSucc] <;> rfl }

instance [AddCommGroupWithOne α] : AddCommGroupWithOne αᵐᵒᵖ :=
  { MulOpposite.addGroupWithOne α, MulOpposite.addCommGroup α with }

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/


@[to_additive]
instance [Semigroup α] : Semigroup αᵐᵒᵖ :=
  { MulOpposite.hasMul α with
    mul_assoc := fun x y z => unop_injective <| Eq.symm <| mul_assoc (unop z) (unop y) (unop x) }

@[to_additive]
instance [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ :=
  { MulOpposite.semigroup α with
    hMul_left_cancel := fun x y z H => unop_injective <| mul_right_cancel <| op_injective H }

@[to_additive]
instance [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ :=
  { MulOpposite.semigroup α with
    hMul_right_cancel := fun x y z H => unop_injective <| mul_left_cancel <| op_injective H }

@[to_additive]
instance [CommSemigroup α] : CommSemigroup αᵐᵒᵖ :=
  { MulOpposite.semigroup α with
    mul_comm := fun x y => unop_injective <| mul_comm (unop y) (unop x) }

@[to_additive]
instance [MulOneClass α] : MulOneClass αᵐᵒᵖ :=
  { MulOpposite.hasMul α,
    MulOpposite.hasOne
      α with
    one_mul := fun x => unop_injective <| mul_one <| unop x
    mul_one := fun x => unop_injective <| one_mul <| unop x }

@[to_additive]
instance [Monoid α] : Monoid αᵐᵒᵖ :=
  { MulOpposite.semigroup α,
    MulOpposite.mulOneClass α with
    npow := fun n x => op <| x.unop ^ n
    npow_zero := fun x => unop_injective <| Monoid.npow_zero x.unop
    npow_succ := fun n x => unop_injective <| pow_succ x.unop n }

@[to_additive]
instance [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ :=
  { MulOpposite.leftCancelSemigroup α, MulOpposite.monoid α with }

@[to_additive]
instance [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ :=
  { MulOpposite.rightCancelSemigroup α, MulOpposite.monoid α with }

@[to_additive]
instance [CancelMonoid α] : CancelMonoid αᵐᵒᵖ :=
  { MulOpposite.rightCancelMonoid α, MulOpposite.leftCancelMonoid α with }

@[to_additive]
instance [CommMonoid α] : CommMonoid αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.commSemigroup α with }

@[to_additive]
instance [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ :=
  { MulOpposite.cancelMonoid α, MulOpposite.commMonoid α with }

@[to_additive AddOpposite.subNegMonoid]
instance [DivInvMonoid α] : DivInvMonoid αᵐᵒᵖ :=
  { MulOpposite.monoid α,
    MulOpposite.hasInv α with
    zpow := fun n x => op <| x.unop ^ n
    zpow_zero' := fun x => unop_injective <| DivInvMonoid.zpow_zero' x.unop
    zpow_succ' := fun n x =>
      unop_injective <| by rw [unop_op, zpow_natCast, zpow_natCast, pow_succ, unop_mul, unop_op]
    zpow_neg' := fun z x => unop_injective <| DivInvMonoid.zpow_neg' z x.unop }

@[to_additive AddOpposite.subtractionMonoid]
instance [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ :=
  { MulOpposite.divInvMonoid α,
    MulOpposite.hasInvolutiveInv
      α with
    mul_inv_rev := fun a b => unop_injective <| mul_inv_rev _ _
    inv_eq_of_hMul := fun a b h => unop_injective <| inv_eq_of_mul_eq_one_left <| congr_arg unop h }

@[to_additive AddOpposite.subtractionCommMonoid]
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ :=
  { MulOpposite.divisionMonoid α, MulOpposite.commSemigroup α with }

@[to_additive]
instance [Group α] : Group αᵐᵒᵖ :=
  { MulOpposite.divInvMonoid α with
    hMul_left_inv := fun x => unop_injective <| mul_inv_self <| unop x }

@[to_additive]
instance [CommGroup α] : CommGroup αᵐᵒᵖ :=
  { MulOpposite.group α, MulOpposite.commMonoid α with }

variable {α}

#print MulOpposite.op_natCast /-
@[simp, norm_cast, to_additive]
theorem op_natCast [NatCast α] (n : ℕ) : op (n : α) = n :=
  rfl
#align mul_opposite.op_nat_cast MulOpposite.op_natCast
#align add_opposite.op_nat_cast AddOpposite.op_natCast
-/

#print MulOpposite.op_intCast /-
@[simp, norm_cast, to_additive]
theorem op_intCast [IntCast α] (n : ℤ) : op (n : α) = n :=
  rfl
#align mul_opposite.op_int_cast MulOpposite.op_intCast
#align add_opposite.op_int_cast AddOpposite.op_intCast
-/

#print MulOpposite.unop_natCast /-
@[simp, norm_cast, to_additive]
theorem unop_natCast [NatCast α] (n : ℕ) : unop (n : αᵐᵒᵖ) = n :=
  rfl
#align mul_opposite.unop_nat_cast MulOpposite.unop_natCast
#align add_opposite.unop_nat_cast AddOpposite.unop_natCast
-/

#print MulOpposite.unop_intCast /-
@[simp, norm_cast, to_additive]
theorem unop_intCast [IntCast α] (n : ℤ) : unop (n : αᵐᵒᵖ) = n :=
  rfl
#align mul_opposite.unop_int_cast MulOpposite.unop_intCast
#align add_opposite.unop_int_cast AddOpposite.unop_intCast
-/

#print MulOpposite.unop_div /-
@[simp, to_additive]
theorem unop_div [DivInvMonoid α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl
#align mul_opposite.unop_div MulOpposite.unop_div
#align add_opposite.unop_sub AddOpposite.unop_sub
-/

#print MulOpposite.op_div /-
@[simp, to_additive]
theorem op_div [DivInvMonoid α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by simp [div_eq_mul_inv]
#align mul_opposite.op_div MulOpposite.op_div
#align add_opposite.op_sub AddOpposite.op_sub
-/

#print MulOpposite.semiconjBy_op /-
@[simp, to_additive]
theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]
#align mul_opposite.semiconj_by_op MulOpposite.semiconjBy_op
#align add_opposite.semiconj_by_op AddOpposite.addSemiconjBy_op
-/

#print MulOpposite.semiconjBy_unop /-
@[simp, to_additive]
theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconj_by_op]
#align mul_opposite.semiconj_by_unop MulOpposite.semiconjBy_unop
#align add_opposite.semiconj_by_unop AddOpposite.addSemiconjBy_unop
-/

#print SemiconjBy.op /-
@[to_additive]
theorem SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) :=
  semiconjBy_op.2 h
#align semiconj_by.op SemiconjBy.op
#align add_semiconj_by.op AddSemiconjBy.op
-/

#print SemiconjBy.unop /-
@[to_additive]
theorem SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) :=
  semiconjBy_unop.2 h
#align semiconj_by.unop SemiconjBy.unop
#align add_semiconj_by.unop AddSemiconjBy.unop
-/

#print Commute.op /-
@[to_additive]
theorem Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  h.op
#align commute.op Commute.op
#align add_commute.op AddCommute.op
-/

#print Commute.unop /-
@[to_additive]
theorem Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) : Commute (unop x) (unop y) :=
  h.unop
#align mul_opposite.commute.unop Commute.unop
#align add_opposite.commute.unop AddCommute.unop
-/

#print MulOpposite.commute_op /-
@[simp, to_additive]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconjBy_op
#align mul_opposite.commute_op MulOpposite.commute_op
#align add_opposite.commute_op AddOpposite.addCommute_op
-/

#print MulOpposite.commute_unop /-
@[simp, to_additive]
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconjBy_unop
#align mul_opposite.commute_unop MulOpposite.commute_unop
#align add_opposite.commute_unop AddOpposite.addCommute_unop
-/

#print MulOpposite.opAddEquiv /-
/-- The function `mul_opposite.op` is an additive equivalence. -/
@[simps (config :=
      { fullyApplied := false
        simpRhs := true })]
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ :=
  { opEquiv with map_add' := fun a b => rfl }
#align mul_opposite.op_add_equiv MulOpposite.opAddEquiv
-/

#print MulOpposite.opAddEquiv_toEquiv /-
@[simp]
theorem opAddEquiv_toEquiv [Add α] : (opAddEquiv : α ≃+ αᵐᵒᵖ).toEquiv = opEquiv :=
  rfl
#align mul_opposite.op_add_equiv_to_equiv MulOpposite.opAddEquiv_toEquiv
-/

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

instance [Semigroup α] : Semigroup αᵃᵒᵖ :=
  unop_injective.Semigroup _ fun x y => rfl

instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.LeftCancelSemigroup _ fun x y => rfl

instance [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.RightCancelSemigroup _ fun x y => rfl

instance [CommSemigroup α] : CommSemigroup αᵃᵒᵖ :=
  unop_injective.CommSemigroup _ fun x y => rfl

instance [MulOneClass α] : MulOneClass αᵃᵒᵖ :=
  unop_injective.MulOneClass _ rfl fun x y => rfl

instance {β} [Pow α β] : Pow αᵃᵒᵖ β where pow a b := op (unop a ^ b)

#print AddOpposite.op_pow /-
@[simp]
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl
#align add_opposite.op_pow AddOpposite.op_pow
-/

#print AddOpposite.unop_pow /-
@[simp]
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl
#align add_opposite.unop_pow AddOpposite.unop_pow
-/

instance [Monoid α] : Monoid αᵃᵒᵖ :=
  unop_injective.Monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [CommMonoid α] : CommMonoid αᵃᵒᵖ :=
  unop_injective.CommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [DivInvMonoid α] : DivInvMonoid αᵃᵒᵖ :=
  unop_injective.DivInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Group α] : Group αᵃᵒᵖ :=
  unop_injective.Group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

instance [CommGroup α] : CommGroup αᵃᵒᵖ :=
  unop_injective.CommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

-- NOTE: `add_monoid_with_one α → add_monoid_with_one αᵃᵒᵖ` does not hold
instance [AddCommMonoidWithOne α] : AddCommMonoidWithOne αᵃᵒᵖ :=
  { AddOpposite.addCommMonoid α, AddOpposite.hasOne,
    AddOpposite.hasNatCast
      _ with
    natCast_zero := show op ((0 : ℕ) : α) = 0 by rw [Nat.cast_zero, op_zero]
    natCast_succ := show ∀ n, op ((n + 1 : ℕ) : α) = op (n : ℕ) + 1 by simp [add_comm] }

instance [AddCommGroupWithOne α] : AddCommGroupWithOne αᵃᵒᵖ :=
  { AddOpposite.addCommMonoidWithOne _, AddOpposite.addCommGroup α,
    AddOpposite.hasIntCast
      α with
    intCast_ofNat := fun n => congr_arg op <| Int.cast_natCast n
    intCast_negSucc := fun _ => congr_arg op <| Int.cast_negSucc _ }

variable {α}

#print AddOpposite.opMulEquiv /-
/-- The function `add_opposite.op` is a multiplicative equivalence. -/
@[simps (config :=
      { fullyApplied := false
        simpRhs := true })]
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ :=
  { opEquiv with map_mul' := fun a b => rfl }
#align add_opposite.op_mul_equiv AddOpposite.opMulEquiv
-/

#print AddOpposite.opMulEquiv_toEquiv /-
@[simp]
theorem opMulEquiv_toEquiv [Mul α] : (opMulEquiv : α ≃* αᵃᵒᵖ).toEquiv = opEquiv :=
  rfl
#align add_opposite.op_mul_equiv_to_equiv AddOpposite.opMulEquiv_toEquiv
-/

end AddOpposite

open MulOpposite

#print MulEquiv.inv' /-
/-- Inversion on a group is a `mul_equiv` to the opposite group. When `G` is commutative, there is
`mul_equiv.inv`. -/
@[to_additive
      "Negation on an additive group is an `add_equiv` to the opposite group. When `G`\nis commutative, there is `add_equiv.inv`.",
  simps (config :=
      { fullyApplied := false
        simpRhs := true })]
def MulEquiv.inv' (G : Type _) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equiv.inv G).trans opEquiv with map_mul' := fun x y => unop_injective <| mul_inv_rev x y }
#align mul_equiv.inv' MulEquiv.inv'
#align add_equiv.neg' AddEquiv.neg'
-/

#print MulHom.toOpposite /-
/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive
      "An additive semigroup homomorphism `f : add_hom M N` such that `f x` additively\ncommutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MulHom.toOpposite {M N : Type _} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ
    where
  toFun := MulOpposite.op ∘ f
  map_mul' x y := by simp [(hf x y).Eq]
#align mul_hom.to_opposite MulHom.toOpposite
#align add_hom.to_opposite AddHom.toOpposite
-/

#print MulHom.fromOpposite /-
/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive
      "An additive semigroup homomorphism `f : add_hom M N` such that `f x` additively\ncommutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MulHom.fromOpposite {M N : Type _} [Mul M] [Mul N] (f : M →ₙ* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →ₙ* N
    where
  toFun := f ∘ MulOpposite.unop
  map_mul' x y := (f.map_hMul _ _).trans (hf _ _).Eq
#align mul_hom.from_opposite MulHom.fromOpposite
#align add_hom.from_opposite AddHom.fromOpposite
-/

#print MonoidHom.toOpposite /-
/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes\nwith `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MonoidHom.toOpposite {M N : Type _} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →* Nᵐᵒᵖ
    where
  toFun := MulOpposite.op ∘ f
  map_one' := congr_arg op f.map_one
  map_mul' x y := by simp [(hf x y).Eq]
#align monoid_hom.to_opposite MonoidHom.toOpposite
#align add_monoid_hom.to_opposite AddMonoidHom.toOpposite
-/

#print MonoidHom.fromOpposite /-
/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes\nwith `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MonoidHom.fromOpposite {M N : Type _} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →* N
    where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' x y := (f.map_hMul _ _).trans (hf _ _).Eq
#align monoid_hom.from_opposite MonoidHom.fromOpposite
#align add_monoid_hom.from_opposite AddMonoidHom.fromOpposite
-/

#print Units.opEquiv /-
/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive
      "The additive units of the additive opposites are equivalent to the additive opposites\nof the additive units."]
def Units.opEquiv {M} [Monoid M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ
    where
  toFun u := op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
  invFun := MulOpposite.rec' fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective <| u.4, unop_injective u.3⟩
  map_mul' x y := unop_injective <| Units.ext <| rfl
  left_inv x := Units.ext <| by simp
  right_inv x := unop_injective <| Units.ext <| rfl
#align units.op_equiv Units.opEquiv
#align add_units.op_equiv AddUnits.opEquiv
-/

#print Units.coe_unop_opEquiv /-
@[simp, to_additive]
theorem Units.coe_unop_opEquiv {M} [Monoid M] (u : Mᵐᵒᵖˣ) :
    ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl
#align units.coe_unop_op_equiv Units.coe_unop_opEquiv
#align add_units.coe_unop_op_equiv AddUnits.coe_unop_opEquiv
-/

#print Units.coe_opEquiv_symm /-
@[simp, to_additive]
theorem Units.coe_opEquiv_symm {M} [Monoid M] (u : Mˣᵐᵒᵖ) :
    (Units.opEquiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
  rfl
#align units.coe_op_equiv_symm Units.coe_opEquiv_symm
#align add_units.coe_op_equiv_symm AddUnits.coe_opEquiv_symm
-/

#print IsUnit.op /-
@[to_additive]
theorem IsUnit.op {M} [Monoid M] {m : M} (h : IsUnit m) : IsUnit (op m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨Units.opEquiv.symm (op u), rfl⟩
#align is_unit.op IsUnit.op
#align is_add_unit.op IsAddUnit.op
-/

#print IsUnit.unop /-
@[to_additive]
theorem IsUnit.unop {M} [Monoid M] {m : Mᵐᵒᵖ} (h : IsUnit m) : IsUnit (unop m) :=
  let ⟨u, hu⟩ := h
  hu ▸ ⟨unop (Units.opEquiv u), rfl⟩
#align is_unit.unop IsUnit.unop
#align is_add_unit.unop IsAddUnit.unop
-/

#print isUnit_op /-
@[simp, to_additive]
theorem isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m :=
  ⟨IsUnit.unop, IsUnit.op⟩
#align is_unit_op isUnit_op
#align is_add_unit_op isAddUnit_op
-/

#print isUnit_unop /-
@[simp, to_additive]
theorem isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m :=
  ⟨IsUnit.op, IsUnit.unop⟩
#align is_unit_unop isUnit_unop
#align is_add_unit_unop isAddUnit_unop
-/

#print MulHom.op /-
/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive
      "An additive semigroup homomorphism `add_hom M N` can equivalently be viewed as an\nadditive semigroup homomorphism `add_hom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the (fully faithful)\n`ᵃᵒᵖ`-functor on morphisms.",
  simps]
def MulHom.op {M N} [Mul M] [Mul N] : (M →ₙ* N) ≃ (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ)
    where
  toFun f :=
    { toFun := op ∘ f ∘ unop
      map_mul' := fun x y => unop_injective (f.map_hMul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ op
      map_mul' := fun x y => congr_arg unop (f.map_hMul (op y) (op x)) }
  left_inv f := by ext; rfl
  right_inv f := by ext x; simp
#align mul_hom.op MulHom.op
#align add_hom.op AddHom.op
-/

#print MulHom.unop /-
/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `mul_hom.op`. -/
@[simp,
  to_additive
      "The 'unopposite' of an additive semigroup homomorphism `Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse\nto `add_hom.op`."]
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) :=
  MulHom.op.symm
#align mul_hom.unop MulHom.unop
#align add_hom.unop AddHom.unop
-/

#print AddHom.mulOp /-
/-- An additive semigroup homomorphism `add_hom M N` can equivalently be viewed as an additive
homomorphism `add_hom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
def AddHom.mulOp {M N} [Add M] [Add N] : AddHom M N ≃ AddHom Mᵐᵒᵖ Nᵐᵒᵖ
    where
  toFun f :=
    { toFun := op ∘ f ∘ unop
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ op
      map_add' := fun x y => congr_arg unop (f.map_add (op x) (op y)) }
  left_inv f := by ext; rfl
  right_inv f := by ext; simp
#align add_hom.mul_op AddHom.mulOp
-/

#print AddHom.mulUnop /-
/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`add_hom.mul_op`. -/
@[simp]
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm
#align add_hom.mul_unop AddHom.mulUnop
-/

#print MonoidHom.op /-
/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive
      "An additive monoid homomorphism `M →+ N` can equivalently be viewed as an\nadditive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)\n`ᵃᵒᵖ`-functor on morphisms.",
  simps]
def MonoidHom.op {M N} [MulOneClass M] [MulOneClass N] : (M →* N) ≃ (Mᵐᵒᵖ →* Nᵐᵒᵖ)
    where
  toFun f :=
    { toFun := op ∘ f ∘ unop
      map_one' := congr_arg op f.map_one
      map_mul' := fun x y => unop_injective (f.map_hMul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ op
      map_one' := congr_arg unop f.map_one
      map_mul' := fun x y => congr_arg unop (f.map_hMul (op y) (op x)) }
  left_inv f := by ext; rfl
  right_inv f := by ext x; simp
#align monoid_hom.op MonoidHom.op
#align add_monoid_hom.op AddMonoidHom.op
-/

#print MonoidHom.unop /-
/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `monoid_hom.op`. -/
@[simp,
  to_additive
      "The 'unopposite' of an additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to\n`add_monoid_hom.op`."]
def MonoidHom.unop {M N} [MulOneClass M] [MulOneClass N] : (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) :=
  MonoidHom.op.symm
#align monoid_hom.unop MonoidHom.unop
#align add_monoid_hom.unop AddMonoidHom.unop
-/

#print AddMonoidHom.mulOp /-
/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.mulOp {M N} [AddZeroClass M] [AddZeroClass N] : (M →+ N) ≃ (Mᵐᵒᵖ →+ Nᵐᵒᵖ)
    where
  toFun f :=
    { toFun := op ∘ f ∘ unop
      map_zero' := unop_injective f.map_zero
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ op
      map_zero' := congr_arg unop f.map_zero
      map_add' := fun x y => congr_arg unop (f.map_add (op x) (op y)) }
  left_inv f := by ext; rfl
  right_inv f := by ext; simp
#align add_monoid_hom.mul_op AddMonoidHom.mulOp
-/

#print AddMonoidHom.mulUnop /-
/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`add_monoid_hom.mul_op`. -/
@[simp]
def AddMonoidHom.mulUnop {α β} [AddZeroClass α] [AddZeroClass β] : (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) :=
  AddMonoidHom.mulOp.symm
#align add_monoid_hom.mul_unop AddMonoidHom.mulUnop
-/

#print AddEquiv.mulOp /-
/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ)
    where
  toFun f := opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun f := opAddEquiv.trans (f.trans opAddEquiv.symm)
  left_inv f := by ext; rfl
  right_inv f := by ext; simp
#align add_equiv.mul_op AddEquiv.mulOp
-/

#print AddEquiv.mulUnop /-
/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `add_equiv.mul_op`. -/
@[simp]
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm
#align add_equiv.mul_unop AddEquiv.mulUnop
-/

#print MulEquiv.op /-
/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive "A iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`.", simps]
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ)
    where
  toFun f :=
    { toFun := op ∘ f ∘ unop
      invFun := op ∘ f.symm ∘ unop
      left_inv := fun x => unop_injective (f.symm_apply_apply x.unop)
      right_inv := fun x => unop_injective (f.apply_symm_apply x.unop)
      map_mul' := fun x y => unop_injective (f.map_hMul y.unop x.unop) }
  invFun f :=
    { toFun := unop ∘ f ∘ op
      invFun := unop ∘ f.symm ∘ op
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_mul' := fun x y => congr_arg unop (f.map_hMul (op y) (op x)) }
  left_inv f := by ext; rfl
  right_inv f := by ext; simp
#align mul_equiv.op MulEquiv.op
#align add_equiv.op AddEquiv.op
-/

#print MulEquiv.unop /-
/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `mul_equiv.op`. -/
@[simp, to_additive "The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `add_equiv.op`."]
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) :=
  MulEquiv.op.symm
#align mul_equiv.unop MulEquiv.unop
#align add_equiv.unop AddEquiv.unop
-/

section Ext

#print AddMonoidHom.mul_op_ext /-
/-- This ext lemma change equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `finsupp.add_hom_ext'`. -/
@[ext]
theorem AddMonoidHom.mul_op_ext {α β} [AddZeroClass α] [AddZeroClass β] (f g : αᵐᵒᵖ →+ β)
    (h :
      f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom =
        g.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) :
    f = g :=
  AddMonoidHom.ext <| MulOpposite.rec' fun x => (AddMonoidHom.congr_fun h : _) x
#align add_monoid_hom.mul_op_ext AddMonoidHom.mul_op_ext
-/

end Ext

