/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Algebra.Group.WithOne.Defs
import Algebra.Group.Equiv.Basic

#align_import algebra.group.with_one.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# More operations on `with_one` and `with_zero`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines various bundled morphisms on `with_one` and `with_zero`
that were not available in `algebra/group/with_one/defs`.

## Main definitions

* `with_one.lift`, `with_zero.lift`
* `with_one.map`, `with_zero.map`
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

section

#print WithOne.coeMulHom /-
-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' x y := rfl
#align with_one.coe_mul_hom WithOne.coeMulHom
#align with_zero.coe_add_hom WithZero.coeAddHom
-/

end

section lift

attribute [local semireducible] WithOne WithZero

variable [Mul α] [MulOneClass β]

#print WithOne.lift /-
/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift : (α →ₙ* β) ≃ (WithOne α →* β)
    where
  toFun f :=
    { toFun := fun x => Option.casesOn x 1 f
      map_one' := rfl
      map_mul' := fun x y =>
        WithOne.cases_on x (by rw [one_mul]; exact (one_mul _).symm) fun x =>
          WithOne.cases_on y (by rw [mul_one]; exact (mul_one _).symm) fun y => f.map_hMul x y }
  invFun F := F.toMulHom.comp coeMulHom
  left_inv f := MulHom.ext fun x => rfl
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm fun x => rfl
#align with_one.lift WithOne.lift
#align with_zero.lift WithZero.lift
-/

variable (f : α →ₙ* β)

#print WithOne.lift_coe /-
@[simp, to_additive]
theorem lift_coe (x : α) : lift f x = f x :=
  rfl
#align with_one.lift_coe WithOne.lift_coe
#align with_zero.lift_coe WithZero.lift_coe
-/

#print WithOne.lift_one /-
@[simp, to_additive]
theorem lift_one : lift f 1 = 1 :=
  rfl
#align with_one.lift_one WithOne.lift_one
#align with_zero.lift_zero WithZero.lift_zero
-/

#print WithOne.lift_unique /-
@[to_additive]
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm
#align with_one.lift_unique WithOne.lift_unique
#align with_zero.lift_unique WithZero.lift_unique
-/

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

#print WithOne.map /-
/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive
      "Given an additive map from `α → β` returns an add_monoid homomorphism\n  from `with_zero α` to `with_zero β`"]
def map (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)
#align with_one.map WithOne.map
#align with_zero.map WithZero.map
-/

#print WithOne.map_coe /-
@[simp, to_additive]
theorem map_coe (f : α →ₙ* β) (a : α) : map f (a : WithOne α) = f a :=
  lift_coe _ _
#align with_one.map_coe WithOne.map_coe
#align with_zero.map_coe WithZero.map_coe
-/

#print WithOne.map_id /-
@[simp, to_additive]
theorem map_id : map (MulHom.id α) = MonoidHom.id (WithOne α) := by ext;
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_id WithOne.map_id
#align with_zero.map_id WithZero.map_id
-/

#print WithOne.map_map /-
@[to_additive]
theorem map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) : map g (map f x) = map (g.comp f) x := by
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_map WithOne.map_map
#align with_zero.map_map WithZero.map_map
-/

#print WithOne.map_comp /-
@[simp, to_additive]
theorem map_comp (f : α →ₙ* β) (g : β →ₙ* γ) : map (g.comp f) = (map g).comp (map f) :=
  MonoidHom.ext fun x => (map_map f g x).symm
#align with_one.map_comp WithOne.map_comp
#align with_zero.map_comp WithZero.map_comp
-/

#print MulEquiv.withOneCongr /-
/-- A version of `equiv.option_congr` for `with_one`. -/
@[to_additive "A version of `equiv.option_congr` for `with_zero`.", simps apply]
def MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { map e.toMulHom with
    toFun := map e.toMulHom
    invFun := map e.symm.toMulHom
    left_inv := fun x => (map_map _ _ _).trans <| by induction x using WithOne.cases_on <;> · simp
    right_inv := fun x =>
      (map_map _ _ _).trans <| by induction x using WithOne.cases_on <;> · simp }
#align mul_equiv.with_one_congr MulEquiv.withOneCongr
#align add_equiv.with_zero_congr AddEquiv.withZeroCongr
-/

#print MulEquiv.withOneCongr_refl /-
@[simp]
theorem MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective map_id
#align mul_equiv.with_one_congr_refl MulEquiv.withOneCongr_refl
-/

#print MulEquiv.withOneCongr_symm /-
@[simp]
theorem MulEquiv.withOneCongr_symm (e : α ≃* β) : e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl
#align mul_equiv.with_one_congr_symm MulEquiv.withOneCongr_symm
-/

#print MulEquiv.withOneCongr_trans /-
@[simp]
theorem MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (map_comp _ _).symm
#align mul_equiv.with_one_congr_trans MulEquiv.withOneCongr_trans
-/

end Map

end WithOne

