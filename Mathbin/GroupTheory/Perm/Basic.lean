/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module group_theory.perm.basic
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Logic.Equiv.Set

/-!
# The group of permutations (self-equivalences) of a type `α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `group` structure on `equiv.perm α`.
-/


universe u v

namespace Equiv

variable {α : Type u} {β : Type v}

namespace Perm

#print Equiv.Perm.permGroup /-
instance permGroup : Group (Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  mul_left_inv := self_trans_symm
#align equiv.perm.perm_group Equiv.Perm.permGroup
-/

/- warning: equiv.perm.default_eq -> Equiv.Perm.default_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inhabited.default.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.inhabited'.{succ u1} α)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inhabited.default.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.inhabited'.{succ u1} α)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.default_eq Equiv.Perm.default_eqₓ'. -/
@[simp]
theorem default_eq : (default : Perm α) = 1 :=
  rfl
#align equiv.perm.default_eq Equiv.Perm.default_eq

/- warning: equiv.perm.equiv_units_End -> Equiv.Perm.equivUnitsEnd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, MulEquiv.{u1, u1} (Equiv.Perm.{succ u1} α) (Units.{u1} (Function.End.{u1} α) (Function.End.monoid.{u1} α)) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toHasMul.{u1} (Units.{u1} (Function.End.{u1} α) (Function.End.monoid.{u1} α)) (Units.mulOneClass.{u1} (Function.End.{u1} α) (Function.End.monoid.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, MulEquiv.{u1, u1} (Equiv.Perm.{succ u1} α) (Units.{u1} (Function.End.{u1} α) (instMonoidEnd.{u1} α)) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toMul.{u1} (Units.{u1} (Function.End.{u1} α) (instMonoidEnd.{u1} α)) (Units.instMulOneClassUnits.{u1} (Function.End.{u1} α) (instMonoidEnd.{u1} α)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.equiv_units_End Equiv.Perm.equivUnitsEndₓ'. -/
/-- The permutation of a type is equivalent to the units group of the endomorphisms monoid of this
type. -/
@[simps]
def equivUnitsEnd : Perm α ≃* Units (Function.End α)
    where
  toFun e := ⟨e, e.symm, e.self_comp_symm, e.symm_comp_self⟩
  invFun u :=
    ⟨(u : Function.End α), (↑u⁻¹ : Function.End α), congr_fun u.inv_val, congr_fun u.val_inv⟩
  left_inv e := ext fun x => rfl
  right_inv u := Units.ext rfl
  map_mul' e₁ e₂ := rfl
#align equiv.perm.equiv_units_End Equiv.Perm.equivUnitsEnd

/- warning: monoid_hom.to_hom_perm -> MonoidHom.toHomPerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G], (MonoidHom.{u2, u1} G (Function.End.{u1} α) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} (Function.End.{u1} α) (Function.End.monoid.{u1} α))) -> (MonoidHom.{u2, u1} G (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G], (MonoidHom.{u2, u1} G (Function.End.{u1} α) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} (Function.End.{u1} α) (instMonoidEnd.{u1} α))) -> (MonoidHom.{u2, u1} G (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_hom_perm MonoidHom.toHomPermₓ'. -/
/-- Lift a monoid homomorphism `f : G →* function.End α` to a monoid homomorphism
`f : G →* equiv.perm α`. -/
@[simps]
def MonoidHom.toHomPerm {G : Type _} [Group G] (f : G →* Function.End α) : G →* Perm α :=
  equivUnitsEnd.symm.toMonoidHom.comp f.toHomUnits
#align monoid_hom.to_hom_perm MonoidHom.toHomPerm

#print Equiv.Perm.mul_apply /-
theorem mul_apply (f g : Perm α) (x) : (f * g) x = f (g x) :=
  Equiv.trans_apply _ _ _
#align equiv.perm.mul_apply Equiv.Perm.mul_apply
-/

#print Equiv.Perm.one_apply /-
theorem one_apply (x) : (1 : Perm α) x = x :=
  rfl
#align equiv.perm.one_apply Equiv.Perm.one_apply
-/

#print Equiv.Perm.inv_apply_self /-
@[simp]
theorem inv_apply_self (f : Perm α) (x) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x
#align equiv.perm.inv_apply_self Equiv.Perm.inv_apply_self
-/

#print Equiv.Perm.apply_inv_self /-
@[simp]
theorem apply_inv_self (f : Perm α) (x) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x
#align equiv.perm.apply_inv_self Equiv.Perm.apply_inv_self
-/

/- warning: equiv.perm.one_def -> Equiv.Perm.one_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.Perm.{succ u1} α) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (Equiv.refl.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.Perm.{succ u1} α) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) (Equiv.refl.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align equiv.perm.one_def Equiv.Perm.one_defₓ'. -/
theorem one_def : (1 : Perm α) = Equiv.refl α :=
  rfl
#align equiv.perm.one_def Equiv.Perm.one_def

/- warning: equiv.perm.mul_def -> Equiv.Perm.mul_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α) (g : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g) (Equiv.trans.{succ u1, succ u1, succ u1} α α α g f)
but is expected to have type
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α) (g : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f g) (Equiv.trans.{succ u1, succ u1, succ u1} α α α g f)
Case conversion may be inaccurate. Consider using '#align equiv.perm.mul_def Equiv.Perm.mul_defₓ'. -/
theorem mul_def (f g : Perm α) : f * g = g.trans f :=
  rfl
#align equiv.perm.mul_def Equiv.Perm.mul_def

/- warning: equiv.perm.inv_def -> Equiv.Perm.inv_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) f) (Equiv.symm.{succ u1, succ u1} α α f)
but is expected to have type
  forall {α : Type.{u1}} (f : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f) (Equiv.symm.{succ u1, succ u1} α α f)
Case conversion may be inaccurate. Consider using '#align equiv.perm.inv_def Equiv.Perm.inv_defₓ'. -/
theorem inv_def (f : Perm α) : f⁻¹ = f.symm :=
  rfl
#align equiv.perm.inv_def Equiv.Perm.inv_def

#print Equiv.Perm.coe_one /-
@[simp, norm_cast]
theorem coe_one : ⇑(1 : Perm α) = id :=
  rfl
#align equiv.perm.coe_one Equiv.Perm.coe_one
-/

#print Equiv.Perm.coe_mul /-
@[simp, norm_cast]
theorem coe_mul (f g : Perm α) : ⇑(f * g) = f ∘ g :=
  rfl
#align equiv.perm.coe_mul Equiv.Perm.coe_mul
-/

#print Equiv.Perm.coe_pow /-
@[norm_cast]
theorem coe_pow (f : Perm α) (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _
#align equiv.perm.coe_pow Equiv.Perm.coe_pow
-/

#print Equiv.Perm.iterate_eq_pow /-
@[simp]
theorem iterate_eq_pow (f : Perm α) (n : ℕ) : f^[n] = ⇑(f ^ n) :=
  (coe_pow _ _).symm
#align equiv.perm.iterate_eq_pow Equiv.Perm.iterate_eq_pow
-/

#print Equiv.Perm.eq_inv_iff_eq /-
theorem eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
  f.eq_symm_apply
#align equiv.perm.eq_inv_iff_eq Equiv.Perm.eq_inv_iff_eq
-/

#print Equiv.Perm.inv_eq_iff_eq /-
theorem inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x = y ↔ x = f y :=
  f.symm_apply_eq
#align equiv.perm.inv_eq_iff_eq Equiv.Perm.inv_eq_iff_eq
-/

#print Equiv.Perm.zpow_apply_comm /-
theorem zpow_apply_comm {α : Type _} (σ : Perm α) (m n : ℤ) {x : α} :
    (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) := by
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, zpow_mul_comm]
#align equiv.perm.zpow_apply_comm Equiv.Perm.zpow_apply_comm
-/

#print Equiv.Perm.image_inv /-
@[simp]
theorem image_inv (f : Perm α) (s : Set α) : ⇑f⁻¹ '' s = f ⁻¹' s :=
  f⁻¹.image_eq_preimage _
#align equiv.perm.image_inv Equiv.Perm.image_inv
-/

#print Equiv.Perm.preimage_inv /-
@[simp]
theorem preimage_inv (f : Perm α) (s : Set α) : ⇑f⁻¹ ⁻¹' s = f '' s :=
  (f.image_eq_preimage _).symm
#align equiv.perm.preimage_inv Equiv.Perm.preimage_inv
-/

/-! Lemmas about mixing `perm` with `equiv`. Because we have multiple ways to express
`equiv.refl`, `equiv.symm`, and `equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/


/- warning: equiv.perm.trans_one -> Equiv.Perm.trans_one is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Type.{u2}} (e : Equiv.{u1, succ u2} α β), Eq.{max 1 (max u1 (succ u2)) (imax (succ u2) u1)} (Equiv.{u1, succ u2} α β) (Equiv.trans.{u1, succ u2, succ u2} α β β e (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (OfNat.mk.{u2} (Equiv.Perm.{succ u2} β) 1 (One.one.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))))) e
but is expected to have type
  forall {α : Sort.{u2}} {β : Type.{u1}} (e : Equiv.{u2, succ u1} α β), Eq.{max u2 (succ u1)} (Equiv.{u2, succ u1} α β) (Equiv.trans.{u2, succ u1, succ u1} α β β e (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} β) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} β) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} β) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))))))) e
Case conversion may be inaccurate. Consider using '#align equiv.perm.trans_one Equiv.Perm.trans_oneₓ'. -/
@[simp]
theorem trans_one {α : Sort _} {β : Type _} (e : α ≃ β) : e.trans (1 : Perm β) = e :=
  Equiv.trans_refl e
#align equiv.perm.trans_one Equiv.Perm.trans_one

/- warning: equiv.perm.mul_refl -> Equiv.Perm.mul_refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e (Equiv.refl.{succ u1} α)) e
but is expected to have type
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e (Equiv.refl.{succ u1} α)) e
Case conversion may be inaccurate. Consider using '#align equiv.perm.mul_refl Equiv.Perm.mul_reflₓ'. -/
@[simp]
theorem mul_refl (e : Perm α) : e * Equiv.refl α = e :=
  Equiv.trans_refl e
#align equiv.perm.mul_refl Equiv.Perm.mul_refl

/- warning: equiv.perm.one_symm -> Equiv.Perm.one_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Equiv.symm.{succ u1, succ u1} α α (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (OfNat.mk.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.one.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasOne.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Equiv.symm.{succ u1, succ u1} α α (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.toOfNat1.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toOne.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.one_symm Equiv.Perm.one_symmₓ'. -/
@[simp]
theorem one_symm : (1 : Perm α).symm = 1 :=
  Equiv.refl_symm
#align equiv.perm.one_symm Equiv.Perm.one_symm

/- warning: equiv.perm.refl_inv -> Equiv.Perm.refl_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toHasInv.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))) (Equiv.refl.{succ u1} α)) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (OfNat.mk.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.one.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasOne.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toInv.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.refl.{succ u1} α)) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.toOfNat1.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toOne.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.refl_inv Equiv.Perm.refl_invₓ'. -/
@[simp]
theorem refl_inv : (Equiv.refl α : Perm α)⁻¹ = 1 :=
  Equiv.refl_symm
#align equiv.perm.refl_inv Equiv.Perm.refl_inv

/- warning: equiv.perm.one_trans -> Equiv.Perm.one_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Sort.{u2}} (e : Equiv.{succ u1, u2} α β), Eq.{max 1 (imax (succ u1) u2) u2 (succ u1)} (Equiv.{succ u1, u2} α β) (Equiv.trans.{succ u1, succ u1, u2} α α β (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) e) e
but is expected to have type
  forall {α : Type.{u2}} {β : Sort.{u1}} (e : Equiv.{succ u2, u1} α β), Eq.{max (succ u2) u1} (Equiv.{succ u2, u1} α β) (Equiv.trans.{succ u2, succ u2, u1} α α β (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} α) 1 (One.toOfNat1.{u2} (Equiv.Perm.{succ u2} α) (InvOneClass.toOne.{u2} (Equiv.Perm.{succ u2} α) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α))))))) e) e
Case conversion may be inaccurate. Consider using '#align equiv.perm.one_trans Equiv.Perm.one_transₓ'. -/
@[simp]
theorem one_trans {α : Type _} {β : Sort _} (e : α ≃ β) : (1 : Perm α).trans e = e :=
  Equiv.refl_trans e
#align equiv.perm.one_trans Equiv.Perm.one_trans

/- warning: equiv.perm.refl_mul -> Equiv.Perm.refl_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (HMul.hMul.{u1, u1, u1} (Equiv.{succ u1, succ u1} α α) (Equiv.{succ u1, succ u1} α α) (Equiv.{succ u1, succ u1} α α) (instHMul.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasMul.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.refl.{succ u1} α) e) e
but is expected to have type
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (HMul.hMul.{u1, u1, u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.{succ u1} α) (Equiv.{succ u1, succ u1} α α) (instHMul.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toMul.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.refl.{succ u1} α) e) e
Case conversion may be inaccurate. Consider using '#align equiv.perm.refl_mul Equiv.Perm.refl_mulₓ'. -/
@[simp]
theorem refl_mul (e : Perm α) : Equiv.refl α * e = e :=
  Equiv.refl_trans e
#align equiv.perm.refl_mul Equiv.Perm.refl_mul

/- warning: equiv.perm.inv_trans_self -> Equiv.Perm.inv_trans_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Equiv.trans.{succ u1, succ u1, succ u1} α α α (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) e) e) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (OfNat.mk.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.one.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasOne.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Equiv.trans.{succ u1, succ u1, succ u1} α α α (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) e) e) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.toOfNat1.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toOne.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.inv_trans_self Equiv.Perm.inv_trans_selfₓ'. -/
@[simp]
theorem inv_trans_self (e : Perm α) : e⁻¹.trans e = 1 :=
  Equiv.symm_trans_self e
#align equiv.perm.inv_trans_self Equiv.Perm.inv_trans_self

/- warning: equiv.perm.mul_symm -> Equiv.Perm.mul_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e (Equiv.symm.{succ u1, succ u1} α α e)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e (Equiv.symm.{succ u1, succ u1} α α e)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.mul_symm Equiv.Perm.mul_symmₓ'. -/
@[simp]
theorem mul_symm (e : Perm α) : e * e.symm = 1 :=
  Equiv.symm_trans_self e
#align equiv.perm.mul_symm Equiv.Perm.mul_symm

/- warning: equiv.perm.self_trans_inv -> Equiv.Perm.self_trans_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Equiv.trans.{succ u1, succ u1, succ u1} α α α e (Inv.inv.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toHasInv.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))) e)) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (OfNat.mk.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.one.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasOne.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (Equiv.trans.{succ u1, succ u1, succ u1} α α α e (Inv.inv.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toInv.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))) e)) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.toOfNat1.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toOne.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.self_trans_inv Equiv.Perm.self_trans_invₓ'. -/
@[simp]
theorem self_trans_inv (e : Perm α) : e.trans e⁻¹ = 1 :=
  Equiv.self_trans_symm e
#align equiv.perm.self_trans_inv Equiv.Perm.self_trans_inv

/- warning: equiv.perm.symm_mul -> Equiv.Perm.symm_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (HMul.hMul.{u1, u1, u1} (Equiv.{succ u1, succ u1} α α) (Equiv.{succ u1, succ u1} α α) (Equiv.{succ u1, succ u1} α α) (instHMul.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasMul.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.symm.{succ u1, succ u1} α α e) e) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (OfNat.mk.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.one.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toHasOne.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} (e : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.{succ u1, succ u1} α α) (HMul.hMul.{u1, u1, u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.{succ u1} α) (Equiv.{succ u1, succ u1} α α) (instHMul.{u1} (Equiv.{succ u1, succ u1} α α) (MulOneClass.toMul.{u1} (Equiv.{succ u1, succ u1} α α) (Monoid.toMulOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvMonoid.toMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivInvMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.symm.{succ u1, succ u1} α α e) e) (OfNat.ofNat.{u1} (Equiv.{succ u1, succ u1} α α) 1 (One.toOfNat1.{u1} (Equiv.{succ u1, succ u1} α α) (InvOneClass.toOne.{u1} (Equiv.{succ u1, succ u1} α α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.{succ u1, succ u1} α α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Group.toDivisionMonoid.{u1} (Equiv.{succ u1, succ u1} α α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.symm_mul Equiv.Perm.symm_mulₓ'. -/
@[simp]
theorem symm_mul (e : Perm α) : e.symm * e = 1 :=
  Equiv.self_trans_symm e
#align equiv.perm.symm_mul Equiv.Perm.symm_mul

/-! Lemmas about `equiv.perm.sum_congr` re-expressed via the group structure. -/


/- warning: equiv.perm.sum_congr_mul -> Equiv.Perm.sumCongr_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) (f : Equiv.Perm.{succ u2} β) (g : Equiv.Perm.{succ u1} α) (h : Equiv.Perm.{succ u2} β), Eq.{succ (max u1 u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (instHMul.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (MulOneClass.toHasMul.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β))))))) (Equiv.Perm.sumCongr.{u1, u2} α β e f) (Equiv.Perm.sumCongr.{u1, u2} α β g h)) (Equiv.Perm.sumCongr.{u1, u2} α β (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e g) (HMul.hMul.{u2, u2, u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.{succ u2} β) (Equiv.Perm.{succ u2} β) (instHMul.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasMul.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))))) f h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.Perm.{succ u2} α) (f : Equiv.Perm.{succ u1} β) (g : Equiv.Perm.{succ u2} α) (h : Equiv.Perm.{succ u1} β), Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (instHMul.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (MulOneClass.toMul.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β))))))) (Equiv.Perm.sumCongr.{u2, u1} α β e f) (Equiv.Perm.sumCongr.{u2, u1} α β g h)) (Equiv.Perm.sumCongr.{u2, u1} α β (HMul.hMul.{u2, u2, u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u2} α) (instHMul.{u2} (Equiv.Perm.{succ u2} α) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} α) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))))) e g) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.{succ u1} β) (Equiv.Perm.{succ u1} β) (instHMul.{u1} (Equiv.Perm.{succ u1} β) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))))) f h))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_mul Equiv.Perm.sumCongr_mulₓ'. -/
@[simp]
theorem sumCongr_mul {α β : Type _} (e : Perm α) (f : Perm β) (g : Perm α) (h : Perm β) :
    sumCongr e f * sumCongr g h = sumCongr (e * g) (f * h) :=
  sumCongr_trans g h e f
#align equiv.perm.sum_congr_mul Equiv.Perm.sumCongr_mul

/- warning: equiv.perm.sum_congr_inv -> Equiv.Perm.sumCongr_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) (f : Equiv.Perm.{succ u2} β), Eq.{succ (max u1 u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Inv.inv.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toHasInv.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))) (Equiv.Perm.sumCongr.{u1, u2} α β e f)) (Equiv.Perm.sumCongr.{u1, u2} α β (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) e) (Inv.inv.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toHasInv.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.Perm.{succ u2} α) (f : Equiv.Perm.{succ u1} β), Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Inv.inv.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (InvOneClass.toInv.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvOneMonoid.toInvOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivisionMonoid.toDivInvOneMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivisionMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β)))))) (Equiv.Perm.sumCongr.{u2, u1} α β e f)) (Equiv.Perm.sumCongr.{u2, u1} α β (Inv.inv.{u2} (Equiv.Perm.{succ u2} α) (InvOneClass.toInv.{u2} (Equiv.Perm.{succ u2} α) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α))))) e) (Inv.inv.{u1} (Equiv.Perm.{succ u1} β) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} β) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) f))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_inv Equiv.Perm.sumCongr_invₓ'. -/
@[simp]
theorem sumCongr_inv {α β : Type _} (e : Perm α) (f : Perm β) :
    (sumCongr e f)⁻¹ = sumCongr e⁻¹ f⁻¹ :=
  sumCongr_symm e f
#align equiv.perm.sum_congr_inv Equiv.Perm.sumCongr_inv

/- warning: equiv.perm.sum_congr_one -> Equiv.Perm.sumCongr_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (OfNat.mk.{u2} (Equiv.Perm.{succ u2} β) 1 (One.one.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))))) (OfNat.ofNat.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) 1 (OfNat.mk.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) 1 (One.one.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (MulOneClass.toHasOne.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.sumCongr.{u2, u1} α β (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} α) 1 (One.toOfNat1.{u2} (Equiv.Perm.{succ u2} α) (InvOneClass.toOne.{u2} (Equiv.Perm.{succ u2} α) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} β) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} β) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} β) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))))))) (OfNat.ofNat.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) 1 (One.toOfNat1.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (InvOneClass.toOne.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvOneMonoid.toInvOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivisionMonoid.toDivInvOneMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivisionMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_one Equiv.Perm.sumCongr_oneₓ'. -/
@[simp]
theorem sumCongr_one {α β : Type _} : sumCongr (1 : Perm α) (1 : Perm β) = 1 :=
  sumCongr_refl
#align equiv.perm.sum_congr_one Equiv.Perm.sumCongr_one

/- warning: equiv.perm.sum_congr_hom -> Equiv.Perm.sumCongrHom is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}), MonoidHom.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Prod.mulOneClass.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}), MonoidHom.{max u2 u1, max u1 u2} (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) (Equiv.Perm.{max (succ u2) (succ u1)} (Sum.{u1, u2} α β)) (Prod.instMulOneClassProd.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u2) (succ u1)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u2) (succ u1)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u2) (succ u1)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_hom Equiv.Perm.sumCongrHomₓ'. -/
/-- `equiv.perm.sum_congr` as a `monoid_hom`, with its two arguments bundled into a single `prod`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
def sumCongrHom (α β : Type _) : Perm α × Perm β →* Perm (Sum α β)
    where
  toFun a := sumCongr a.1 a.2
  map_one' := sumCongr_one
  map_mul' a b := (sumCongr_mul _ _ _ _).symm
#align equiv.perm.sum_congr_hom Equiv.Perm.sumCongrHom

/- warning: equiv.perm.sum_congr_hom_injective -> Equiv.Perm.sumCongrHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Function.Injective.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (MonoidHom.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Prod.mulOneClass.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))))) (fun (_x : MonoidHom.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Prod.mulOneClass.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))))) => (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) -> (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β))) (MonoidHom.hasCoeToFun.{max u1 u2, max u1 u2} (Prod.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Prod.mulOneClass.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.permGroup.{max u1 u2} (Sum.{u1, u2} α β)))))) (Equiv.Perm.sumCongrHom.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{max u1 u2, max u2 u1} (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Prod.instMulOneClassProd.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β)))))) (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (fun (_x : Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) => Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) _x) (MulHomClass.toFunLike.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{max u1 u2, max u2 u1} (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Prod.instMulOneClassProd.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β)))))) (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (MulOneClass.toMul.{max u2 u1} (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Prod.instMulOneClassProd.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))))) (MulOneClass.toMul.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β)))))) (MonoidHomClass.toMulHomClass.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{max u1 u2, max u2 u1} (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Prod.instMulOneClassProd.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β)))))) (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Prod.instMulOneClassProd.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β))))) (MonoidHom.monoidHomClass.{max u2 u1, max u2 u1} (Prod.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Prod.instMulOneClassProd.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.permGroup.{max u2 u1} (Sum.{u2, u1} α β)))))))) (Equiv.Perm.sumCongrHom.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_hom_injective Equiv.Perm.sumCongrHom_injectiveₓ'. -/
theorem sumCongrHom_injective {α β : Type _} : Function.Injective (sumCongrHom α β) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iff]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)
#align equiv.perm.sum_congr_hom_injective Equiv.Perm.sumCongrHom_injective

/- warning: equiv.perm.sum_congr_swap_one -> Equiv.Perm.sumCongr_swap_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (i : α) (j : α), Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (OfNat.mk.{u2} (Equiv.Perm.{succ u2} β) 1 (One.one.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))))) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) β (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.inl.{u1, u2} α β i) (Sum.inl.{u1, u2} α β j))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] (i : α) (j : α), Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.sumCongr.{u2, u1} α β (Equiv.swap.{succ u2} α (fun (a : α) (b : α) => _inst_1 a b) i j) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} β) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} β) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} β) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))))))) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (fun (a : Sum.{u2, u1} α β) (b : Sum.{u2, u1} α β) => Sum.instDecidableEqSum.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.inl.{u2, u1} α β i) (Sum.inl.{u2, u1} α β j))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_swap_one Equiv.Perm.sumCongr_swap_oneₓ'. -/
@[simp]
theorem sumCongr_swap_one {α β : Type _} [DecidableEq α] [DecidableEq β] (i j : α) :
    sumCongr (Equiv.swap i j) (1 : Perm β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  sumCongr_swap_refl i j
#align equiv.perm.sum_congr_swap_one Equiv.Perm.sumCongr_swap_one

/- warning: equiv.perm.sum_congr_one_swap -> Equiv.Perm.sumCongr_one_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (i : β) (j : β), Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β)) (Equiv.Perm.sumCongr.{u1, u2} α β (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (Equiv.swap.{succ u2} β (fun (a : β) (b : β) => _inst_2 a b) i j)) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u1, u2} α β) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) β (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.inr.{u1, u2} α β i) (Sum.inr.{u1, u2} α β j))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] (i : β) (j : β), Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β)) (Equiv.Perm.sumCongr.{u2, u1} α β (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} α) 1 (One.toOfNat1.{u2} (Equiv.Perm.{succ u2} α) (InvOneClass.toOne.{u2} (Equiv.Perm.{succ u2} α) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α))))))) (Equiv.swap.{succ u1} β (fun (a : β) (b : β) => _inst_2 a b) i j)) (Equiv.swap.{max (succ u1) (succ u2)} (Sum.{u2, u1} α β) (fun (a : Sum.{u2, u1} α β) (b : Sum.{u2, u1} α β) => Sum.instDecidableEqSum.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (Sum.inr.{u2, u1} α β i) (Sum.inr.{u2, u1} α β j))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sum_congr_one_swap Equiv.Perm.sumCongr_one_swapₓ'. -/
@[simp]
theorem sumCongr_one_swap {α β : Type _} [DecidableEq α] [DecidableEq β] (i j : β) :
    sumCongr (1 : Perm α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  sumCongr_refl_swap i j
#align equiv.perm.sum_congr_one_swap Equiv.Perm.sumCongr_one_swap

/-! Lemmas about `equiv.perm.sigma_congr_right` re-expressed via the group structure. -/


/- warning: equiv.perm.sigma_congr_right_mul -> Equiv.Perm.sigmaCongrRight_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (F : forall (a : α), Equiv.Perm.{succ u2} (β a)) (G : forall (a : α), Equiv.Perm.{succ u2} (β a)), Eq.{succ (max u1 u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (instHMul.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (MulOneClass.toHasMul.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a)))))))) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) F) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) G)) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (forall (a : α), Equiv.Perm.{succ u2} (β a)) (forall (a : α), Equiv.Perm.{succ u2} (β a)) (instHMul.{max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (Pi.instMul.{u1, u2} α (fun (a : α) => Equiv.Perm.{succ u2} (β a)) (fun (i : α) => MulOneClass.toHasMul.{u2} (Equiv.Perm.{succ u2} (β i)) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} (β i)) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Equiv.Perm.permGroup.{u2} (β i)))))))) F G))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} (F : forall (a : α), Equiv.Perm.{succ u1} (β a)) (G : forall (a : α), Equiv.Perm.{succ u1} (β a)), Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (instHMul.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (MulOneClass.toMul.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)))))))) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) F) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) G)) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (forall (a : α), Equiv.Perm.{succ u1} (β a)) (forall (a : α), Equiv.Perm.{succ u1} (β a)) (instHMul.{max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Pi.instMul.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (β i)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))))) F G))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_mul Equiv.Perm.sigmaCongrRight_mulₓ'. -/
@[simp]
theorem sigmaCongrRight_mul {α : Type _} {β : α → Type _} (F : ∀ a, Perm (β a))
    (G : ∀ a, Perm (β a)) : sigmaCongrRight F * sigmaCongrRight G = sigmaCongrRight (F * G) :=
  sigmaCongrRight_trans G F
#align equiv.perm.sigma_congr_right_mul Equiv.Perm.sigmaCongrRight_mul

/- warning: equiv.perm.sigma_congr_right_inv -> Equiv.Perm.sigmaCongrRight_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} (F : forall (a : α), Equiv.Perm.{succ u2} (β a)), Eq.{succ (max u1 u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Inv.inv.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (DivInvMonoid.toHasInv.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) F)) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) (fun (a : α) => Inv.inv.{u2} (Equiv.Perm.{succ u2} (β a)) (DivInvMonoid.toHasInv.{u2} (Equiv.Perm.{succ u2} (β a)) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} (β a)) (Equiv.Perm.permGroup.{u2} (β a)))) (F a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} (F : forall (a : α), Equiv.Perm.{succ u1} (β a)), Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Inv.inv.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (InvOneClass.toInv.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvOneMonoid.toInvOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivisionMonoid.toDivInvOneMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivisionMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a))))))) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) F)) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) (fun (a : α) => Inv.inv.{u1} (Equiv.Perm.{succ u1} (β a)) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} (β a)) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} (β a)) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} (β a)) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.permGroup.{u1} (β a)))))) (F a)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_inv Equiv.Perm.sigmaCongrRight_invₓ'. -/
@[simp]
theorem sigmaCongrRight_inv {α : Type _} {β : α → Type _} (F : ∀ a, Perm (β a)) :
    (sigmaCongrRight F)⁻¹ = sigmaCongrRight fun a => (F a)⁻¹ :=
  sigmaCongrRight_symm F
#align equiv.perm.sigma_congr_right_inv Equiv.Perm.sigmaCongrRight_inv

/- warning: equiv.perm.sigma_congr_right_one -> Equiv.Perm.sigmaCongrRight_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}}, Eq.{max 1 (succ u1) (succ u2)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.sigmaCongrRight.{u1, u2} α (fun (a : α) => β a) (OfNat.ofNat.{max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) 1 (OfNat.mk.{max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) 1 (One.one.{max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (Pi.instOne.{u1, u2} α (fun (a : α) => Equiv.Perm.{succ u2} (β a)) (fun (i : α) => MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} (β i)) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} (β i)) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Equiv.Perm.permGroup.{u2} (β i))))))))))) (OfNat.ofNat.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) 1 (OfNat.mk.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) 1 (One.one.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (MulOneClass.toHasOne.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.sigmaCongrRight.{u2, u1} α (fun (a : α) => β a) (OfNat.ofNat.{max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) 1 (One.toOfNat1.{max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Pi.instOne.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))))))) (OfNat.ofNat.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) 1 (One.toOfNat1.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (InvOneClass.toOne.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvOneMonoid.toInvOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivisionMonoid.toDivInvOneMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivisionMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_one Equiv.Perm.sigmaCongrRight_oneₓ'. -/
@[simp]
theorem sigmaCongrRight_one {α : Type _} {β : α → Type _} :
    sigmaCongrRight (1 : ∀ a, Equiv.Perm <| β a) = 1 :=
  sigmaCongrRight_refl
#align equiv.perm.sigma_congr_right_one Equiv.Perm.sigmaCongrRight_one

#print Equiv.Perm.sigmaCongrRightHom /-
/-- `equiv.perm.sigma_congr_right` as a `monoid_hom`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
def sigmaCongrRightHom {α : Type _} (β : α → Type _) : (∀ a, Perm (β a)) →* Perm (Σa, β a)
    where
  toFun := sigmaCongrRight
  map_one' := sigmaCongrRight_one
  map_mul' a b := (sigmaCongrRight_mul _ _).symm
#align equiv.perm.sigma_congr_right_hom Equiv.Perm.sigmaCongrRightHom
-/

/- warning: equiv.perm.sigma_congr_right_hom_injective -> Equiv.Perm.sigmaCongrRightHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}}, Function.Injective.{max (succ u1) (succ u2), max 1 (succ u1) (succ u2)} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (MonoidHom.{max u1 u2, max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Pi.mulOneClass.{u1, u2} α (fun (a : α) => Equiv.Perm.{succ u2} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} (β i)) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Equiv.Perm.permGroup.{u2} (β i)))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))))) (fun (_x : MonoidHom.{max u1 u2, max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Pi.mulOneClass.{u1, u2} α (fun (a : α) => Equiv.Perm.{succ u2} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} (β i)) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Equiv.Perm.permGroup.{u2} (β i)))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))))) => (forall (a : α), Equiv.Perm.{succ u2} (β a)) -> (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a)))) (MonoidHom.hasCoeToFun.{max u1 u2, max u1 u2} (forall (a : α), Equiv.Perm.{succ u2} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Pi.mulOneClass.{u1, u2} α (fun (a : α) => Equiv.Perm.{succ u2} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} (β i)) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} (β i)) (Equiv.Perm.permGroup.{u2} (β i)))))) (Monoid.toMulOneClass.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u1 u2} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u1, u2} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u1 u2} (Sigma.{u1, u2} α (fun (a : α) => β a))))))) (Equiv.Perm.sigmaCongrRightHom.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}}, Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{max u2 u1, max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Pi.mulOneClass.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a))))))) (forall (a : α), Equiv.Perm.{succ u1} (β a)) (fun (_x : forall (a : α), Equiv.Perm.{succ u1} (β a)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : forall (a : α), Equiv.Perm.{succ u1} (β a)) => Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) _x) (MulHomClass.toFunLike.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{max u2 u1, max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Pi.mulOneClass.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a))))))) (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (MulOneClass.toMul.{max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Pi.mulOneClass.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (a : α) => Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β a)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β a)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.permGroup.{u1} (β a))))))) (MulOneClass.toMul.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a))))))) (MonoidHomClass.toMulHomClass.{max u2 u1, max u2 u1, max u2 u1} (MonoidHom.{max u2 u1, max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Pi.mulOneClass.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a))))))) (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Pi.mulOneClass.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a)))))) (MonoidHom.monoidHomClass.{max u2 u1, max u2 u1} (forall (a : α), Equiv.Perm.{succ u1} (β a)) (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Pi.mulOneClass.{u2, u1} α (fun (a : α) => Equiv.Perm.{succ u1} (β a)) (fun (i : α) => Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (β i)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (β i)) (Equiv.Perm.permGroup.{u1} (β i)))))) (Monoid.toMulOneClass.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (DivInvMonoid.toMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Group.toDivInvMonoid.{max u2 u1} (Equiv.Perm.{max (succ u1) (succ u2)} (Sigma.{u2, u1} α (fun (a : α) => β a))) (Equiv.Perm.permGroup.{max u2 u1} (Sigma.{u2, u1} α (fun (a : α) => β a))))))))) (Equiv.Perm.sigmaCongrRightHom.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align equiv.perm.sigma_congr_right_hom_injective Equiv.Perm.sigmaCongrRightHom_injectiveₓ'. -/
theorem sigmaCongrRightHom_injective {α : Type _} {β : α → Type _} :
    Function.Injective (sigmaCongrRightHom β) :=
  by
  intro x y h
  ext (a b)
  simpa using Equiv.congr_fun h ⟨a, b⟩
#align equiv.perm.sigma_congr_right_hom_injective Equiv.Perm.sigmaCongrRightHom_injective

/- warning: equiv.perm.subtype_congr_hom -> Equiv.Perm.subtypeCongrHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.mulOneClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.subtype_congr_hom Equiv.Perm.subtypeCongrHomₓ'. -/
/-- `equiv.perm.subtype_congr` as a `monoid_hom`. -/
@[simps]
def subtypeCongrHom (p : α → Prop) [DecidablePred p] :
    Perm { a // p a } × Perm { a // ¬p a } →* Perm α
    where
  toFun pair := Perm.subtypeCongr pair.fst pair.snd
  map_one' := Perm.subtypeCongr.refl
  map_mul' _ _ := (Perm.subtypeCongr.trans _ _ _ _).symm
#align equiv.perm.subtype_congr_hom Equiv.Perm.subtypeCongrHom

/- warning: equiv.perm.subtype_congr_hom_injective -> Equiv.Perm.subtypeCongrHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Function.Injective.{succ u1, succ u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.mulOneClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (fun (_x : MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.mulOneClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) => (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) -> (Equiv.Perm.{succ u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.mulOneClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.subtypeCongrHom.{u1} α p (fun (a : α) => _inst_1 a)))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Function.Injective.{succ u1, succ u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (fun (_x : Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) => Equiv.Perm.{succ u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))))))) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (MonoidHom.monoidHomClass.{u1, u1} (Prod.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a))))) (Equiv.Perm.{succ u1} α) (Prod.instMulOneClassProd.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => p a))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => p a)))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (a : α) => Not (p a)))))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) (Equiv.Perm.subtypeCongrHom.{u1} α p (fun (a : α) => _inst_1 a)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.subtype_congr_hom_injective Equiv.Perm.subtypeCongrHom_injectiveₓ'. -/
theorem subtypeCongrHom_injective (p : α → Prop) [DecidablePred p] :
    Function.Injective (subtypeCongrHom p) :=
  by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk.inj_iff]
  constructor <;> ext i <;> simpa using Equiv.congr_fun h i
#align equiv.perm.subtype_congr_hom_injective Equiv.Perm.subtypeCongrHom_injective

#print Equiv.Perm.permCongr_eq_mul /-
/-- If `e` is also a permutation, we can write `perm_congr`
completely in terms of the group structure. -/
@[simp]
theorem permCongr_eq_mul (e p : Perm α) : e.permCongr p = e * p * e⁻¹ :=
  rfl
#align equiv.perm.perm_congr_eq_mul Equiv.Perm.permCongr_eq_mul
-/

section ExtendDomain

/-! Lemmas about `equiv.perm.extend_domain` re-expressed via the group structure. -/


variable (e : Perm α) {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)

/- warning: equiv.perm.extend_domain_one -> Equiv.Perm.extendDomain_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.extendDomain.{u1, u2} α β (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) p (fun (a : β) => _inst_1 a) f) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (OfNat.mk.{u2} (Equiv.Perm.{succ u2} β) 1 (One.one.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.extendDomain.{u1, u2} α β (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) p (fun (a : β) => _inst_1 a) f) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (One.toOfNat1.{u2} (Equiv.Perm.{succ u2} β) (InvOneClass.toOne.{u2} (Equiv.Perm.{succ u2} β) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.extend_domain_one Equiv.Perm.extendDomain_oneₓ'. -/
@[simp]
theorem extendDomain_one : extendDomain 1 f = 1 :=
  extendDomain_refl f
#align equiv.perm.extend_domain_one Equiv.Perm.extendDomain_one

/- warning: equiv.perm.extend_domain_inv -> Equiv.Perm.extendDomain_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (Inv.inv.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toHasInv.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))) (Equiv.Perm.extendDomain.{u1, u2} α β e p (fun (a : β) => _inst_1 a) f)) (Equiv.Perm.extendDomain.{u1, u2} α β (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) e) p (fun (a : β) => _inst_1 a) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (Inv.inv.{u2} (Equiv.Perm.{succ u2} β) (InvOneClass.toInv.{u2} (Equiv.Perm.{succ u2} β) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.extendDomain.{u1, u2} α β e p (fun (a : β) => _inst_1 a) f)) (Equiv.Perm.extendDomain.{u1, u2} α β (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) e) p (fun (a : β) => _inst_1 a) f)
Case conversion may be inaccurate. Consider using '#align equiv.perm.extend_domain_inv Equiv.Perm.extendDomain_invₓ'. -/
@[simp]
theorem extendDomain_inv : (e.extendDomain f)⁻¹ = e⁻¹.extendDomain f :=
  rfl
#align equiv.perm.extend_domain_inv Equiv.Perm.extendDomain_inv

/- warning: equiv.perm.extend_domain_mul -> Equiv.Perm.extendDomain_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)) (e : Equiv.Perm.{succ u1} α) (e' : Equiv.Perm.{succ u1} α), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (HMul.hMul.{u2, u2, u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.{succ u2} β) (Equiv.Perm.{succ u2} β) (instHMul.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasMul.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))))) (Equiv.Perm.extendDomain.{u1, u2} α β e p (fun (a : β) => _inst_1 a) f) (Equiv.Perm.extendDomain.{u1, u2} α β e' p (fun (a : β) => _inst_1 a) f)) (Equiv.Perm.extendDomain.{u1, u2} α β (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e e') p (fun (a : β) => _inst_1 a) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)) (e : Equiv.Perm.{succ u1} α) (e' : Equiv.Perm.{succ u1} α), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (HMul.hMul.{u2, u2, u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.{succ u2} β) (Equiv.Perm.{succ u2} β) (instHMul.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))))) (Equiv.Perm.extendDomain.{u1, u2} α β e p (fun (a : β) => _inst_1 a) f) (Equiv.Perm.extendDomain.{u1, u2} α β e' p (fun (a : β) => _inst_1 a) f)) (Equiv.Perm.extendDomain.{u1, u2} α β (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) e e') p (fun (a : β) => _inst_1 a) f)
Case conversion may be inaccurate. Consider using '#align equiv.perm.extend_domain_mul Equiv.Perm.extendDomain_mulₓ'. -/
@[simp]
theorem extendDomain_mul (e e' : Perm α) :
    e.extendDomain f * e'.extendDomain f = (e * e').extendDomain f :=
  extendDomain_trans _ _ _
#align equiv.perm.extend_domain_mul Equiv.Perm.extendDomain_mul

#print Equiv.Perm.extendDomainHom /-
/-- `extend_domain` as a group homomorphism -/
@[simps]
def extendDomainHom : Perm α →* Perm β
    where
  toFun e := extendDomain e f
  map_one' := extendDomain_one f
  map_mul' e e' := (extendDomain_mul f e e').symm
#align equiv.perm.extend_domain_hom Equiv.Perm.extendDomainHom
-/

/- warning: equiv.perm.extend_domain_hom_injective -> Equiv.Perm.extendDomainHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)), Function.Injective.{succ u1, succ u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (fun (_x : MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) => (Equiv.Perm.{succ u1} α) -> (Equiv.Perm.{succ u2} β)) (MonoidHom.hasCoeToFun.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.extendDomainHom.{u1, u2} α β p (fun (a : β) => _inst_1 a) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] (f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)), Function.Injective.{succ u1, succ u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.Perm.{succ u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Equiv.Perm.{succ u1} α) => Equiv.Perm.{succ u2} β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))) (MonoidHom.monoidHomClass.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))) (Equiv.Perm.extendDomainHom.{u1, u2} α β p (fun (a : β) => _inst_1 a) f))
Case conversion may be inaccurate. Consider using '#align equiv.perm.extend_domain_hom_injective Equiv.Perm.extendDomainHom_injectiveₓ'. -/
theorem extendDomainHom_injective : Function.Injective (extendDomainHom f) :=
  (injective_iff_map_eq_one (extendDomainHom f)).mpr fun e he =>
    ext fun x =>
      f.injective (Subtype.ext ((extendDomain_apply_image e f x).symm.trans (ext_iff.mp he (f x))))
#align equiv.perm.extend_domain_hom_injective Equiv.Perm.extendDomainHom_injective

/- warning: equiv.perm.extend_domain_eq_one_iff -> Equiv.Perm.extendDomain_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] {e : Equiv.Perm.{succ u1} α} {f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)}, Iff (Eq.{succ u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.extendDomain.{u1, u2} α β e p (fun (a : β) => _inst_1 a) f) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (OfNat.mk.{u2} (Equiv.Perm.{succ u2} β) 1 (One.one.{u2} (Equiv.Perm.{succ u2} β) (MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) e (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {p : β -> Prop} [_inst_1 : DecidablePred.{succ u2} β p] {e : Equiv.Perm.{succ u1} α} {f : Equiv.{succ u1, succ u2} α (Subtype.{succ u2} β p)}, Iff (Eq.{succ u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.extendDomain.{u1, u2} α β e p (fun (a : β) => _inst_1 a) f) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} β) 1 (One.toOfNat1.{u2} (Equiv.Perm.{succ u2} β) (InvOneClass.toOne.{u2} (Equiv.Perm.{succ u2} β) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))))))) (Eq.{succ u1} (Equiv.Perm.{succ u1} α) e (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.extend_domain_eq_one_iff Equiv.Perm.extendDomain_eq_one_iffₓ'. -/
@[simp]
theorem extendDomain_eq_one_iff {e : Perm α} {f : α ≃ Subtype p} : e.extendDomain f = 1 ↔ e = 1 :=
  (injective_iff_map_eq_one' (extendDomainHom f)).mp (extendDomainHom_injective f) e
#align equiv.perm.extend_domain_eq_one_iff Equiv.Perm.extendDomain_eq_one_iff

@[simp]
theorem extendDomain_pow (n : ℕ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_pow (extendDomainHom f) _ _
#align equiv.perm.extend_domain_pow Equiv.Perm.extendDomain_pow

@[simp]
theorem extendDomain_zpow (n : ℤ) : (e ^ n).extendDomain f = e.extendDomain f ^ n :=
  map_zpow (extendDomainHom f) _ _
#align equiv.perm.extend_domain_zpow Equiv.Perm.extendDomain_zpow

end ExtendDomain

section Subtype

variable {p : α → Prop} {f : Perm α}

#print Equiv.Perm.subtypePerm /-
/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtypePerm (f : Perm α) (h : ∀ x, p x ↔ p (f x)) : Perm { x // p x } :=
  ⟨fun x => ⟨f x, (h _).1 x.2⟩, fun x => ⟨f⁻¹ x, (h (f⁻¹ x)).2 <| by simpa using x.2⟩, fun _ => by
    simp only [Perm.inv_apply_self, Subtype.coe_eta, Subtype.coe_mk], fun _ => by
    simp only [Perm.apply_inv_self, Subtype.coe_eta, Subtype.coe_mk]⟩
#align equiv.perm.subtype_perm Equiv.Perm.subtypePerm
-/

#print Equiv.Perm.subtypePerm_apply /-
@[simp]
theorem subtypePerm_apply (f : Perm α) (h : ∀ x, p x ↔ p (f x)) (x : { x // p x }) :
    subtypePerm f h x = ⟨f x, (h _).1 x.2⟩ :=
  rfl
#align equiv.perm.subtype_perm_apply Equiv.Perm.subtypePerm_apply
-/

/- warning: equiv.perm.subtype_perm_one -> Equiv.Perm.subtypePerm_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (h : optParam.{0} (forall (_x : α), Iff (p _x) (p _x)) (fun (_x : α) => Iff.rfl (p _x))), Eq.{succ u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Equiv.Perm.subtypePerm.{u1} α p (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) h) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) 1 (One.one.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (x : α) => p x))))))))))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) (h : optParam.{0} (forall (_x : α), Iff (p _x) (p _x)) (fun (_x : α) => Iff.rfl (p _x))), Eq.{succ u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Equiv.Perm.subtypePerm.{u1} α p (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) h) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α (fun (x : α) => p x)))))))))
Case conversion may be inaccurate. Consider using '#align equiv.perm.subtype_perm_one Equiv.Perm.subtypePerm_oneₓ'. -/
@[simp]
theorem subtypePerm_one (p : α → Prop) (h := fun _ => Iff.rfl) : @subtypePerm α p 1 h = 1 :=
  Equiv.ext fun ⟨_, _⟩ => rfl
#align equiv.perm.subtype_perm_one Equiv.Perm.subtypePerm_one

#print Equiv.Perm.subtypePerm_mul /-
@[simp]
theorem subtypePerm_mul (f g : Perm α) (hf hg) :
    (f.subtypePerm hf * g.subtypePerm hg : Perm { x // p x }) =
      (f * g).subtypePerm fun x => (hg _).trans <| hf _ :=
  rfl
#align equiv.perm.subtype_perm_mul Equiv.Perm.subtypePerm_mul
-/

private theorem inv_aux : (∀ x, p x ↔ p (f x)) ↔ ∀ x, p x ↔ p (f⁻¹ x) :=
  f⁻¹.surjective.forall.trans <| by simp_rw [f.apply_inv_self, Iff.comm]
#align equiv.perm.inv_aux equiv.perm.inv_aux

#print Equiv.Perm.subtypePerm_inv /-
/-- See `equiv.perm.inv_subtype_perm`-/
theorem subtypePerm_inv (f : Perm α) (hf) :
    f⁻¹.subtypePerm hf = (f.subtypePerm <| inv_aux.2 hf : Perm { x // p x })⁻¹ :=
  rfl
#align equiv.perm.subtype_perm_inv Equiv.Perm.subtypePerm_inv
-/

#print Equiv.Perm.inv_subtypePerm /-
/-- See `equiv.perm.subtype_perm_inv`-/
@[simp]
theorem inv_subtypePerm (f : Perm α) (hf) :
    (f.subtypePerm hf : Perm { x // p x })⁻¹ = f⁻¹.subtypePerm (inv_aux.1 hf) :=
  rfl
#align equiv.perm.inv_subtype_perm Equiv.Perm.inv_subtypePerm
-/

private theorem pow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℕ} (x), p x ↔ p ((f ^ n) x)
  | 0, x => Iff.rfl
  | n + 1, x => (pow_aux _).trans (hf _)
#align equiv.perm.pow_aux equiv.perm.pow_aux

#print Equiv.Perm.subtypePerm_pow /-
@[simp]
theorem subtypePerm_pow (f : Perm α) (n : ℕ) (hf) :
    (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf) :=
  by
  induction' n with n ih
  · simp
  · simp_rw [pow_succ', ih, subtypePerm_mul]
#align equiv.perm.subtype_perm_pow Equiv.Perm.subtypePerm_pow
-/

private theorem zpow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℤ} (x), p x ↔ p ((f ^ n) x)
  | int.of_nat n => pow_aux hf
  | int.neg_succ_of_nat n => by
    rw [zpow_negSucc]
    exact inv_aux.1 (pow_aux hf)
#align equiv.perm.zpow_aux equiv.perm.zpow_aux

#print Equiv.Perm.subtypePerm_zpow /-
@[simp]
theorem subtypePerm_zpow (f : Perm α) (n : ℤ) (hf) :
    (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux hf) :=
  by
  induction' n with n ih
  · exact subtypePerm_pow _ _ _
  · simp only [zpow_negSucc, subtypePerm_pow, subtypePerm_inv]
#align equiv.perm.subtype_perm_zpow Equiv.Perm.subtypePerm_zpow
-/

variable [DecidablePred p] {a : α}

#print Equiv.Perm.ofSubtype /-
/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def ofSubtype : Perm (Subtype p) →* Perm α
    where
  toFun f := extendDomain f (Equiv.refl (Subtype p))
  map_one' := Equiv.Perm.extendDomain_one _
  map_mul' f g := (Equiv.Perm.extendDomain_mul _ f g).symm
#align equiv.perm.of_subtype Equiv.Perm.ofSubtype
-/

#print Equiv.Perm.ofSubtype_subtypePerm /-
theorem ofSubtype_subtypePerm {f : Perm α} (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) :
    ofSubtype (subtypePerm f h₁) = f :=
  Equiv.ext fun x => by
    by_cases hx : p x
    · exact (subtypePerm f h₁).extendDomain_apply_subtype _ hx
    · rw [ofSubtype, MonoidHom.coe_mk, Equiv.Perm.extendDomain_apply_not_subtype]
      · exact not_not.mp fun h => hx (h₂ x (Ne.symm h))
      · exact hx
#align equiv.perm.of_subtype_subtype_perm Equiv.Perm.ofSubtype_subtypePerm
-/

#print Equiv.Perm.ofSubtype_apply_of_mem /-
theorem ofSubtype_apply_of_mem (f : Perm (Subtype p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩ :=
  extendDomain_apply_subtype _ _ _
#align equiv.perm.of_subtype_apply_of_mem Equiv.Perm.ofSubtype_apply_of_mem
-/

#print Equiv.Perm.ofSubtype_apply_coe /-
@[simp]
theorem ofSubtype_apply_coe (f : Perm (Subtype p)) (x : Subtype p) : ofSubtype f x = f x :=
  Subtype.casesOn x fun _ => ofSubtype_apply_of_mem f
#align equiv.perm.of_subtype_apply_coe Equiv.Perm.ofSubtype_apply_coe
-/

#print Equiv.Perm.ofSubtype_apply_of_not_mem /-
theorem ofSubtype_apply_of_not_mem (f : Perm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a :=
  extendDomain_apply_not_subtype _ _ ha
#align equiv.perm.of_subtype_apply_of_not_mem Equiv.Perm.ofSubtype_apply_of_not_mem
-/

#print Equiv.Perm.mem_iff_ofSubtype_apply_mem /-
theorem mem_iff_ofSubtype_apply_mem (f : Perm (Subtype p)) (x : α) :
    p x ↔ p ((ofSubtype f : α → α) x) :=
  if h : p x then by
    simpa only [h, true_iff_iff, MonoidHom.coe_mk, ofSubtype_apply_of_mem f h] using (f ⟨x, h⟩).2
  else by simp [h, ofSubtype_apply_of_not_mem f h]
#align equiv.perm.mem_iff_of_subtype_apply_mem Equiv.Perm.mem_iff_ofSubtype_apply_mem
-/

/- warning: equiv.perm.subtype_perm_of_subtype -> Equiv.Perm.subtypePerm_ofSubtype is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (f : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)), Eq.{succ u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Equiv.Perm.subtypePerm.{u1} α (fun (x : α) => p x) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (fun (_x : MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) => (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) -> (Equiv.Perm.{succ u1} α)) (MonoidHom.hasCoeToFun.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.ofSubtype.{u1} α p (fun (a : α) => _inst_1 a)) f) (Equiv.Perm.mem_iff_ofSubtype_apply_mem.{u1} α p (fun (a : α) => _inst_1 a) f)) f
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] (f : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)), Eq.{succ u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α (fun (x : α) => p x))) (Equiv.Perm.subtypePerm.{u1} α (fun (x : α) => p x) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (fun (_x : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) => Equiv.Perm.{succ u1} α) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p)))))) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (MonoidHom.monoidHomClass.{u1, u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} (Subtype.{succ u1} α p)) (Equiv.Perm.permGroup.{u1} (Subtype.{succ u1} α p))))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))) (Equiv.Perm.ofSubtype.{u1} α p (fun (a : α) => _inst_1 a)) f) (Equiv.Perm.mem_iff_ofSubtype_apply_mem.{u1} α p (fun (a : α) => _inst_1 a) f)) f
Case conversion may be inaccurate. Consider using '#align equiv.perm.subtype_perm_of_subtype Equiv.Perm.subtypePerm_ofSubtypeₓ'. -/
@[simp]
theorem subtypePerm_ofSubtype (f : Perm (Subtype p)) :
    subtypePerm (ofSubtype f) (mem_iff_ofSubtype_apply_mem f) = f :=
  Equiv.ext fun x => Subtype.coe_injective (ofSubtype_apply_coe f x)
#align equiv.perm.subtype_perm_of_subtype Equiv.Perm.subtypePerm_ofSubtype

#print Equiv.Perm.subtypeEquivSubtypePerm /-
/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps]
protected def subtypeEquivSubtypePerm (p : α → Prop) [DecidablePred p] :
    Perm (Subtype p) ≃ { f : Perm α // ∀ a, ¬p a → f a = a }
    where
  toFun f := ⟨f.ofSubtype, fun a => f.ofSubtype_apply_of_not_mem⟩
  invFun f :=
    (f : Perm α).subtypePerm fun a =>
      ⟨Decidable.not_imp_not.1 fun hfa => f.val.injective (f.prop _ hfa) ▸ hfa,
        Decidable.not_imp_not.1 fun ha hfa => ha <| f.prop a ha ▸ hfa⟩
  left_inv := Equiv.Perm.subtypePerm_ofSubtype
  right_inv f :=
    Subtype.ext (Equiv.Perm.ofSubtype_subtypePerm _ fun a => Not.decidable_imp_symm <| f.prop a)
#align equiv.perm.subtype_equiv_subtype_perm Equiv.Perm.subtypeEquivSubtypePerm
-/

#print Equiv.Perm.subtypeEquivSubtypePerm_apply_of_mem /-
theorem subtypeEquivSubtypePerm_apply_of_mem (f : Perm (Subtype p)) (h : p a) :
    Perm.subtypeEquivSubtypePerm p f a = f ⟨a, h⟩ :=
  f.ofSubtype_apply_of_mem h
#align equiv.perm.subtype_equiv_subtype_perm_apply_of_mem Equiv.Perm.subtypeEquivSubtypePerm_apply_of_mem
-/

#print Equiv.Perm.subtypeEquivSubtypePerm_apply_of_not_mem /-
theorem subtypeEquivSubtypePerm_apply_of_not_mem (f : Perm (Subtype p)) (h : ¬p a) :
    Perm.subtypeEquivSubtypePerm p f a = a :=
  f.ofSubtype_apply_of_not_mem h
#align equiv.perm.subtype_equiv_subtype_perm_apply_of_not_mem Equiv.Perm.subtypeEquivSubtypePerm_apply_of_not_mem
-/

end Subtype

end Perm

section Swap

variable [DecidableEq α]

/- warning: equiv.swap_inv -> Equiv.swap_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α) (y : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (x : α) (y : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)
Case conversion may be inaccurate. Consider using '#align equiv.swap_inv Equiv.swap_invₓ'. -/
@[simp]
theorem swap_inv (x y : α) : (swap x y)⁻¹ = swap x y :=
  rfl
#align equiv.swap_inv Equiv.swap_inv

/- warning: equiv.swap_mul_self -> Equiv.swap_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.swap_mul_self Equiv.swap_mul_selfₓ'. -/
@[simp]
theorem swap_mul_self (i j : α) : swap i j * swap i j = 1 :=
  swap_swap i j
#align equiv.swap_mul_self Equiv.swap_mul_self

/- warning: equiv.swap_mul_eq_mul_swap -> Equiv.swap_mul_eq_mul_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Equiv.Perm.{succ u1} α) (x : α) (y : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) f) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) f) x) (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) f) y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Equiv.Perm.{succ u1} α) (x : α) (y : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y) f) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f (Equiv.swap.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x) (fun (a : α) (b : α) => _inst_1 a b) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f) x) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f) y)))
Case conversion may be inaccurate. Consider using '#align equiv.swap_mul_eq_mul_swap Equiv.swap_mul_eq_mul_swapₓ'. -/
theorem swap_mul_eq_mul_swap (f : Perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
  Equiv.ext fun z => by
    simp only [Perm.mul_apply, swap_apply_def]
    split_ifs <;>
      simp_all only [Perm.apply_inv_self, Perm.eq_inv_iff_eq, eq_self_iff_true, not_true]
#align equiv.swap_mul_eq_mul_swap Equiv.swap_mul_eq_mul_swap

/- warning: equiv.mul_swap_eq_swap_mul -> Equiv.mul_swap_eq_swap_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Equiv.Perm.{succ u1} α) (x : α) (y : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f x) (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f y)) f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (f : Equiv.Perm.{succ u1} α) (x : α) (y : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) f (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (instHMul.{u1} (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x)) (Equiv.Perm.permGroup.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x))))))) (Equiv.swap.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) x) (fun (a : α) (b : α) => _inst_1 a b) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f x) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f y)) f)
Case conversion may be inaccurate. Consider using '#align equiv.mul_swap_eq_swap_mul Equiv.mul_swap_eq_swap_mulₓ'. -/
theorem mul_swap_eq_swap_mul (f : Perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f := by
  rw [swap_mul_eq_mul_swap, Perm.inv_apply_self, Perm.inv_apply_self]
#align equiv.mul_swap_eq_swap_mul Equiv.mul_swap_eq_swap_mul

#print Equiv.swap_apply_apply /-
theorem swap_apply_apply (f : Perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ := by
  rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]
#align equiv.swap_apply_apply Equiv.swap_apply_apply
-/

/- warning: equiv.swap_mul_self_mul -> Equiv.swap_mul_self_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α) (σ : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) σ)) σ
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α) (σ : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) σ)) σ
Case conversion may be inaccurate. Consider using '#align equiv.swap_mul_self_mul Equiv.swap_mul_self_mulₓ'. -/
/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem swap_mul_self_mul (i j : α) (σ : Perm α) : Equiv.swap i j * (Equiv.swap i j * σ) = σ := by
  rw [← mul_assoc, swap_mul_self, one_mul]
#align equiv.swap_mul_self_mul Equiv.swap_mul_self_mul

/- warning: equiv.mul_swap_mul_self -> Equiv.mul_swap_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α) (σ : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) σ (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) σ
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α) (σ : Equiv.Perm.{succ u1} α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) σ (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) σ
Case conversion may be inaccurate. Consider using '#align equiv.mul_swap_mul_self Equiv.mul_swap_mul_selfₓ'. -/
/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
theorem mul_swap_mul_self (i j : α) (σ : Perm α) : σ * Equiv.swap i j * Equiv.swap i j = σ := by
  rw [mul_assoc, swap_mul_self, mul_one]
#align equiv.mul_swap_mul_self Equiv.mul_swap_mul_self

/- warning: equiv.swap_mul_involutive -> Equiv.swap_mul_involutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α), Function.Involutive.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α), Function.Involutive.{succ u1} (Equiv.Perm.{succ u1} α) ((fun (x._@.Mathlib.GroupTheory.Perm.Basic._hyg.3840 : Equiv.Perm.{succ u1} α) (x._@.Mathlib.GroupTheory.Perm.Basic._hyg.3842 : Equiv.Perm.{succ u1} α) => HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) x._@.Mathlib.GroupTheory.Perm.Basic._hyg.3840 x._@.Mathlib.GroupTheory.Perm.Basic._hyg.3842) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j))
Case conversion may be inaccurate. Consider using '#align equiv.swap_mul_involutive Equiv.swap_mul_involutiveₓ'. -/
/-- A stronger version of `mul_right_injective` -/
@[simp]
theorem swap_mul_involutive (i j : α) : Function.Involutive ((· * ·) (Equiv.swap i j)) :=
  swap_mul_self_mul i j
#align equiv.swap_mul_involutive Equiv.swap_mul_involutive

/- warning: equiv.mul_swap_involutive -> Equiv.mul_swap_involutive is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α), Function.Involutive.{succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.Perm.{succ u1} α) => HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) _x (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (i : α) (j : α), Function.Involutive.{succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.Perm.{succ u1} α) => HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) _x (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j))
Case conversion may be inaccurate. Consider using '#align equiv.mul_swap_involutive Equiv.mul_swap_involutiveₓ'. -/
/-- A stronger version of `mul_left_injective` -/
@[simp]
theorem mul_swap_involutive (i j : α) : Function.Involutive (· * Equiv.swap i j) :=
  mul_swap_mul_self i j
#align equiv.mul_swap_involutive Equiv.mul_swap_involutive

/- warning: equiv.swap_eq_one_iff -> Equiv.swap_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {i : α} {j : α}, Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))) (Eq.{succ u1} α i j)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {i : α} {j : α}, Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))) (Eq.{succ u1} α i j)
Case conversion may be inaccurate. Consider using '#align equiv.swap_eq_one_iff Equiv.swap_eq_one_iffₓ'. -/
@[simp]
theorem swap_eq_one_iff {i j : α} : swap i j = (1 : Perm α) ↔ i = j :=
  swap_eq_refl_iff
#align equiv.swap_eq_one_iff Equiv.swap_eq_one_iff

/- warning: equiv.swap_mul_eq_iff -> Equiv.swap_mul_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {i : α} {j : α} {σ : Equiv.Perm.{succ u1} α}, Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) σ) σ) (Eq.{succ u1} α i j)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {i : α} {j : α} {σ : Equiv.Perm.{succ u1} α}, Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j) σ) σ) (Eq.{succ u1} α i j)
Case conversion may be inaccurate. Consider using '#align equiv.swap_mul_eq_iff Equiv.swap_mul_eq_iffₓ'. -/
theorem swap_mul_eq_iff {i j : α} {σ : Perm α} : swap i j * σ = σ ↔ i = j :=
  ⟨fun h => by
    have swap_id : swap i j = 1 := mul_right_cancel (trans h (one_mul σ).symm)
    rw [← swap_apply_right i j, swap_id]
    rfl, fun h => by erw [h, swap_self, one_mul]⟩
#align equiv.swap_mul_eq_iff Equiv.swap_mul_eq_iff

/- warning: equiv.mul_swap_eq_iff -> Equiv.mul_swap_eq_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {i : α} {j : α} {σ : Equiv.Perm.{succ u1} α}, Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) σ (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) σ) (Eq.{succ u1} α i j)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {i : α} {j : α} {σ : Equiv.Perm.{succ u1} α}, Iff (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) σ (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) i j)) σ) (Eq.{succ u1} α i j)
Case conversion may be inaccurate. Consider using '#align equiv.mul_swap_eq_iff Equiv.mul_swap_eq_iffₓ'. -/
theorem mul_swap_eq_iff {i j : α} {σ : Perm α} : σ * swap i j = σ ↔ i = j :=
  ⟨fun h => by
    have swap_id : swap i j = 1 := mul_left_cancel (trans h (one_mul σ).symm)
    rw [← swap_apply_right i j, swap_id]
    rfl, fun h => by erw [h, swap_self, mul_one]⟩
#align equiv.mul_swap_eq_iff Equiv.mul_swap_eq_iff

/- warning: equiv.swap_mul_swap_mul_swap -> Equiv.swap_mul_swap_mul_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : α} {y : α} {z : α}, (Ne.{succ u1} α x y) -> (Ne.{succ u1} α x z) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) y z) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) y z)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) z x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {x : α} {y : α} {z : α}, (Ne.{succ u1} α x y) -> (Ne.{succ u1} α x z) -> (Eq.{succ u1} (Equiv.Perm.{succ u1} α) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) y z) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) x y)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) y z)) (Equiv.swap.{succ u1} α (fun (a : α) (b : α) => _inst_1 a b) z x))
Case conversion may be inaccurate. Consider using '#align equiv.swap_mul_swap_mul_swap Equiv.swap_mul_swap_mul_swapₓ'. -/
theorem swap_mul_swap_mul_swap {x y z : α} (hwz : x ≠ y) (hxz : x ≠ z) :
    swap y z * swap x y * swap y z = swap z x :=
  Equiv.ext fun n => by
    simp only [swap_apply_def, Perm.mul_apply]
    split_ifs <;> cc
#align equiv.swap_mul_swap_mul_swap Equiv.swap_mul_swap_mul_swap

end Swap

section AddGroup

variable [AddGroup α] (a b : α)

/- warning: equiv.add_left_zero -> Equiv.addLeft_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addLeft.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addLeft.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.add_left_zero Equiv.addLeft_zeroₓ'. -/
@[simp]
theorem addLeft_zero : Equiv.addLeft (0 : α) = 1 :=
  ext zero_add
#align equiv.add_left_zero Equiv.addLeft_zero

/- warning: equiv.add_right_zero -> Equiv.addRight_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addRight.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addRight.{u1} α _inst_1 (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.add_right_zero Equiv.addRight_zeroₓ'. -/
@[simp]
theorem addRight_zero : Equiv.addRight (0 : α) = 1 :=
  ext add_zero
#align equiv.add_right_zero Equiv.addRight_zero

/- warning: equiv.add_left_add -> Equiv.addLeft_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addLeft.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.addLeft.{u1} α _inst_1 a) (Equiv.addLeft.{u1} α _inst_1 b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addLeft.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.addLeft.{u1} α _inst_1 a) (Equiv.addLeft.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align equiv.add_left_add Equiv.addLeft_addₓ'. -/
@[simp]
theorem addLeft_add : Equiv.addLeft (a + b) = Equiv.addLeft a * Equiv.addLeft b :=
  ext <| add_assoc _ _
#align equiv.add_left_add Equiv.addLeft_add

/- warning: equiv.add_right_add -> Equiv.addRight_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addRight.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toHasAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.addRight.{u1} α _inst_1 b) (Equiv.addRight.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.addRight.{u1} α _inst_1 (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (AddZeroClass.toAdd.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.addRight.{u1} α _inst_1 b) (Equiv.addRight.{u1} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align equiv.add_right_add Equiv.addRight_addₓ'. -/
@[simp]
theorem addRight_add : Equiv.addRight (a + b) = Equiv.addRight b * Equiv.addRight a :=
  ext fun _ => (add_assoc _ _ _).symm
#align equiv.add_right_add Equiv.addRight_add

/- warning: equiv.inv_add_left -> Equiv.inv_addLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) (Equiv.addLeft.{u1} α _inst_1 a)) (Equiv.addLeft.{u1} α _inst_1 (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.addLeft.{u1} α _inst_1 a)) (Equiv.addLeft.{u1} α _inst_1 (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.inv_add_left Equiv.inv_addLeftₓ'. -/
@[simp]
theorem inv_addLeft : (Equiv.addLeft a)⁻¹ = Equiv.addLeft (-a) :=
  Equiv.coe_inj.1 rfl
#align equiv.inv_add_left Equiv.inv_addLeft

/- warning: equiv.inv_add_right -> Equiv.inv_addRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) (Equiv.addRight.{u1} α _inst_1 a)) (Equiv.addRight.{u1} α _inst_1 (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : AddGroup.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.addRight.{u1} α _inst_1 a)) (Equiv.addRight.{u1} α _inst_1 (Neg.neg.{u1} α (NegZeroClass.toNeg.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (AddGroup.toSubtractionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.inv_add_right Equiv.inv_addRightₓ'. -/
@[simp]
theorem inv_addRight : (Equiv.addRight a)⁻¹ = Equiv.addRight (-a) :=
  Equiv.coe_inj.1 rfl
#align equiv.inv_add_right Equiv.inv_addRight

#print Equiv.pow_addLeft /-
@[simp]
theorem pow_addLeft (n : ℕ) : Equiv.addLeft a ^ n = Equiv.addLeft (n • a) :=
  by
  ext
  simp [Perm.coe_pow]
#align equiv.pow_add_left Equiv.pow_addLeft
-/

#print Equiv.pow_addRight /-
@[simp]
theorem pow_addRight (n : ℕ) : Equiv.addRight a ^ n = Equiv.addRight (n • a) :=
  by
  ext
  simp [Perm.coe_pow]
#align equiv.pow_add_right Equiv.pow_addRight
-/

#print Equiv.zpow_addLeft /-
@[simp]
theorem zpow_addLeft (n : ℤ) : Equiv.addLeft a ^ n = Equiv.addLeft (n • a) :=
  (map_zsmul (⟨Equiv.addLeft, addLeft_zero, addLeft_add⟩ : α →+ Additive (Perm α)) _ _).symm
#align equiv.zpow_add_left Equiv.zpow_addLeft
-/

#print Equiv.zpow_addRight /-
@[simp]
theorem zpow_addRight (n : ℤ) : Equiv.addRight a ^ n = Equiv.addRight (n • a) :=
  @zpow_addLeft αᵃᵒᵖ _ _ _
#align equiv.zpow_add_right Equiv.zpow_addRight
-/

end AddGroup

section Group

variable [Group α] (a b : α)

/- warning: equiv.mul_left_one -> Equiv.mulLeft_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulLeft.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulLeft.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.mul_left_one Equiv.mulLeft_oneₓ'. -/
@[simp, to_additive]
theorem mulLeft_one : Equiv.mulLeft (1 : α) = 1 :=
  ext one_mul
#align equiv.mul_left_one Equiv.mulLeft_one
#align equiv.add_left_zero Equiv.addLeft_zero

/- warning: equiv.mul_right_one -> Equiv.mulRight_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulRight.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (OfNat.mk.{u1} (Equiv.Perm.{succ u1} α) 1 (One.one.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasOne.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α], Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulRight.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} (Equiv.Perm.{succ u1} α) 1 (One.toOfNat1.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toOne.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))))
Case conversion may be inaccurate. Consider using '#align equiv.mul_right_one Equiv.mulRight_oneₓ'. -/
@[simp, to_additive]
theorem mulRight_one : Equiv.mulRight (1 : α) = 1 :=
  ext mul_one
#align equiv.mul_right_one Equiv.mulRight_one
#align equiv.add_right_zero Equiv.addRight_zero

/- warning: equiv.mul_left_mul -> Equiv.mulLeft_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulLeft.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.mulLeft.{u1} α _inst_1 a) (Equiv.mulLeft.{u1} α _inst_1 b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulLeft.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.mulLeft.{u1} α _inst_1 a) (Equiv.mulLeft.{u1} α _inst_1 b))
Case conversion may be inaccurate. Consider using '#align equiv.mul_left_mul Equiv.mulLeft_mulₓ'. -/
@[simp, to_additive]
theorem mulLeft_mul : Equiv.mulLeft (a * b) = Equiv.mulLeft a * Equiv.mulLeft b :=
  ext <| mul_assoc _ _
#align equiv.mul_left_mul Equiv.mulLeft_mul
#align equiv.add_left_add Equiv.addLeft_add

/- warning: equiv.mul_right_mul -> Equiv.mulRight_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulRight.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toHasMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.mulRight.{u1} α _inst_1 b) (Equiv.mulRight.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α) (b : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Equiv.mulRight.{u1} α _inst_1 (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a b)) (HMul.hMul.{u1, u1, u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u1} α) (instHMul.{u1} (Equiv.Perm.{succ u1} α) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))))) (Equiv.mulRight.{u1} α _inst_1 b) (Equiv.mulRight.{u1} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align equiv.mul_right_mul Equiv.mulRight_mulₓ'. -/
@[simp, to_additive]
theorem mulRight_mul : Equiv.mulRight (a * b) = Equiv.mulRight b * Equiv.mulRight a :=
  ext fun _ => (mul_assoc _ _ _).symm
#align equiv.mul_right_mul Equiv.mulRight_mul
#align equiv.add_right_add Equiv.addRight_add

/- warning: equiv.inv_mul_left -> Equiv.inv_mulLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) (Equiv.mulLeft.{u1} α _inst_1 a)) (Equiv.mulLeft.{u1} α _inst_1 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.mulLeft.{u1} α _inst_1 a)) (Equiv.mulLeft.{u1} α _inst_1 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.inv_mul_left Equiv.inv_mulLeftₓ'. -/
@[simp, to_additive inv_add_left]
theorem inv_mulLeft : (Equiv.mulLeft a)⁻¹ = Equiv.mulLeft a⁻¹ :=
  Equiv.coe_inj.1 rfl
#align equiv.inv_mul_left Equiv.inv_mulLeft
#align equiv.inv_add_left Equiv.inv_addLeft

/- warning: equiv.inv_mul_right -> Equiv.inv_mulRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) (Equiv.mulRight.{u1} α _inst_1 a)) (Equiv.mulRight.{u1} α _inst_1 (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] (a : α), Eq.{succ u1} (Equiv.Perm.{succ u1} α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (Equiv.mulRight.{u1} α _inst_1 a)) (Equiv.mulRight.{u1} α _inst_1 (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.inv_mul_right Equiv.inv_mulRightₓ'. -/
@[simp, to_additive inv_add_right]
theorem inv_mulRight : (Equiv.mulRight a)⁻¹ = Equiv.mulRight a⁻¹ :=
  Equiv.coe_inj.1 rfl
#align equiv.inv_mul_right Equiv.inv_mulRight
#align equiv.inv_add_right Equiv.inv_addRight

#print Equiv.pow_mulLeft /-
@[simp, to_additive pow_add_left]
theorem pow_mulLeft (n : ℕ) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) :=
  by
  ext
  simp [Perm.coe_pow]
#align equiv.pow_mul_left Equiv.pow_mulLeft
#align equiv.pow_add_left Equiv.pow_addLeft
-/

#print Equiv.pow_mulRight /-
@[simp, to_additive pow_add_right]
theorem pow_mulRight (n : ℕ) : Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n) :=
  by
  ext
  simp [Perm.coe_pow]
#align equiv.pow_mul_right Equiv.pow_mulRight
#align equiv.pow_add_right Equiv.pow_addRight
-/

#print Equiv.zpow_mulLeft /-
@[simp, to_additive zpow_add_left]
theorem zpow_mulLeft (n : ℤ) : Equiv.mulLeft a ^ n = Equiv.mulLeft (a ^ n) :=
  (map_zpow (⟨Equiv.mulLeft, mulLeft_one, mulLeft_mul⟩ : α →* Perm α) _ _).symm
#align equiv.zpow_mul_left Equiv.zpow_mulLeft
#align equiv.zpow_add_left Equiv.zpow_addLeft
-/

#print Equiv.zpow_mulRight /-
@[simp, to_additive zpow_add_right]
theorem zpow_mulRight : ∀ n : ℤ, Equiv.mulRight a ^ n = Equiv.mulRight (a ^ n)
  | int.of_nat n => by simp
  | int.neg_succ_of_nat n => by simp
#align equiv.zpow_mul_right Equiv.zpow_mulRight
#align equiv.zpow_add_right Equiv.zpow_addRight
-/

end Group

end Equiv

open Equiv Function

namespace Set

variable {α : Type _} {f : Perm α} {s t : Set α}

@[simp]
theorem bijOn_perm_inv : BijOn (⇑f⁻¹) t s ↔ BijOn f s t :=
  Equiv.bijOn_symm
#align set.bij_on_perm_inv Set.bijOn_perm_inv

/- warning: set.bij_on.perm_inv -> Set.BijOn.perm_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.BijOn.{u1, u1} α α (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) f) s t) -> (Set.BijOn.{u1, u1} α α (coeFn.{succ u1, succ u1} (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.{succ u1, succ u1} α α) => α -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toHasInv.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))) f)) t s)
but is expected to have type
  forall {α : Type.{u1}} {f : Equiv.Perm.{succ u1} α} {s : Set.{u1} α}, (Set.BijOn.{u1, u1} α α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (a : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) a) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) f) s s) -> (Set.BijOn.{u1, u1} α α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} α) α (fun (a : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => α) a) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α α) (Inv.inv.{u1} (Equiv.Perm.{succ u1} α) (InvOneClass.toInv.{u1} (Equiv.Perm.{succ u1} α) (DivInvOneMonoid.toInvOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivisionMonoid.toDivInvOneMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivisionMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) f)) s s)
Case conversion may be inaccurate. Consider using '#align set.bij_on.perm_inv Set.BijOn.perm_invₓ'. -/
alias bij_on_perm_inv ↔ bij_on.of_perm_inv bij_on.perm_inv
#align set.bij_on.of_perm_inv Set.BijOn.of_perm_inv
#align set.bij_on.perm_inv Set.BijOn.perm_inv

#print Set.MapsTo.perm_pow /-
theorem MapsTo.perm_pow : MapsTo f s s → ∀ n : ℕ, MapsTo (⇑(f ^ n)) s s :=
  by
  simp_rw [Equiv.Perm.coe_pow]
  exact MapsTo.iterate
#align set.maps_to.perm_pow Set.MapsTo.perm_pow
-/

#print Set.SurjOn.perm_pow /-
theorem SurjOn.perm_pow : SurjOn f s s → ∀ n : ℕ, SurjOn (⇑(f ^ n)) s s :=
  by
  simp_rw [Equiv.Perm.coe_pow]
  exact SurjOn.iterate
#align set.surj_on.perm_pow Set.SurjOn.perm_pow
-/

#print Set.BijOn.perm_pow /-
theorem BijOn.perm_pow : BijOn f s s → ∀ n : ℕ, BijOn (⇑(f ^ n)) s s :=
  by
  simp_rw [Equiv.Perm.coe_pow]
  exact BijOn.iterate
#align set.bij_on.perm_pow Set.BijOn.perm_pow
-/

#print Set.BijOn.perm_zpow /-
theorem BijOn.perm_zpow (hf : BijOn f s s) : ∀ n : ℤ, BijOn (⇑(f ^ n)) s s
  | int.of_nat n => hf.perm_pow _
  | int.neg_succ_of_nat n => by
    rw [zpow_negSucc]
    exact (hf.perm_pow _).perm_inv
#align set.bij_on.perm_zpow Set.BijOn.perm_zpow
-/

end Set

