/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Group.Z_Module_equivalence
! leanprover-community/mathlib commit bf1b813e20e108e8868341ca94bb3404a2506ae5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.Basic

/-!
The forgetful functor from ℤ-modules to additive commutative groups is
an equivalence of categories.

TODO:
either use this equivalence to transport the monoidal structure from `Module ℤ` to `Ab`,
or, having constructed that monoidal structure directly, show this functor is monoidal.
-/


open CategoryTheory

open CategoryTheory.Equivalence

universe u

namespace ModuleCat

/- warning: Module.forget₂_AddCommGroup_full -> ModuleCat.forget₂AddCommGroupFull is a dubious translation:
lean 3 declaration is
  CategoryTheory.Full.{u1, u1, succ u1, succ u1} (ModuleCat.{u1, 0} Int Int.ring) (ModuleCat.moduleCategory.{u1, 0} Int Int.ring) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} (ModuleCat.{u1, 0} Int Int.ring) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.ring) (ModuleCat.moduleConcreteCategory.{u1, 0} Int Int.ring) AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1} (ModuleCat.hasForgetToAddCommGroup.{0, u1} Int Int.ring))
but is expected to have type
  CategoryTheory.Full.{u1, u1, succ u1, succ u1} (ModuleCat.{u1, 0} Int Int.instRingInt) (ModuleCat.moduleCategory.{u1, 0} Int Int.instRingInt) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} (ModuleCat.{u1, 0} Int Int.instRingInt) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.instRingInt) (ModuleCat.moduleConcreteCategory.{u1, 0} Int Int.instRingInt) AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1} (ModuleCat.hasForgetToAddCommGroup.{0, u1} Int Int.instRingInt))
Case conversion may be inaccurate. Consider using '#align Module.forget₂_AddCommGroup_full ModuleCat.forget₂AddCommGroupFullₓ'. -/
/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is full. -/
instance forget₂AddCommGroupFull : Full (forget₂ (ModuleCat ℤ) AddCommGroupCat.{u})
    where preimage A B
    f :=-- `add_monoid_hom.to_int_linear_map` doesn't work here because `A` and `B` are not definitionally
    -- equal to the canonical `add_comm_group.int_module` module instances it expects.
    { toFun := f
      map_add' := AddMonoidHom.map_add f
      map_smul' := fun n x => by
        rw [int_smul_eq_zsmul, int_smul_eq_zsmul, map_zsmul, RingHom.id_apply] }
#align Module.forget₂_AddCommGroup_full ModuleCat.forget₂AddCommGroupFull

/- warning: Module.forget₂_AddCommGroup_ess_surj -> ModuleCat.forget₂_addCommGroupCat_essSurj is a dubious translation:
lean 3 declaration is
  CategoryTheory.EssSurj.{u1, u1, succ u1, succ u1} (ModuleCat.{u1, 0} Int Int.ring) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.ring) AddCommGroupCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} (ModuleCat.{u1, 0} Int Int.ring) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.ring) (ModuleCat.moduleConcreteCategory.{u1, 0} Int Int.ring) AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1} (ModuleCat.hasForgetToAddCommGroup.{0, u1} Int Int.ring))
but is expected to have type
  CategoryTheory.EssSurj.{u1, u1, succ u1, succ u1} (ModuleCat.{u1, 0} Int Int.instRingInt) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.instRingInt) AddCommGroupCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} (ModuleCat.{u1, 0} Int Int.instRingInt) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.instRingInt) (ModuleCat.moduleConcreteCategory.{u1, 0} Int Int.instRingInt) AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1} (ModuleCat.hasForgetToAddCommGroup.{0, u1} Int Int.instRingInt))
Case conversion may be inaccurate. Consider using '#align Module.forget₂_AddCommGroup_ess_surj ModuleCat.forget₂_addCommGroupCat_essSurjₓ'. -/
/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is essentially surjective. -/
instance forget₂_addCommGroupCat_essSurj : EssSurj (forget₂ (ModuleCat ℤ) AddCommGroupCat.{u})
    where mem_essImage A :=
    ⟨ModuleCat.of ℤ A,
      ⟨{  Hom := 𝟙 A
          inv := 𝟙 A }⟩⟩
#align Module.forget₂_AddCommGroup_ess_surj ModuleCat.forget₂_addCommGroupCat_essSurj

/- warning: Module.forget₂_AddCommGroup_is_equivalence -> ModuleCat.forget₂AddCommGroupIsEquivalence is a dubious translation:
lean 3 declaration is
  CategoryTheory.IsEquivalence.{u1, u1, succ u1, succ u1} (ModuleCat.{u1, 0} Int Int.ring) (ModuleCat.moduleCategory.{u1, 0} Int Int.ring) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} (ModuleCat.{u1, 0} Int Int.ring) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.ring) (ModuleCat.moduleConcreteCategory.{u1, 0} Int Int.ring) AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1} (ModuleCat.hasForgetToAddCommGroup.{0, u1} Int Int.ring))
but is expected to have type
  CategoryTheory.IsEquivalence.{u1, u1, succ u1, succ u1} (ModuleCat.{u1, 0} Int Int.instRingInt) (ModuleCat.moduleCategory.{u1, 0} Int Int.instRingInt) AddCommGroupCat.{u1} AddCommGroupCat.largeCategory.{u1} (CategoryTheory.forget₂.{succ u1, succ u1, u1, u1, u1} (ModuleCat.{u1, 0} Int Int.instRingInt) AddCommGroupCat.{u1} (ModuleCat.moduleCategory.{u1, 0} Int Int.instRingInt) (ModuleCat.moduleConcreteCategory.{u1, 0} Int Int.instRingInt) AddCommGroupCat.largeCategory.{u1} AddCommGroupCat.concreteCategory.{u1} (ModuleCat.hasForgetToAddCommGroup.{0, u1} Int Int.instRingInt))
Case conversion may be inaccurate. Consider using '#align Module.forget₂_AddCommGroup_is_equivalence ModuleCat.forget₂AddCommGroupIsEquivalenceₓ'. -/
noncomputable instance forget₂AddCommGroupIsEquivalence :
    IsEquivalence (forget₂ (ModuleCat ℤ) AddCommGroupCat.{u}) :=
  Equivalence.ofFullyFaithfullyEssSurj (forget₂ (ModuleCat ℤ) AddCommGroupCat)
#align Module.forget₂_AddCommGroup_is_equivalence ModuleCat.forget₂AddCommGroupIsEquivalence

end ModuleCat

