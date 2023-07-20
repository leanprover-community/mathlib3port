/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Algebra.Category.Module.Basic

#align_import algebra.category.Group.Z_Module_equivalence from "leanprover-community/mathlib"@"ef55335933293309ff8c0b1d20ffffeecbe5c39f"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print ModuleCat.forget₂AddCommGroupFull /-
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
-/

#print ModuleCat.forget₂_addCommGroupCat_essSurj /-
/-- The forgetful functor from `ℤ` modules to `AddCommGroup` is essentially surjective. -/
instance forget₂_addCommGroupCat_essSurj : EssSurj (forget₂ (ModuleCat ℤ) AddCommGroupCat.{u})
    where mem_essImage A :=
    ⟨ModuleCat.of ℤ A,
      ⟨{  Hom := 𝟙 A
          inv := 𝟙 A }⟩⟩
#align Module.forget₂_AddCommGroup_ess_surj ModuleCat.forget₂_addCommGroupCat_essSurj
-/

#print ModuleCat.forget₂AddCommGroupIsEquivalence /-
noncomputable instance forget₂AddCommGroupIsEquivalence :
    IsEquivalence (forget₂ (ModuleCat ℤ) AddCommGroupCat.{u}) :=
  Equivalence.ofFullyFaithfullyEssSurj (forget₂ (ModuleCat ℤ) AddCommGroupCat)
#align Module.forget₂_AddCommGroup_is_equivalence ModuleCat.forget₂AddCommGroupIsEquivalence
-/

end ModuleCat

