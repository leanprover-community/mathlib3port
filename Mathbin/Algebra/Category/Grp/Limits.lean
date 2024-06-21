/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Algebra.Category.MonCat.Limits
import Algebra.Category.Grp.Preadditive
import CategoryTheory.Comma.Over
import Algebra.Group.Subgroup.Basic
import CategoryTheory.ConcreteCategory.Elementwise

#align_import algebra.category.Group.limits from "leanprover-community/mathlib"@"4280f5f32e16755ec7985ce11e189b6cd6ff6735"

/-!
# The category of (commutative) (additive) groups has all limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/


open CategoryTheory

open CategoryTheory.Limits

universe v u

noncomputable section

variable {J : Type v} [SmallCategory J]

namespace Grp

#print Grp.groupObj /-
@[to_additive]
instance groupObj (F : J ⥤ Grp.{max v u}) (j) : Group ((F ⋙ forget Grp).obj j) := by
  change Group (F.obj j); infer_instance
#align Group.group_obj Grp.groupObj
#align AddGroup.add_group_obj AddGrp.addGroupObj
-/

#print Grp.sectionsSubgroup /-
/-- The flat sections of a functor into `Group` form a subgroup of all sections.
-/
@[to_additive
      "The flat sections of a functor into `AddGroup` form an additive subgroup of all sections."]
def sectionsSubgroup (F : J ⥤ Grp) : Subgroup (∀ j, F.obj j) :=
  {
    MonCat.sectionsSubmonoid
      (F ⋙ forget₂ Grp MonCat) with
    carrier := (F ⋙ forget Grp).sections
    inv_mem' := fun a ah j j' f =>
      by
      simp only [forget_map_eq_coe, functor.comp_map, Pi.inv_apply, MonoidHom.map_inv, inv_inj]
      dsimp [functor.sections] at ah
      rw [ah f] }
#align Group.sections_subgroup Grp.sectionsSubgroup
#align AddGroup.sections_add_subgroup AddGrp.sectionsAddSubgroup
-/

#print Grp.limitGroup /-
@[to_additive]
instance limitGroup (F : J ⥤ Grp.{max v u}) : Group (Types.limitCone (F ⋙ forget Grp)).pt :=
  by
  change Group (sections_subgroup F)
  infer_instance
#align Group.limit_group Grp.limitGroup
#align AddGroup.limit_add_group AddGrp.limitAddGroup
-/

#print Grp.Forget₂.createsLimit /-
/-- We show that the forgetful functor `Group ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `group` instance available, and then reuse
the existing limit. -/
@[to_additive
      "We show that the forgetful functor `AddGroup ⥤ AddMon` creates limits.\n\nAll we need to do is notice that the limit point has an `add_group` instance available, and then\nreuse the existing limit."]
instance Forget₂.createsLimit (F : J ⥤ Grp.{max v u}) :
    CreatesLimit F (forget₂ Grp.{max v u} MonCat.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := Grp.of (Types.limitCone (F ⋙ forget Grp)).pt
          π :=
            { app := MonCat.limitπMonoidHom (F ⋙ forget₂ Grp MonCat.{max v u})
              naturality' :=
                (MonCat.HasLimits.limitCone (F ⋙ forget₂ Grp MonCat.{max v u})).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (MonCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ Grp MonCat.{max v u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }
#align Group.forget₂.creates_limit Grp.Forget₂.createsLimit
#align AddGroup.forget₂.creates_limit AddGrp.Forget₂.createsLimit
-/

#print Grp.limitCone /-
/-- A choice of limit cone for a functor into `Group`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
      "A choice of limit cone for a functor into `Group`.\n(Generally, you'll just want to use `limit F`.)"]
def limitCone (F : J ⥤ Grp.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ Grp MonCat.{max v u}))
#align Group.limit_cone Grp.limitCone
#align AddGroup.limit_cone AddGrp.limitCone
-/

#print Grp.limitConeIsLimit /-
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone.\n(Generally, you'll just want to use `limit.cone F`.)"]
def limitConeIsLimit (F : J ⥤ Grp.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align Group.limit_cone_is_limit Grp.limitConeIsLimit
#align AddGroup.limit_cone_is_limit AddGrp.limitConeIsLimit
-/

#print Grp.hasLimitsOfSize /-
/-- The category of groups has all limits. -/
@[to_additive "The category of additive groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} Grp.{max v u}
    where HasLimitsOfShape J 𝒥 :=
    { HasLimit := fun F => has_limit_of_created F (forget₂ Grp MonCat.{max v u}) }
#align Group.has_limits_of_size Grp.hasLimitsOfSize
#align AddGroup.has_limits_of_size AddGrp.hasLimitsOfSize
-/

#print Grp.hasLimits /-
@[to_additive]
instance hasLimits : HasLimits Grp.{u} :=
  Grp.hasLimitsOfSize.{u, u}
#align Group.has_limits Grp.hasLimits
#align AddGroup.has_limits AddGrp.hasLimits
-/

#print Grp.forget₂MonPreservesLimitsOfSize /-
/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive AddGrp.forget₂AddMonPreservesLimitsOfSize
      "The forgetful functor from additive groups\nto additive monoids preserves all limits.\n\nThis means the underlying additive monoid of a limit can be computed as a limit in the category of\nadditive monoids."]
instance forget₂MonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ Grp MonCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align Group.forget₂_Mon_preserves_limits_of_size Grp.forget₂MonPreservesLimitsOfSize
#align AddGroup.forget₂_AddMon_preserves_limits AddGrp.forget₂AddMonPreservesLimitsOfSize
-/

#print Grp.forget₂MonPreservesLimits /-
@[to_additive]
instance forget₂MonPreservesLimits : PreservesLimits (forget₂ Grp MonCat.{u}) :=
  Grp.forget₂MonPreservesLimitsOfSize.{u, u}
#align Group.forget₂_Mon_preserves_limits Grp.forget₂MonPreservesLimits
#align AddGroup.forget₂_Mon_preserves_limits AddGrp.forget₂MonPreservesLimits
-/

#print Grp.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
      "The forgetful functor from additive groups to types preserves all limits.\n\nThis means the underlying type of a limit can be computed as a limit in the category of types."]
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget Grp.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ Grp MonCat) (forget MonCat) }
#align Group.forget_preserves_limits_of_size Grp.forgetPreservesLimitsOfSize
#align AddGroup.forget_preserves_limits_of_size AddGrp.forgetPreservesLimitsOfSize
-/

#print Grp.forgetPreservesLimits /-
@[to_additive]
instance forgetPreservesLimits : PreservesLimits (forget Grp.{u}) :=
  Grp.forgetPreservesLimitsOfSize.{u, u}
#align Group.forget_preserves_limits Grp.forgetPreservesLimits
#align AddGroup.forget_preserves_limits AddGrp.forgetPreservesLimits
-/

end Grp

namespace CommGrp

#print CommGrp.commGroupObj /-
@[to_additive]
instance commGroupObj (F : J ⥤ CommGrp.{max v u}) (j) : CommGroup ((F ⋙ forget CommGrp).obj j) := by
  change CommGroup (F.obj j); infer_instance
#align CommGroup.comm_group_obj CommGrp.commGroupObj
#align AddCommGroup.add_comm_group_obj AddCommGrp.addCommGroupObj
-/

#print CommGrp.limitCommGroup /-
@[to_additive]
instance limitCommGroup (F : J ⥤ CommGrp.{max v u}) :
    CommGroup (Types.limitCone (F ⋙ forget CommGrp.{max v u})).pt :=
  @Subgroup.toCommGroup (∀ j, F.obj j) _ (Grp.sectionsSubgroup (F ⋙ forget₂ CommGrp Grp.{max v u}))
#align CommGroup.limit_comm_group CommGrp.limitCommGroup
#align AddCommGroup.limit_add_comm_group AddCommGrp.limitAddCommGroup
-/

#print CommGrp.Forget₂.createsLimit /-
/-- We show that the forgetful functor `CommGroup ⥤ Group` creates limits.

All we need to do is notice that the limit point has a `comm_group` instance available,
and then reuse the existing limit.
-/
@[to_additive
      "We show that the forgetful functor `AddCommGroup ⥤ AddGroup` creates limits.\n\nAll we need to do is notice that the limit point has an `add_comm_group` instance available, and\nthen reuse the existing limit."]
instance Forget₂.createsLimit (F : J ⥤ CommGrp.{max v u}) :
    CreatesLimit F (forget₂ CommGrp Grp.{max v u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommGrp.of (Types.limitCone (F ⋙ forget CommGrp)).pt
          π :=
            { app :=
                MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGrp Grp.{max v u} ⋙ forget₂ Grp MonCat.{max v u})
              naturality' := (MonCat.HasLimits.limitCone _).π.naturality } }
      validLift := by apply is_limit.unique_up_to_iso (Grp.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ Grp.{max v u} ⋙ forget₂ _ MonCat.{max v u})
          (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }
#align CommGroup.forget₂.creates_limit CommGrp.Forget₂.createsLimit
#align AddCommGroup.forget₂.creates_limit AddCommGrp.Forget₂.createsLimit
-/

#print CommGrp.limitCone /-
/-- A choice of limit cone for a functor into `CommGroup`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive
      "A choice of limit cone for a functor into `CommGroup`.\n(Generally, you'll just want to use `limit F`.)"]
def limitCone (F : J ⥤ CommGrp.{max v u}) : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrp Grp.{max v u}))
#align CommGroup.limit_cone CommGrp.limitCone
#align AddCommGroup.limit_cone AddCommGrp.limitCone
-/

#print CommGrp.limitConeIsLimit /-
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
      "The chosen cone is a limit cone.\n(Generally, you'll just wantto use `limit.cone F`.)"]
def limitConeIsLimit (F : J ⥤ CommGrp.{max v u}) : IsLimit (limitCone F) :=
  liftedLimitIsLimit _
#align CommGroup.limit_cone_is_limit CommGrp.limitConeIsLimit
#align AddCommGroup.limit_cone_is_limit AddCommGrp.limitConeIsLimit
-/

#print CommGrp.hasLimitsOfSize /-
/-- The category of commutative groups has all limits. -/
@[to_additive "The category of additive commutative groups has all limits."]
instance hasLimitsOfSize : HasLimitsOfSize.{v, v} CommGrp.{max v u}
    where HasLimitsOfShape J 𝒥 :=
    { HasLimit := fun F => has_limit_of_created F (forget₂ CommGrp Grp.{max v u}) }
#align CommGroup.has_limits_of_size CommGrp.hasLimitsOfSize
#align AddCommGroup.has_limits_of_size AddCommGrp.hasLimitsOfSize
-/

#print CommGrp.hasLimits /-
@[to_additive]
instance hasLimits : HasLimits CommGrp.{u} :=
  CommGrp.hasLimitsOfSize.{u, u}
#align CommGroup.has_limits CommGrp.hasLimits
#align AddCommGroup.has_limits AddCommGrp.hasLimits
-/

#print CommGrp.forget₂GroupPreservesLimitsOfSize /-
/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive AddCommGrp.forget₂AddGroupPreservesLimitsOfSize
      "The forgetful functor from additive commutative groups to groups preserves all limits.\n(That is, the underlying group could have been computed instead as limits in the category\nof additive groups.)"]
instance forget₂GroupPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGrp Grp.{max v u})
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }
#align CommGroup.forget₂_Group_preserves_limits_of_size CommGrp.forget₂GroupPreservesLimitsOfSize
#align AddCommGroup.forget₂_AddGroup_preserves_limits AddCommGrp.forget₂AddGroupPreservesLimitsOfSize
-/

#print CommGrp.forget₂GroupPreservesLimits /-
@[to_additive]
instance forget₂GroupPreservesLimits : PreservesLimits (forget₂ CommGrp Grp.{u}) :=
  CommGrp.forget₂GroupPreservesLimitsOfSize.{u, u}
#align CommGroup.forget₂_Group_preserves_limits CommGrp.forget₂GroupPreservesLimits
#align AddCommGroup.forget₂_Group_preserves_limits AddCommGrp.forget₂AddGroupPreservesLimits
-/

#print CommGrp.forget₂CommMonPreservesLimitsAux /-
/-- An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGrp.forget₂AddCommMonPreservesLimitsAux
      "An auxiliary declaration to speed up typechecking."]
def forget₂CommMonPreservesLimitsAux (F : J ⥤ CommGrp.{max v u}) :
    IsLimit ((forget₂ CommGrp CommMonCat).mapCone (limitCone F)) :=
  CommMonCat.limitConeIsLimit (F ⋙ forget₂ CommGrp CommMonCat)
#align CommGroup.forget₂_CommMon_preserves_limits_aux CommGrp.forget₂CommMonPreservesLimitsAux
#align AddCommGroup.forget₂_AddCommMon_preserves_limits_aux AddCommGrp.forget₂AddCommMonPreservesLimitsAux
-/

#print CommGrp.forget₂CommMonPreservesLimitsOfSize /-
/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGrp.forget₂AddCommMonPreservesLimitsOfSize
      "The forgetful functor from additive commutative groups to additive commutative monoids preserves\nall limits. (That is, the underlying additive commutative monoids could have been computed instead\nas limits in the category of additive commutative monoids.)"]
instance forget₂CommMonPreservesLimitsOfSize :
    PreservesLimitsOfSize.{v, v} (forget₂ CommGrp CommMonCat.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    {
      PreservesLimit := fun F =>
        preserves_limit_of_preserves_limit_cone (limit_cone_is_limit F)
          (forget₂_CommMon_preserves_limits_aux F) }
#align CommGroup.forget₂_CommMon_preserves_limits_of_size CommGrp.forget₂CommMonPreservesLimitsOfSize
#align AddCommGroup.forget₂_AddCommMon_preserves_limits AddCommGrp.forget₂AddCommMonPreservesLimitsOfSize
-/

#print CommGrp.forgetPreservesLimitsOfSize /-
/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive AddCommGrp.forgetPreservesLimitsOfSize
      "The forgetful functor from additive commutative groups to types preserves all limits. (That is,\nthe underlying types could have been computed instead as limits in the category of types.)"]
instance forgetPreservesLimitsOfSize : PreservesLimitsOfSize.{v, v} (forget CommGrp.{max v u})
    where PreservesLimitsOfShape J 𝒥 :=
    { PreservesLimit := fun F => limits.comp_preserves_limit (forget₂ CommGrp Grp) (forget Grp) }
#align CommGroup.forget_preserves_limits_of_size CommGrp.forgetPreservesLimitsOfSize
#align AddCommGroup.forget_preserves_limits AddCommGrp.forgetPreservesLimitsOfSize
-/

-- Verify we can form limits indexed over smaller categories.
example (f : ℕ → AddCommGrp) : HasProduct f := by infer_instance

end CommGrp

namespace AddCommGrp

#print AddCommGrp.kernelIsoKer /-
/-- The categorical kernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical kernel.
-/
def kernelIsoKer {G H : AddCommGrp.{u}} (f : G ⟶ H) : kernel f ≅ AddCommGrp.of f.ker
    where
  Hom :=
    { toFun := fun g =>
        ⟨kernel.ι f g,
          by
          -- TODO where is this `has_coe_t_aux.coe` coming from? can we prevent it appearing?
          change (kernel.ι f) g ∈ f.ker
          simp [AddMonoidHom.mem_ker]⟩
      map_zero' := by ext; simp
      map_add' := fun g g' => by ext; simp }
  inv := kernel.lift f (AddSubgroup.subtype f.ker) (by tidy)
  hom_inv_id' := by apply equalizer.hom_ext _; ext; simp
  inv_hom_id' := by
    apply AddCommGrp.ext
    simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
    rintro ⟨x, mem⟩
    simp
#align AddCommGroup.kernel_iso_ker AddCommGrp.kernelIsoKer
-/

#print AddCommGrp.kernelIsoKer_hom_comp_subtype /-
@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGrp} (f : G ⟶ H) :
    (kernelIsoKer f).Hom ≫ AddSubgroup.subtype f.ker = kernel.ι f := by ext <;> rfl
#align AddCommGroup.kernel_iso_ker_hom_comp_subtype AddCommGrp.kernelIsoKer_hom_comp_subtype
-/

#print AddCommGrp.kernelIsoKer_inv_comp_ι /-
@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGrp} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = AddSubgroup.subtype f.ker :=
  by
  ext
  simp [kernel_iso_ker]
#align AddCommGroup.kernel_iso_ker_inv_comp_ι AddCommGrp.kernelIsoKer_inv_comp_ι
-/

#print AddCommGrp.kernelIsoKerOver /-
/-- The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps]
def kernelIsoKerOver {G H : AddCommGrp.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGrp.of f.ker) (AddSubgroup.subtype f.ker) :=
  Over.isoMk (kernelIsoKer f) (by simp)
#align AddCommGroup.kernel_iso_ker_over AddCommGrp.kernelIsoKerOver
-/

end AddCommGrp

