import Mathbin.Algebra.Category.Mon.Limits
import Mathbin.Algebra.Category.Group.Preadditive
import Mathbin.CategoryTheory.Over
import Mathbin.CategoryTheory.Limits.ConcreteCategory
import Mathbin.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

variable {J : Type u} [small_category J]

namespace Groupₓₓ

@[to_additive]
instance group_obj (F : J ⥤ Groupₓₓ) j : Groupₓ ((F ⋙ forget Groupₓₓ).obj j) := by
  change Groupₓ (F.obj j)
  infer_instance

/-- 
The flat sections of a functor into `Group` form a subgroup of all sections.
-/
@[to_additive "The flat sections of a functor into `AddGroup` form an additive subgroup of all sections."]
def sections_subgroup (F : J ⥤ Groupₓₓ) : Subgroup (∀ j, F.obj j) :=
  { Mon.sectionsSubmonoid (F ⋙ forget₂ Groupₓₓ Mon) with Carrier := (F ⋙ forget Groupₓₓ).sections,
    inv_mem' := fun a ah j j' f => by
      simp only [forget_map_eq_coe, functor.comp_map, Pi.inv_apply, MonoidHom.map_inv, inv_inj]
      dsimp [functor.sections]  at ah
      rw [ah f] }

@[to_additive]
instance limit_group (F : J ⥤ Groupₓₓ) : Groupₓ (types.limit_cone (F ⋙ forget Groupₓₓ.{u})).x := by
  change Groupₓ (sections_subgroup F)
  infer_instance

/-- 
We show that the forgetful functor `Group ⥤ Mon` creates limits.

All we need to do is notice that the limit point has a `group` instance available,
and then reuse the existing limit.
-/
@[to_additive]
instance (F : J ⥤ Groupₓₓ) : creates_limit F (forget₂ Groupₓₓ Mon.{u}) :=
  creates_limit_of_reflects_iso fun c' t =>
    { liftedCone :=
        { x := Groupₓₓ.of (types.limit_cone (F ⋙ forget Groupₓₓ)).x,
          π :=
            { app := Mon.limitπMonoidHom (F ⋙ forget₂ Groupₓₓ Mon.{u}),
              naturality' := (Mon.HasLimits.limitCone (F ⋙ forget₂ _ _)).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (Mon.HasLimits.limitConeIsLimit _) t,
      makesLimit :=
        is_limit.of_faithful (forget₂ Groupₓₓ Mon.{u}) (Mon.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl }

/-- 
A choice of limit cone for a functor into `Group`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `Group`.\n(Generally, you'll just want to use `limit F`.)"]
def limit_cone (F : J ⥤ Groupₓₓ) : cone F :=
  lift_limit (limit.is_limit (F ⋙ forget₂ Groupₓₓ Mon.{u}))

/-- 
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.\n(Generally, you'll just want to use `limit.cone F`.)"]
def limit_cone_is_limit (F : J ⥤ Groupₓₓ) : is_limit (limit_cone F) :=
  lifted_limit_is_limit _

-- failed to format: format: uncaught backtrack exception
/-- The category of groups has all limits. -/ @[ to_additive ]
  instance
    has_limits
    : has_limits Groupₓₓ
    where HasLimitsOfShape J 𝒥 := by exact { HasLimit := fun F => has_limit_of_created F ( forget₂ Groupₓₓ Mon ) }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from groups to monoids preserves all limits.
      (That is, the underlying monoid could have been computed instead as limits in the category
      of monoids.)
      -/
    @[ to_additive AddGroupₓₓ.forget₂AddMonPreservesLimits ]
  instance
    forget₂_Mon_preserves_limits
    : preserves_limits ( forget₂ Groupₓₓ Mon )
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from groups to types preserves all limits. (That is, the underlying
      types could have been computed instead as limits in the category of types.)
      -/
    @[ to_additive ]
  instance
    forget_preserves_limits
    : preserves_limits ( forget Groupₓₓ )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by exact { PreservesLimit := fun F => limits.comp_preserves_limit ( forget₂ Groupₓₓ Mon ) ( forget Mon ) }

end Groupₓₓ

namespace CommGroupₓₓ

@[to_additive]
instance comm_group_obj (F : J ⥤ CommGroupₓₓ) j : CommGroupₓ ((F ⋙ forget CommGroupₓₓ).obj j) := by
  change CommGroupₓ (F.obj j)
  infer_instance

@[to_additive]
instance limit_comm_group (F : J ⥤ CommGroupₓₓ) : CommGroupₓ (types.limit_cone (F ⋙ forget CommGroupₓₓ.{u})).x :=
  @Subgroup.toCommGroup (∀ j, F.obj j) _ (Groupₓₓ.sectionsSubgroup (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ.{u}))

/-- 
We show that the forgetful functor `CommGroup ⥤ Group` creates limits.

All we need to do is notice that the limit point has a `comm_group` instance available,
and then reuse the existing limit.
-/
@[to_additive]
instance (F : J ⥤ CommGroupₓₓ) : creates_limit F (forget₂ CommGroupₓₓ Groupₓₓ.{u}) :=
  creates_limit_of_reflects_iso fun c' t =>
    { liftedCone :=
        { x := CommGroupₓₓ.of (types.limit_cone (F ⋙ forget CommGroupₓₓ)).x,
          π :=
            { app := Mon.limitπMonoidHom (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ.{u} ⋙ forget₂ Groupₓₓ Mon),
              naturality' := (Mon.HasLimits.limitCone _).π.naturality } },
      validLift := by
        apply is_limit.unique_up_to_iso (Groupₓₓ.limitConeIsLimit _) t,
      makesLimit :=
        is_limit.of_faithful (forget₂ _ Groupₓₓ.{u} ⋙ forget₂ _ Mon.{u})
          (by
            apply Mon.HasLimits.limitConeIsLimit _)
          (fun s => _) fun s => rfl }

/-- 
A choice of limit cone for a functor into `CommGroup`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive "A choice of limit cone for a functor into `CommGroup`.\n(Generally, you'll just want to use `limit F`.)"]
def limit_cone (F : J ⥤ CommGroupₓₓ) : cone F :=
  lift_limit (limit.is_limit (F ⋙ forget₂ CommGroupₓₓ Groupₓₓ.{u}))

/-- 
The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive "The chosen cone is a limit cone.\n(Generally, you'll just wantto use `limit.cone F`.)"]
def limit_cone_is_limit (F : J ⥤ CommGroupₓₓ) : is_limit (limit_cone F) :=
  lifted_limit_is_limit _

-- failed to format: format: uncaught backtrack exception
/-- The category of commutative groups has all limits. -/ @[ to_additive ]
  instance
    has_limits
    : has_limits CommGroupₓₓ
    where
      HasLimitsOfShape J 𝒥 := by exact { HasLimit := fun F => has_limit_of_created F ( forget₂ CommGroupₓₓ Groupₓₓ ) }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from commutative groups to groups preserves all limits.
      (That is, the underlying group could have been computed instead as limits in the category
      of groups.)
      -/
    @[ to_additive AddCommGroupₓₓ.forget₂AddGroupPreservesLimits ]
  instance
    forget₂_Group_preserves_limits
    : preserves_limits ( forget₂ CommGroupₓₓ Groupₓₓ )
    where PreservesLimitsOfShape J 𝒥 := { PreservesLimit := fun F => by infer_instance }

/-- 
An auxiliary declaration to speed up typechecking.
-/
@[to_additive AddCommGroupₓₓ.forget₂AddCommMonPreservesLimitsAux "An auxiliary declaration to speed up typechecking."]
def forget₂_CommMon_preserves_limits_aux (F : J ⥤ CommGroupₓₓ) :
    is_limit ((forget₂ CommGroupₓₓ CommMon).mapCone (limit_cone F)) :=
  CommMon.limitConeIsLimit (F ⋙ forget₂ CommGroupₓₓ CommMon)

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from commutative groups to commutative monoids preserves all limits.
      (That is, the underlying commutative monoids could have been computed instead as limits
      in the category of commutative monoids.)
      -/
    @[ to_additive AddCommGroupₓₓ.forget₂AddCommMonPreservesLimits ]
  instance
    forget₂_CommMon_preserves_limits
    : preserves_limits ( forget₂ CommGroupₓₓ CommMon )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by
          exact
            {
              PreservesLimit
                :=
                fun
                  F
                    =>
                    preserves_limit_of_preserves_limit_cone
                      ( limit_cone_is_limit F ) ( forget₂_CommMon_preserves_limits_aux F )
              }

-- failed to format: format: uncaught backtrack exception
/--
      The forgetful functor from commutative groups to types preserves all limits. (That is, the
      underlying types could have been computed instead as limits in the category of types.)
      -/
    @[ to_additive AddCommGroupₓₓ.forgetPreservesLimits ]
  instance
    forget_preserves_limits
    : preserves_limits ( forget CommGroupₓₓ )
    where
      PreservesLimitsOfShape
        J 𝒥
        :=
        by
          exact
            {
              PreservesLimit := fun F => limits.comp_preserves_limit ( forget₂ CommGroupₓₓ Groupₓₓ ) ( forget Groupₓₓ )
              }

end CommGroupₓₓ

namespace AddCommGroupₓₓ

/-- 
The categorical kernel of a morphism in `AddCommGroup`
agrees with the usual group-theoretical kernel.
-/
def kernel_iso_ker {G H : AddCommGroupₓₓ} (f : G ⟶ H) : kernel f ≅ AddCommGroupₓₓ.of f.ker :=
  { Hom :=
      { toFun := fun g =>
          ⟨kernel.ι f g, by
            change (kernel.ι f) g ∈ f.ker
            simp [AddMonoidHom.mem_ker]⟩,
        map_zero' := by
          ext
          simp ,
        map_add' := fun g g' => by
          ext
          simp },
    inv :=
      kernel.lift f (AddSubgroup.subtype f.ker)
        (by
          tidy),
    hom_inv_id' := by
      apply equalizer.hom_ext _
      ext
      simp ,
    inv_hom_id' := by
      apply AddCommGroupₓₓ.ext
      simp only [AddMonoidHom.coe_mk, coe_id, coe_comp]
      rintro ⟨x, mem⟩
      simp }

@[simp]
theorem kernel_iso_ker_hom_comp_subtype {G H : AddCommGroupₓₓ} (f : G ⟶ H) :
    (kernel_iso_ker f).Hom ≫ AddSubgroup.subtype f.ker = kernel.ι f := by
  ext <;> rfl

@[simp]
theorem kernel_iso_ker_inv_comp_ι {G H : AddCommGroupₓₓ} (f : G ⟶ H) :
    (kernel_iso_ker f).inv ≫ kernel.ι f = AddSubgroup.subtype f.ker := by
  ext
  simp [kernel_iso_ker]

/-- 
The categorical kernel inclusion for `f : G ⟶ H`, as an object over `G`,
agrees with the `subtype` map.
-/
@[simps]
def kernel_iso_ker_over {G H : AddCommGroupₓₓ.{u}} (f : G ⟶ H) :
    over.mk (kernel.ι f) ≅ @over.mk _ _ G (AddCommGroupₓₓ.of f.ker) (AddSubgroup.subtype f.ker) :=
  over.iso_mk (kernel_iso_ker f)
    (by
      simp )

end AddCommGroupₓₓ

