/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import CategoryTheory.Limits.ColimitLimit
import CategoryTheory.Limits.Preserves.FunctorCategory
import CategoryTheory.Limits.Preserves.Finite
import CategoryTheory.Limits.Shapes.FiniteLimits
import CategoryTheory.Limits.Preserves.Filtered
import CategoryTheory.ConcreteCategory.Basic

#align_import category_theory.limits.filtered_colimit_commutes_finite_limit from "leanprover-community/mathlib"@"f2b757fc5c341d88741b9c4630b1e8ba973c5726"

/-!
# Filtered colimits commute with finite limits.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that for a functor `F : J × K ⥤ Type v`, when `J` is finite and `K` is filtered,
the universal morphism `colimit_limit_to_limit_colimit F` comparing the
colimit (over `K`) of the limits (over `J`) with the limit of the colimits is an isomorphism.

(In fact, to prove that it is injective only requires that `J` has finitely many objects.)

## References
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
* [Stacks: Filtered colimits](https://stacks.math.columbia.edu/tag/002W)
-/


universe v u

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits.Types

open CategoryTheory.Limits.Types.FilteredColimit

namespace CategoryTheory.Limits

variable {J K : Type v} [SmallCategory J] [SmallCategory K]

variable (F : J × K ⥤ Type v)

open CategoryTheory.prod

variable [IsFiltered K]

section

/-!
Injectivity doesn't need that we have finitely many morphisms in `J`,
only that there are finitely many objects.
-/


variable [Finite J]

#print CategoryTheory.Limits.colimitLimitToLimitColimit_injective /-
/-- This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
-/
theorem colimitLimitToLimitColimit_injective : Function.Injective (colimitLimitToLimitColimit F) :=
  by classical
#align category_theory.limits.colimit_limit_to_limit_colimit_injective CategoryTheory.Limits.colimitLimitToLimitColimit_injective
-/

-- Suppose we have two terms `x y` in the colimit (over `K`) of the limits (over `J`),
-- and that these have the same image under `colimit_limit_to_limit_colimit F`.
-- These elements of the colimit have representatives somewhere:
-- Since the images of `x` and `y` are equal in a limit, they are equal componentwise
-- (indexed by `j : J`),
-- and they are equations in a filtered colimit,
-- so for each `j` we have some place `k j` to the right of both `kx` and `ky`
-- where the images of the components of the representatives become equal:
-- We now use that `K` is filtered, picking some point to the right of all these
-- morphisms `f j` and `g j`.
-- Our goal is now an equation between equivalence classes of representatives of a colimit,
-- and so it suffices to show those representative become equal somewhere, in particular at `S`.
-- We can check if two elements of a limit (in `Type`) are equal by comparing them componentwise.
-- Now it's just a calculation using `W` and `w`.
end

variable [FinCategory J]

#print CategoryTheory.Limits.colimitLimitToLimitColimit_surjective /-
/-- This follows this proof from
* Borceux, Handbook of categorical algebra 1, Theorem 2.13.4
although with different names.
-/
theorem colimitLimitToLimitColimit_surjective :
    Function.Surjective (colimitLimitToLimitColimit F) := by classical
#align category_theory.limits.colimit_limit_to_limit_colimit_surjective CategoryTheory.Limits.colimitLimitToLimitColimit_surjective
-/

#print CategoryTheory.Limits.colimitLimitToLimitColimit_isIso /-
-- We begin with some element `x` in the limit (over J) over the colimits (over K),
-- This consists of some coherent family of elements in the various colimits,
-- and so our first task is to pick representatives of these elements.
-- `k : J ⟶ K` records where the representative of the element in the `j`-th element of `x` lives
-- `y j : F.obj (j, k j)` is the representative
-- and we record that these representatives, when mapped back into the relevant colimits,
-- are actually the components of `x`.
-- A little tidying up of things we no longer need.
-- As a first step, we use that `K` is filtered to pick some point `k' : K` above all the `k j`
-- and name the morphisms as `g j : k j ⟶ k'`.
-- Recalling that the components of `x`, which are indexed by `j : J`, are "coherent",
-- in other words preserved by morphisms in the `J` direction,
-- we see that for any morphism `f : j ⟶ j'` in `J`,
-- the images of `y j` and `y j'`, when mapped to `F.obj (j', k')` respectively by
-- `(f, g j)` and `(𝟙 j', g j')`, both represent the same element in the colimit.
-- Because `K` is filtered, we can restate this as saying that
-- for each such `f`, there is some place to the right of `k'`
-- where these images of `y j` and `y j'` become equal.
-- We take a moment to restate `w` more conveniently.
-- and clean up some things that are no longer needed.
-- We're now ready to use the fact that `K` is filtered a second time,
-- picking some place to the right of all of
-- the morphisms `gf f : k' ⟶ kh f` and `hf f : k' ⟶ kf f`.
-- At this point we're relying on there being only finitely morphisms in `J`.
-- We then restate this slightly more conveniently, as a family of morphism `i f : kf f ⟶ k''`,
-- satisfying `gf f ≫ i f = hf f' ≫ i f'`.
-- We're finally ready to construct the pre-image, and verify it really maps to `x`.
-- We construct the pre-image (which, recall is meant to be a point
-- in the colimit (over `K`) of the limits (over `J`)) via a representative at `k''`.
-- This representative is meant to be an element of a limit,
-- so we need to construct a family of elements in `F.obj (j, k'')` for varying `j`,
-- then show that are coherent with respect to morphisms in the `j` direction.
-- We construct the elements as the images of the `y j`.
-- After which it's just a calculation, using `s` and `wf`, to see they are coherent.
-- Finally we check that this maps to `x`.
-- We can do this componentwise:
-- and as each component is an equation in a colimit, we can verify it by
-- pointing out the morphism which carries one representative to the other:
instance colimitLimitToLimitColimit_isIso : IsIso (colimitLimitToLimitColimit F) :=
  (isIso_iff_bijective _).mpr
    ⟨colimitLimitToLimitColimit_injective F, colimitLimitToLimitColimit_surjective F⟩
#align category_theory.limits.colimit_limit_to_limit_colimit_is_iso CategoryTheory.Limits.colimitLimitToLimitColimit_isIso
-/

#print CategoryTheory.Limits.colimitLimitToLimitColimitCone_iso /-
instance colimitLimitToLimitColimitCone_iso (F : J ⥤ K ⥤ Type v) :
    IsIso (colimitLimitToLimitColimitCone F) :=
  by
  have : is_iso (colimit_limit_to_limit_colimit_cone F).Hom := by
    dsimp only [colimit_limit_to_limit_colimit_cone]; infer_instance
  apply cones.cone_iso_of_hom_iso
#align category_theory.limits.colimit_limit_to_limit_colimit_cone_iso CategoryTheory.Limits.colimitLimitToLimitColimitCone_iso
-/

#print CategoryTheory.Limits.filteredColimPreservesFiniteLimitsOfTypes /-
noncomputable instance filteredColimPreservesFiniteLimitsOfTypes :
    PreservesFiniteLimits (colim : (K ⥤ Type v) ⥤ _) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{v}
  intro J _ _; skip; constructor
  intro F; constructor
  intro c hc
  apply is_limit.of_iso_limit (limit.is_limit _)
  symm; trans colim.map_cone (limit.cone F)
  exact functor.map_iso _ (hc.unique_up_to_iso (limit.is_limit F))
  exact as_iso (colimitLimitToLimitColimitCone.{v, v + 1} F)
#align category_theory.limits.filtered_colim_preserves_finite_limits_of_types CategoryTheory.Limits.filteredColimPreservesFiniteLimitsOfTypes
-/

variable {C : Type u} [Category.{v} C] [ConcreteCategory.{v} C]

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]

variable [ReflectsLimitsOfShape J (forget C)] [PreservesColimitsOfShape K (forget C)]

variable [PreservesLimitsOfShape J (forget C)]

#print CategoryTheory.Limits.filteredColimPreservesFiniteLimits /-
noncomputable instance filteredColimPreservesFiniteLimits :
    PreservesLimitsOfShape J (colim : (K ⥤ C) ⥤ _) :=
  haveI : preserves_limits_of_shape J ((colim : (K ⥤ C) ⥤ _) ⋙ forget C) :=
    preserves_limits_of_shape_of_nat_iso (preserves_colimit_nat_iso _).symm
  preserves_limits_of_shape_of_reflects_of_preserves _ (forget C)
#align category_theory.limits.filtered_colim_preserves_finite_limits CategoryTheory.Limits.filteredColimPreservesFiniteLimits
-/

end

attribute [local instance] reflects_limits_of_shape_of_reflects_isomorphisms

noncomputable instance [PreservesFiniteLimits (forget C)] [PreservesFilteredColimits (forget C)]
    [HasFiniteLimits C] [HasColimitsOfShape K C] [ReflectsIsomorphisms (forget C)] :
    PreservesFiniteLimits (colim : (K ⥤ C) ⥤ _) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{v}
  intro J _ _; skip; infer_instance

section

variable [HasLimitsOfShape J C] [HasColimitsOfShape K C]

variable [ReflectsLimitsOfShape J (forget C)] [PreservesColimitsOfShape K (forget C)]

variable [PreservesLimitsOfShape J (forget C)]

#print CategoryTheory.Limits.colimitLimitIso /-
/-- A curried version of the fact that filtered colimits commute with finite limits. -/
noncomputable def colimitLimitIso (F : J ⥤ K ⥤ C) : colimit (limit F) ≅ limit (colimit F.flip) :=
  (isLimitOfPreserves colim (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    HasLimit.isoOfNatIso (colimitFlipIsoCompColim _).symm
#align category_theory.limits.colimit_limit_iso CategoryTheory.Limits.colimitLimitIso
-/

#print CategoryTheory.Limits.ι_colimitLimitIso_limit_π /-
@[simp, reassoc]
theorem ι_colimitLimitIso_limit_π (F : J ⥤ K ⥤ C) (a) (b) :
    colimit.ι (limit F) a ≫ (colimitLimitIso F).Hom ≫ limit.π (colimit F.flip) b =
      (limit.π F b).app a ≫ (colimit.ι F.flip a).app b :=
  by
  dsimp [colimit_limit_iso]
  simp only [functor.map_cone_π_app, iso.symm_hom,
    limits.limit.cone_point_unique_up_to_iso_hom_comp_assoc, limits.limit.cone_π,
    limits.colimit.ι_map_assoc, limits.colimit_flip_iso_comp_colim_inv_app, assoc,
    limits.has_limit.iso_of_nat_iso_hom_π]
  congr 1
  simp only [← category.assoc, iso.comp_inv_eq,
    limits.colimit_obj_iso_colimit_comp_evaluation_ι_app_hom,
    limits.has_colimit.iso_of_nat_iso_ι_hom, nat_iso.of_components_hom_app]
  dsimp
  simp
#align category_theory.limits.ι_colimit_limit_iso_limit_π CategoryTheory.Limits.ι_colimitLimitIso_limit_π
-/

end

end CategoryTheory.Limits

