/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import Mathbin.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We also give special cases for (co)products,
but not yet for pullbacks / pushouts or for (co)equalizers.

-/


universe v u

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {J : Type v} [SmallCategory J]

variable (F : J ⥤ Cᵒᵖ)

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_limit_of_has_colimit_left_op [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { Cone := coneOfCoconeLeftOp (Colimit.cocone F.leftOp),
      IsLimit :=
        { lift := fun s => (colimit.desc F.leftOp (coconeLeftOpOfCone s)).op,
          fac' := fun s j => by
            rw [cone_of_cocone_left_op_π_app, colimit.cocone_ι, ← op_comp, colimit.ι_desc, cocone_left_op_of_cone_ι_app,
              Quiver.Hom.op_unop]
            rfl,
          uniq' := fun s m w => by
            refine' Quiver.Hom.unop_inj (colimit.hom_ext fun j => Quiver.Hom.op_inj _)
            simpa only [Quiver.Hom.unop_op, colimit.ι_desc] using w (unop j) } }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_limits_of_shape_op_of_has_colimits_of_shape [HasColimitsOfShape Jᵒᵖ C] : HasLimitsOfShape J Cᵒᵖ :=
  { HasLimit := fun F => has_limit_of_has_colimit_left_op F }

attribute [local instance] has_limits_of_shape_op_of_has_colimits_of_shape

/-- If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
theorem has_limits_op_of_has_colimits [HasColimits C] : HasLimits Cᵒᵖ :=
  ⟨inferInstance⟩

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_colimit_of_has_limit_left_op [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { Cocone := coconeOfConeLeftOp (Limit.cone F.leftOp),
      IsColimit :=
        { desc := fun s => (limit.lift F.leftOp (coneLeftOpOfCocone s)).op,
          fac' := fun s j => by
            rw [cocone_of_cone_left_op_ι_app, limit.cone_π, ← op_comp, limit.lift_π, cone_left_op_of_cocone_π_app,
              Quiver.Hom.op_unop]
            rfl,
          uniq' := fun s m w => by
            refine' Quiver.Hom.unop_inj (limit.hom_ext fun j => Quiver.Hom.op_inj _)
            simpa only [Quiver.Hom.unop_op, limit.lift_π] using w (unop j) } }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_colimits_of_shape_op_of_has_limits_of_shape [HasLimitsOfShape Jᵒᵖ C] : HasColimitsOfShape J Cᵒᵖ :=
  { HasColimit := fun F => has_colimit_of_has_limit_left_op F }

attribute [local instance] has_colimits_of_shape_op_of_has_limits_of_shape

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
theorem has_colimits_op_of_has_limits [HasLimits C] : HasColimits Cᵒᵖ :=
  ⟨inferInstance⟩

variable (X : Type v)

/-- If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
theorem has_coproducts_opposite [HasProductsOfShape X C] : HasCoproductsOfShape X Cᵒᵖ := by
  have : has_limits_of_shape (discrete X)ᵒᵖ C := has_limits_of_shape_of_equivalence (discrete.opposite X).symm
  infer_instance

/-- If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
theorem has_products_opposite [HasCoproductsOfShape X C] : HasProductsOfShape X Cᵒᵖ := by
  have : has_colimits_of_shape (discrete X)ᵒᵖ C := has_colimits_of_shape_of_equivalence (discrete.opposite X).symm
  infer_instance

theorem has_finite_coproducts_opposite [HasFiniteProducts C] : HasFiniteCoproducts Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      have : has_limits_of_shape (discrete J)ᵒᵖ C := has_limits_of_shape_of_equivalence (discrete.opposite J).symm
      infer_instance }

theorem has_finite_products_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      have : has_colimits_of_shape (discrete J)ᵒᵖ C := has_colimits_of_shape_of_equivalence (discrete.opposite J).symm
      infer_instance }

theorem has_equalizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ := by
  have : has_colimits_of_shape walking_parallel_pair.{v}ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walkingParallelPairOpEquiv.{v}
  infer_instance

theorem has_coequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ := by
  have : has_limits_of_shape walking_parallel_pair.{v}ᵒᵖ C :=
    has_limits_of_shape_of_equivalence walkingParallelPairOpEquiv.{v}
  infer_instance

theorem has_finite_colimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      infer_instance }

theorem has_finite_limits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      infer_instance }

end CategoryTheory.Limits

