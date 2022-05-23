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
(co)equalizers, and pullbacks / pushouts.

-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

/-- Turn a colimit for `F : J ⥤ C` into a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitCoconeOp (F : J ⥤ C) {c : Cocone F} (hc : IsColimit c) : IsLimit c.op where
  lift := fun s => (hc.desc s.unop).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac] using w (op j)

/-- Turn a limit for `F : J ⥤ C` into a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOp (F : J ⥤ C) {c : Cone F} (hc : IsLimit c) : IsColimit c.op where
  desc := fun s => (hc.lift s.unop).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac] using w (op j)

/-- Turn a colimit for `F : J ⥤ Cᵒᵖ` into a limit for `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeLeftOpOfCocone (F : J ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) : IsLimit (coneLeftOpOfCocone c) where
  lift := fun s => (hc.desc (coconeOfConeLeftOp s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj <| by
      simpa only [cone_left_op_of_cocone_π_app, op_comp, Quiver.Hom.op_unop, is_colimit.fac,
        cocone_of_cone_left_op_ι_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac, cocone_of_cone_left_op_ι_app] using w (op j)

/-- Turn a limit of `F : J ⥤ Cᵒᵖ` into a colimit of `F.left_op : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeLeftOpOfCone (F : J ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) : IsColimit (coconeLeftOpOfCone c) where
  desc := fun s => (hc.lift (coneOfCoconeLeftOp s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj <| by
      simpa only [cocone_left_op_of_cone_ι_app, op_comp, Quiver.Hom.op_unop, is_limit.fac, cone_of_cocone_left_op_π_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac, cone_of_cocone_left_op_π_app] using w (op j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ C` into a limit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeRightOpOfCocone (F : Jᵒᵖ ⥤ C) {c : Cocone F} (hc : IsColimit c) : IsLimit (coneRightOpOfCocone c) where
  lift := fun s => (hc.desc (coconeOfConeRightOp s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac] using w (unop j)

/-- Turn a limit for `F : Jᵒᵖ ⥤ C` into a colimit for `F.right_op : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeRightOpOfCone (F : Jᵒᵖ ⥤ C) {c : Cone F} (hc : IsLimit c) : IsColimit (coconeRightOpOfCone c) where
  desc := fun s => (hc.lift (coneOfCoconeRightOp s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac] using w (unop j)

/-- Turn a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F.unop : J ⥤ C`. -/
@[simps]
def isLimitConeUnopOfCocone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F} (hc : IsColimit c) : IsLimit (coneUnopOfCocone c) where
  lift := fun s => (hc.desc (coconeOfConeUnop s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac] using w (unop j)

/-- Turn a limit of `F : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit of `F.unop : J ⥤ C`. -/
@[simps]
def isColimitCoconeUnopOfCone (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F} (hc : IsLimit c) : IsColimit (coconeUnopOfCone c) where
  desc := fun s => (hc.lift (coneOfCoconeUnop s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac] using w (unop j)

/-- Turn a colimit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a limit for `F : J ⥤ C`. -/
@[simps]
def isLimitCoconeUnop (F : J ⥤ C) {c : Cocone F.op} (hc : IsColimit c) : IsLimit c.unop where
  lift := fun s => (hc.desc s.op).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac] using w (unop j)

/-- Turn a limit for `F.op : Jᵒᵖ ⥤ Cᵒᵖ` into a colimit for `F : J ⥤ C`. -/
@[simps]
def isColimitConeUnop (F : J ⥤ C) {c : Cone F.op} (hc : IsLimit c) : IsColimit c.unop where
  desc := fun s => (hc.lift s.op).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac] using w (unop j)

/-- Turn a colimit for `F.left_op : Jᵒᵖ ⥤ C` into a limit for `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cocone F.leftOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeLeftOp c) where
  lift := fun s => (hc.desc (coconeLeftOpOfCone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj <| by
      simpa only [cone_of_cocone_left_op_π_app, unop_comp, Quiver.Hom.unop_op, is_colimit.fac,
        cocone_left_op_of_cone_ι_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac, cone_of_cocone_left_op_π_app] using w (unop j)

/-- Turn a limit of `F.left_op : Jᵒᵖ ⥤ C` into a colimit of `F : J ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitCoconeOfConeLeftOp (F : J ⥤ Cᵒᵖ) {c : Cone F.leftOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeLeftOp c) where
  desc := fun s => (hc.lift (coneLeftOpOfCocone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj <| by
      simpa only [cocone_of_cone_left_op_ι_app, unop_comp, Quiver.Hom.unop_op, is_limit.fac,
        cone_left_op_of_cocone_π_app]
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac, cocone_of_cone_left_op_ι_app] using w (unop j)

/-- Turn a colimit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isLimitConeOfCoconeRightOp (F : Jᵒᵖ ⥤ C) {c : Cocone F.rightOp} (hc : IsColimit c) :
    IsLimit (coneOfCoconeRightOp c) where
  lift := fun s => (hc.desc (coconeRightOpOfCone s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_colimit.fac] using w (op j)

/-- Turn a limit for `F.right_op : J ⥤ Cᵒᵖ` into a limit for `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def isColimitCoconeOfConeRightOp (F : Jᵒᵖ ⥤ C) {c : Cone F.rightOp} (hc : IsLimit c) :
    IsColimit (coconeOfConeRightOp c) where
  desc := fun s => (hc.lift (coneRightOpOfCocone s)).unop
  fac' := fun s j =>
    Quiver.Hom.op_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.op_inj (hc.hom_ext fun j => Quiver.Hom.unop_inj _)
    simpa only [Quiver.Hom.op_unop, is_limit.fac] using w (op j)

/-- Turn a colimit for `F.unop : J ⥤ C` into a limit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isLimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cocone F.unop} (hc : IsColimit c) : IsLimit (coneOfCoconeUnop c) where
  lift := fun s => (hc.desc (coconeUnopOfCone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_colimit.fac] using w (op j)

/-- Turn a limit for `F.unop : J ⥤ C` into a colimit for `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def isColimitConeOfCoconeUnop (F : Jᵒᵖ ⥤ Cᵒᵖ) {c : Cone F.unop} (hc : IsLimit c) : IsColimit (coconeOfConeUnop c) where
  desc := fun s => (hc.lift (coneUnopOfCocone s)).op
  fac' := fun s j =>
    Quiver.Hom.unop_inj
      (by
        simpa)
  uniq' := fun s m w => by
    refine' Quiver.Hom.unop_inj (hc.hom_ext fun j => Quiver.Hom.op_inj _)
    simpa only [Quiver.Hom.unop_op, is_limit.fac] using w (op j)

/-- If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
theorem has_limit_of_has_colimit_left_op (F : J ⥤ Cᵒᵖ) [HasColimit F.leftOp] : HasLimit F :=
  HasLimit.mk
    { Cone := coneOfCoconeLeftOp (Colimit.cocone F.leftOp),
      IsLimit := isLimitConeOfCoconeLeftOp _ (colimit.isColimit _) }

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
theorem has_colimit_of_has_limit_left_op (F : J ⥤ Cᵒᵖ) [HasLimit F.leftOp] : HasColimit F :=
  HasColimit.mk
    { Cocone := coconeOfConeLeftOp (Limit.cone F.leftOp), IsColimit := isColimitCoconeOfConeLeftOp _ (limit.isLimit _) }

/-- If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
theorem has_colimits_of_shape_op_of_has_limits_of_shape [HasLimitsOfShape Jᵒᵖ C] : HasColimitsOfShape J Cᵒᵖ :=
  { HasColimit := fun F => has_colimit_of_has_limit_left_op F }

attribute [local instance] has_colimits_of_shape_op_of_has_limits_of_shape

/-- If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
theorem has_colimits_op_of_has_limits [HasLimits C] : HasColimits Cᵒᵖ :=
  ⟨inferInstance⟩

variable (X : Type v₁)

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
  { out := fun J 𝒟 => by
      skip
      have : has_limits_of_shape (discrete J)ᵒᵖ C := has_limits_of_shape_of_equivalence (discrete.opposite J).symm
      infer_instance }

theorem has_finite_products_opposite [HasFiniteCoproducts C] : HasFiniteProducts Cᵒᵖ :=
  { out := fun J 𝒟 => by
      skip
      have : has_colimits_of_shape (discrete J)ᵒᵖ C := has_colimits_of_shape_of_equivalence (discrete.opposite J).symm
      infer_instance }

theorem has_equalizers_opposite [HasCoequalizers C] : HasEqualizers Cᵒᵖ := by
  have : has_colimits_of_shape walking_parallel_pair.{v₁}ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walkingParallelPairOpEquiv.{v₁}
  infer_instance

theorem has_coequalizers_opposite [HasEqualizers C] : HasCoequalizers Cᵒᵖ := by
  have : has_limits_of_shape walking_parallel_pair.{v₁}ᵒᵖ C :=
    has_limits_of_shape_of_equivalence walkingParallelPairOpEquiv.{v₁}
  infer_instance

theorem has_finite_colimits_opposite [HasFiniteLimits C] : HasFiniteColimits Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      infer_instance }

theorem has_finite_limits_opposite [HasFiniteColimits C] : HasFiniteLimits Cᵒᵖ :=
  { out := fun J 𝒟 𝒥 => by
      skip
      infer_instance }

theorem has_pullbacks_opposite [HasPushouts C] : HasPullbacks Cᵒᵖ := by
  have : has_colimits_of_shape walking_cospan.{v₁}ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_cospan_op_equiv.symm
  apply has_limits_of_shape_op_of_has_colimits_of_shape

theorem has_pushouts_opposite [HasPullbacks C] : HasPushouts Cᵒᵖ := by
  have : has_limits_of_shape walking_span.{v₁}ᵒᵖ C := has_limits_of_shape_of_equivalence walking_span_op_equiv.symm
  apply has_colimits_of_shape_op_of_has_limits_of_shape

end CategoryTheory.Limits

