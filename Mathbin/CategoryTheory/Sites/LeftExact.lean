/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.left_exact
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.Sheafification
import Mathbin.CategoryTheory.Sites.Limits
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Left exactness of sheafification
In this file we show that sheafification commutes with finite limits.
-/


open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe w v u

variable {C : Type max v u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]

noncomputable section

namespace CategoryTheory.GrothendieckTopology

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagram_functor D X` preserves limits. -/
@[simps]
def coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation {X : C} {K : Type max v u}
    [SmallCategory K] {F : K ⥤ Cᵒᵖ ⥤ D} {W : J.Cover X} (i : W.Arrow)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj (op W))) :
    Cone (F ⋙ (evaluation _ _).obj (op i.y))
    where
  x := E.x
  π :=
    { app := fun k => E.π.app k ≫ multiequalizer.ι (W.index (F.obj k)) i
      naturality' := by
        intro a b f
        dsimp
        rw [Category.id_comp, Category.assoc, ← E.w f]
        dsimp [diagramNatTrans]
        simp only [multiequalizer.lift_ι, Category.assoc] }
#align category_theory.grothendieck_topology.cone_comp_evaluation_of_cone_comp_diagram_functor_comp_evaluation CategoryTheory.GrothendieckTopology.coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation

/-- An auxiliary definition to be used in the proof of the fact that
`J.diagram_functor D X` preserves limits. -/
abbrev liftToDiagramLimitObj {X : C} {K : Type max v u} [SmallCategory K] [HasLimitsOfShape K D]
    {W : (J.Cover X)ᵒᵖ} (F : K ⥤ Cᵒᵖ ⥤ D)
    (E : Cone (F ⋙ J.diagramFunctor D X ⋙ (evaluation (J.Cover X)ᵒᵖ D).obj W)) :
    E.x ⟶ (J.diagram (limit F) X).obj W :=
  multiequalizer.lift _ _
    (fun i =>
      (isLimitOfPreserves ((evaluation _ _).obj (op i.y)) (limit.isLimit _)).lift
        (coneCompEvaluationOfConeCompDiagramFunctorCompEvaluation i E))
    (by
      intro i
      change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _
      dsimp [evaluateCombinedCones]
      erw [Category.comp_id, Category.comp_id, Category.assoc, Category.assoc, ←
        (limit.lift F _).naturality, ← (limit.lift F _).naturality, ← Category.assoc, ←
        Category.assoc]
      congr 1; ext1
      erw [Category.assoc, Category.assoc, limit.lift_π, limit.lift_π, limit.lift_π_assoc,
        limit.lift_π_assoc, Category.assoc, Category.assoc, multiequalizer.condition]
      rfl)
#align category_theory.grothendieck_topology.lift_to_diagram_limit_obj CategoryTheory.GrothendieckTopology.liftToDiagramLimitObj

instance (X : C) (K : Type max v u) [SmallCategory K] [HasLimitsOfShape K D] (F : K ⥤ Cᵒᵖ ⥤ D) :
    PreservesLimit F (J.diagramFunctor D X) :=
  preservesLimitOfEvaluation _ _ fun W =>
    preservesLimitOfPreservesLimitCone (limit.isLimit _)
      { lift := fun E => liftToDiagramLimitObj F E
        fac' := by
          intro E k
          dsimp [diagramNatTrans]
          ext1
          simp only [multiequalizer.lift_ι, multiequalizer.lift_ι_assoc, Category.assoc]
          change (_ ≫ _) ≫ _ = _
          dsimp [evaluateCombinedCones]
          erw [Category.comp_id, Category.assoc, ← NatTrans.comp_app, limit.lift_π, limit.lift_π]
          rfl
        uniq' := by
          intro E m hm
          ext
          delta lift_to_diagram_limit_obj
          erw [multiequalizer.lift_ι, Category.assoc]
          change _ = (_ ≫ _) ≫ _
          dsimp [evaluateCombinedCones]
          erw [Category.comp_id, Category.assoc, ← NatTrans.comp_app, limit.lift_π, limit.lift_π]
          dsimp
          rw [← hm]
          dsimp [diagramNatTrans]
          simp }

instance (X : C) (K : Type max v u) [SmallCategory K] [HasLimitsOfShape K D] :
    PreservesLimitsOfShape K (J.diagramFunctor D X) :=
  ⟨⟩

instance (X : C) [HasLimits D] : PreservesLimits (J.diagramFunctor D X) :=
  ⟨⟩

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [ConcreteCategory.{max v u} D]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

/-- An auxiliary definition to be used in the proof that `J.plus_functor D` commutes
with finite limits. -/
def liftToPlusObjLimitObj {K : Type max v u} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) :
    S.x ⟶ (J.plusObj (limit F)).obj (op X) :=
  let e := colimitLimitIso (F ⋙ J.diagramFunctor D X)
  let t : J.diagram (limit F) X ≅ limit (F ⋙ J.diagramFunctor D X) :=
    (isLimitOfPreserves (J.diagramFunctor D X) (limit.isLimit _)).conePointUniqueUpToIso
      (limit.isLimit _)
  let p : (J.plusObj (limit F)).obj (op X) ≅ colimit (limit (F ⋙ J.diagramFunctor D X)) :=
    HasColimit.isoOfNatIso t
  let s :
    colimit (F ⋙ J.diagramFunctor D X).flip ≅ F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X) :=
    NatIso.ofComponents (fun k => colimitObjIsoColimitCompEvaluation _ k)
      (by
        intro i j f
        rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
        ext w
        dsimp [plusMap]
        erw [colimit.ι_map_assoc,
          colimitObjIsoColimitCompEvaluation_ι_inv (F ⋙ J.diagram_functor D X).flip w j,
          colimitObjIsoColimitCompEvaluation_ι_inv_assoc (F ⋙ J.diagram_functor D X).flip w i]
        rw [← (colimit.ι (F ⋙ J.diagram_functor D X).flip w).naturality]
        rfl)
  limit.lift _ S ≫ (HasLimit.isoOfNatIso s.symm).hom ≫ e.inv ≫ p.inv
#align category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj

-- This lemma should not be used directly. Instead, one should use the fact that
-- `J.plus_functor D` preserves finite limits, along with the fact that
-- evaluation preserves limits.
theorem liftToPlusObjLimitObj_fac {K : Type max v u} [SmallCategory K] [FinCategory K]
    [HasLimitsOfShape K D] [PreservesLimitsOfShape K (forget D)]
    [ReflectsLimitsOfShape K (forget D)] (F : K ⥤ Cᵒᵖ ⥤ D) (X : C)
    (S : Cone (F ⋙ J.plusFunctor D ⋙ (evaluation Cᵒᵖ D).obj (op X))) (k) :
    liftToPlusObjLimitObj F X S ≫ (J.plusMap (limit.π F k)).app (op X) = S.π.app k :=
  by
  dsimp only [liftToPlusObjLimitObj]
  rw [← (limit.isLimit (F ⋙ J.plus_functor D ⋙ (evaluation Cᵒᵖ D).obj (op X))).fac S k,
    Category.assoc]
  congr 1
  dsimp
  simp only [Category.assoc]
  rw [← Iso.eq_inv_comp, Iso.inv_comp_eq, Iso.inv_comp_eq]
  ext
  dsimp [plusMap]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, ι_colimMap]
  dsimp [IsLimit.conePointUniqueUpToIso, HasLimit.isoOfNatIso, IsLimit.map]
  rw [limit.lift_π]
  dsimp
  rw [ι_colimitLimitIso_limit_π_assoc]
  simp_rw [← NatTrans.comp_app, ← Category.assoc, ← NatTrans.comp_app]
  rw [limit.lift_π, Category.assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  erw [colimit.ι_desc]
  rfl
#align category_theory.grothendieck_topology.lift_to_plus_obj_limit_obj_fac CategoryTheory.GrothendieckTopology.liftToPlusObjLimitObj_fac

instance (K : Type max v u) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.plusFunctor D) :=
  by
  constructor; intro F; apply preservesLimitOfEvaluation; intro X
  apply preservesLimitOfPreservesLimitCone (limit.isLimit F)
  refine' ⟨fun S => liftToPlusObjLimitObj F X.unop S, _, _⟩
  · intro S k
    apply liftToPlusObjLimitObj_fac
  · intro S m hm
    dsimp [liftToPlusObjLimitObj]
    simp_rw [← Category.assoc, Iso.eq_comp_inv, ← Iso.comp_inv_eq]
    ext
    simp only [limit.lift_π, Category.assoc, ← hm]
    congr 1
    ext
    dsimp [plusMap, plusObj]
    erw [colimit.ι_map, colimit.ι_desc_assoc, limit.lift_π]
    dsimp
    simp only [Category.assoc]
    rw [ι_colimitLimitIso_limit_π_assoc]
    simp only [NatIso.ofComponents_inv_app, colimitObjIsoColimitCompEvaluation_ι_app_hom,
      Iso.symm_inv]
    dsimp [IsLimit.conePointUniqueUpToIso]
    rw [← Category.assoc, ← NatTrans.comp_app, limit.lift_π]
    rfl

instance [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [ReflectsIsomorphisms (forget D)] :
    PreservesFiniteLimits (J.plusFunctor D) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  intro K _ _
  haveI : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShapeOfReflectsIsomorphisms
  infer_instance

instance (K : Type max v u) [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]
    [PreservesLimitsOfShape K (forget D)] [ReflectsLimitsOfShape K (forget D)] :
    PreservesLimitsOfShape K (J.sheafification D) :=
  Limits.compPreservesLimitsOfShape _ _

instance [HasFiniteLimits D] [PreservesFiniteLimits (forget D)] [ReflectsIsomorphisms (forget D)] :
    PreservesFiniteLimits (J.sheafification D) :=
  Limits.compPreservesFiniteLimits _ _

end CategoryTheory.GrothendieckTopology

namespace CategoryTheory

variable [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

variable [ConcreteCategory.{max v u} D]

variable [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]

variable [PreservesLimits (forget D)]

variable [ReflectsIsomorphisms (forget D)]

variable (K : Type max v u)

variable [SmallCategory K] [FinCategory K] [HasLimitsOfShape K D]

instance : PreservesLimitsOfShape K (presheafToSheaf J D) :=
  by
  constructor; intro F; constructor; intro S hS
  apply isLimitOfReflects (sheafToPresheaf J D)
  haveI : ReflectsLimitsOfShape K (forget D) := reflectsLimitsOfShapeOfReflectsIsomorphisms
  apply isLimitOfPreserves (J.sheafification D) hS

instance [HasFiniteLimits D] : PreservesFiniteLimits (presheafToSheaf J D) :=
  by
  apply preservesFiniteLimitsOfPreservesFiniteLimitsOfSize.{max v u}
  intros ; skip; infer_instance

end CategoryTheory

