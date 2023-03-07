/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.adjunction.evaluation
! leanprover-community/mathlib commit 937c692d73f5130c7fecd3fd32e81419f4e04eb7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Products
import Mathbin.CategoryTheory.Functor.EpiMono

/-!

# Adjunctions involving evaluation

We show that evaluation of functors have adjoints, given the existence of (co)products.

-/


namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

noncomputable section

section

variable [∀ a b : C, HasCoproductsOfShape (a ⟶ b) D]

#print CategoryTheory.evaluationLeftAdjoint /-
/-- The left adjoint of evaluation. -/
@[simps]
def evaluationLeftAdjoint (c : C) : D ⥤ C ⥤ D
    where
  obj d :=
    { obj := fun t => ∐ fun i : c ⟶ t => d
      map := fun u v f => Sigma.desc fun g => (Sigma.ι fun _ => d) <| g ≫ f
      map_id' := by
        intros ; ext ⟨j⟩; simp only [cofan.mk_ι_app, colimit.ι_desc, category.comp_id]
        congr 1; rw [category.comp_id]
      map_comp' := by
        intros ; ext; simp only [cofan.mk_ι_app, colimit.ι_desc_assoc, colimit.ι_desc]
        congr 1; rw [category.assoc] }
  map d₁ d₂ f :=
    { app := fun e => Sigma.desc fun h => f ≫ Sigma.ι (fun _ => d₂) h
      naturality' := by
        intros
        ext
        dsimp
        simp }
  map_id' := by
    intros
    ext (x⟨j⟩)
    dsimp
    simp
  map_comp' := by
    intros
    ext
    dsimp
    simp
#align category_theory.evaluation_left_adjoint CategoryTheory.evaluationLeftAdjoint
-/

/- warning: category_theory.evaluation_adjunction_right -> CategoryTheory.evaluationAdjunctionRight is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasCoproductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.Adjunction.{u2, max u3 u2, u4, max u1 u2 u3 u4} D _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.evaluationLeftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.evaluationAdjunctionRight._proof_1.{u3, u4, u1, u2} C _inst_1 D _inst_2 _inst_3) c) (CategoryTheory.Functor.obj.{u1, max (max u1 u2 u3 u4) u2, u3, max (max u3 u2) u2 (max u1 u2 u3 u4) u4} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2) c)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasCoproductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.Adjunction.{u2, max u2 u3, u4, max (max (max u4 u2) u3) u1} D _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.evaluationLeftAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 (fun (a : C) (b : C) => _inst_3 a b) c) (Prefunctor.obj.{succ u1, max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3), u3, max (max (max u4 u2) u1) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, max (max (max u4 u2) u3) u1, u3, max (max (max u4 u2) u3) u1} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2)) c)
Case conversion may be inaccurate. Consider using '#align category_theory.evaluation_adjunction_right CategoryTheory.evaluationAdjunctionRightₓ'. -/
/-- The adjunction showing that evaluation is a right adjoint. -/
@[simps unit_app counit_app_app]
def evaluationAdjunctionRight (c : C) : evaluationLeftAdjoint D c ⊣ (evaluation _ _).obj c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun d F =>
        { toFun := fun f => Sigma.ι (fun _ => d) (𝟙 _) ≫ f.app c
          invFun := fun f =>
            { app := fun e => Sigma.desc fun h => f ≫ F.map h
              naturality' := by
                intros
                ext
                dsimp
                simp }
          left_inv := by
            intro f
            ext (x⟨g⟩)
            dsimp
            simp only [colimit.ι_desc, limits.cofan.mk_ι_app, category.assoc, ← f.naturality,
              evaluation_left_adjoint_obj_map, colimit.ι_desc_assoc, cofan.mk_ι_app]
            congr 2
            rw [category.id_comp]
          right_inv := fun f => by
            dsimp
            simp }
      homEquiv_naturality_left_symm := by
        intros
        ext
        dsimp
        simp
      homEquiv_naturality_right := by
        intros
        dsimp
        simp }
#align category_theory.evaluation_adjunction_right CategoryTheory.evaluationAdjunctionRight

/- warning: category_theory.evaluation_is_right_adjoint -> CategoryTheory.evaluationIsRightAdjoint is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasCoproductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.IsRightAdjoint.{u2, max u3 u2, u4, max u1 u2 u3 u4} D _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.obj.{u1, max (max u1 u2 u3 u4) u2, u3, max (max u3 u2) u2 (max u1 u2 u3 u4) u4} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2) c)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasCoproductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.IsRightAdjoint.{u2, max u2 u3, u4, max (max (max u4 u2) u1) u3} D _inst_2 (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) (Prefunctor.obj.{succ u1, max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3), u3, max (max (max u4 u2) u1) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, max (max (max u4 u2) u3) u1, u3, max (max (max u4 u2) u3) u1} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2)) c)
Case conversion may be inaccurate. Consider using '#align category_theory.evaluation_is_right_adjoint CategoryTheory.evaluationIsRightAdjointₓ'. -/
instance evaluationIsRightAdjoint (c : C) : IsRightAdjoint ((evaluation _ D).obj c) :=
  ⟨_, evaluationAdjunctionRight _ _⟩
#align category_theory.evaluation_is_right_adjoint CategoryTheory.evaluationIsRightAdjoint

/- warning: category_theory.nat_trans.mono_iff_mono_app -> CategoryTheory.NatTrans.mono_iff_mono_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasCoproductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (η : Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2))) F G), Iff (CategoryTheory.Mono.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) F G η) (forall (c : C), CategoryTheory.Mono.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F c) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G c) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G η c))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasCoproductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (η : Quiver.Hom.{max (succ u3) (succ u2), max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2))) F G), Iff (CategoryTheory.Mono.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) F G η) (forall (c : C), CategoryTheory.Mono.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) c) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) c) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G η c))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.mono_iff_mono_app CategoryTheory.NatTrans.mono_iff_mono_appₓ'. -/
theorem NatTrans.mono_iff_mono_app {F G : C ⥤ D} (η : F ⟶ G) : Mono η ↔ ∀ c, Mono (η.app c) :=
  by
  constructor
  · intro h c
    exact (inferInstance : mono (((evaluation _ _).obj c).map η))
  · intro _
    apply nat_trans.mono_of_mono_app
#align category_theory.nat_trans.mono_iff_mono_app CategoryTheory.NatTrans.mono_iff_mono_app

end

section

variable [∀ a b : C, HasProductsOfShape (a ⟶ b) D]

#print CategoryTheory.evaluationRightAdjoint /-
/-- The right adjoint of evaluation. -/
@[simps]
def evaluationRightAdjoint (c : C) : D ⥤ C ⥤ D
    where
  obj d :=
    { obj := fun t => ∏ fun i : t ⟶ c => d
      map := fun u v f => Pi.lift fun g => Pi.π _ <| f ≫ g
      map_id' := by
        intros ; ext ⟨j⟩; dsimp
        simp only [limit.lift_π, category.id_comp, fan.mk_π_app]
        congr ; simp
      map_comp' := by
        intros ; ext ⟨j⟩; dsimp
        simp only [limit.lift_π, fan.mk_π_app, category.assoc]
        congr 1; simp }
  map d₁ d₂ f :=
    { app := fun t => Pi.lift fun g => Pi.π _ g ≫ f
      naturality' := by
        intros
        ext
        dsimp
        simp }
  map_id' := by
    intros
    ext (x⟨j⟩)
    dsimp
    simp
  map_comp' := by
    intros
    ext
    dsimp
    simp
#align category_theory.evaluation_right_adjoint CategoryTheory.evaluationRightAdjoint
-/

/- warning: category_theory.evaluation_adjunction_left -> CategoryTheory.evaluationAdjunctionLeft is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasProductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.Adjunction.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2 (CategoryTheory.Functor.obj.{u1, max (max u1 u2 u3 u4) u2, u3, max (max u3 u2) u2 (max u1 u2 u3 u4) u4} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2) c) (CategoryTheory.evaluationRightAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 (CategoryTheory.evaluationAdjunctionLeft._proof_1.{u3, u4, u1, u2} C _inst_1 D _inst_2 _inst_3) c)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasProductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.Adjunction.{max u2 u3, u2, max (max (max u4 u2) u1) u3, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2 (Prefunctor.obj.{succ u1, max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3), u3, max (max (max u4 u2) u1) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, max (max (max u4 u2) u3) u1, u3, max (max (max u4 u2) u3) u1} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2)) c) (CategoryTheory.evaluationRightAdjoint.{u1, u2, u3, u4} C _inst_1 D _inst_2 (fun (a : C) (b : C) => _inst_3 a b) c)
Case conversion may be inaccurate. Consider using '#align category_theory.evaluation_adjunction_left CategoryTheory.evaluationAdjunctionLeftₓ'. -/
/-- The adjunction showing that evaluation is a left adjoint. -/
@[simps unit_app_app counit_app]
def evaluationAdjunctionLeft (c : C) : (evaluation _ _).obj c ⊣ evaluationRightAdjoint D c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F d =>
        { toFun := fun f =>
            { app := fun t => Pi.lift fun g => F.map g ≫ f
              naturality' := by
                intros
                ext
                dsimp
                simp }
          invFun := fun f => f.app _ ≫ Pi.π _ (𝟙 _)
          left_inv := fun f => by
            dsimp
            simp
          right_inv := by
            intro f
            ext (x⟨g⟩)
            dsimp
            simp only [limit.lift_π, evaluation_right_adjoint_obj_map, nat_trans.naturality_assoc,
              fan.mk_π_app]
            congr
            rw [category.comp_id] }
      homEquiv_naturality_left_symm := by
        intros
        dsimp
        simp
      homEquiv_naturality_right := by
        intros
        ext
        dsimp
        simp }
#align category_theory.evaluation_adjunction_left CategoryTheory.evaluationAdjunctionLeft

/- warning: category_theory.evaluation_is_left_adjoint -> CategoryTheory.evaluationIsLeftAdjoint is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasProductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.IsLeftAdjoint.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2 (CategoryTheory.Functor.obj.{u1, max (max u1 u2 u3 u4) u2, u3, max (max u3 u2) u2 (max u1 u2 u3 u4) u4} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max u1 u2 u3 u4, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2) c)
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasProductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] (c : C), CategoryTheory.IsLeftAdjoint.{max u2 u3, u2, max (max (max u4 u2) u1) u3, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2 (Prefunctor.obj.{succ u1, max (max (max (succ u4) (succ u2)) (succ u1)) (succ u3), u3, max (max (max u4 u2) u1) u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max (max (max u4 u2) u3) u1, max (max (max u4 u2) u3) u1} (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2))) (CategoryTheory.Functor.toPrefunctor.{u1, max (max (max u4 u2) u3) u1, u3, max (max (max u4 u2) u3) u1} C _inst_1 (CategoryTheory.Functor.{max u3 u2, u2, max (max (max u4 u3) u2) u1, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.Functor.category.{max u3 u2, u2, max (max (max u3 u4) u1) u2, u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) D _inst_2) (CategoryTheory.evaluation.{u1, u2, u3, u4} C _inst_1 D _inst_2)) c)
Case conversion may be inaccurate. Consider using '#align category_theory.evaluation_is_left_adjoint CategoryTheory.evaluationIsLeftAdjointₓ'. -/
instance evaluationIsLeftAdjoint (c : C) : IsLeftAdjoint ((evaluation _ D).obj c) :=
  ⟨_, evaluationAdjunctionLeft _ _⟩
#align category_theory.evaluation_is_left_adjoint CategoryTheory.evaluationIsLeftAdjoint

/- warning: category_theory.nat_trans.epi_iff_epi_app -> CategoryTheory.NatTrans.epi_iff_epi_app is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasProductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (η : Quiver.Hom.{succ (max u3 u2), max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2))) F G), Iff (CategoryTheory.Epi.{max u3 u2, max u1 u2 u3 u4} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) F G η) (forall (c : C), CategoryTheory.Epi.{u2, u4} D _inst_2 (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 F c) (CategoryTheory.Functor.obj.{u1, u2, u3, u4} C _inst_1 D _inst_2 G c) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G η c))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] (D : Type.{u4}) [_inst_2 : CategoryTheory.Category.{u2, u4} D] [_inst_3 : forall (a : C) (b : C), CategoryTheory.Limits.HasProductsOfShape.{u1, u4, u2} (Quiver.Hom.{succ u1, u3} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) a b) D _inst_2] {F : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} {G : CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2} (η : Quiver.Hom.{max (succ u3) (succ u2), max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.CategoryStruct.toQuiver.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Category.toCategoryStruct.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2))) F G), Iff (CategoryTheory.Epi.{max u3 u2, max (max (max u3 u4) u1) u2} (CategoryTheory.Functor.{u1, u2, u3, u4} C _inst_1 D _inst_2) (CategoryTheory.Functor.category.{u1, u2, u3, u4} C _inst_1 D _inst_2) F G η) (forall (c : C), CategoryTheory.Epi.{u2, u4} D _inst_2 (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 F) c) (Prefunctor.obj.{succ u1, succ u2, u3, u4} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u3} C (CategoryTheory.Category.toCategoryStruct.{u1, u3} C _inst_1)) D (CategoryTheory.CategoryStruct.toQuiver.{u2, u4} D (CategoryTheory.Category.toCategoryStruct.{u2, u4} D _inst_2)) (CategoryTheory.Functor.toPrefunctor.{u1, u2, u3, u4} C _inst_1 D _inst_2 G) c) (CategoryTheory.NatTrans.app.{u1, u2, u3, u4} C _inst_1 D _inst_2 F G η c))
Case conversion may be inaccurate. Consider using '#align category_theory.nat_trans.epi_iff_epi_app CategoryTheory.NatTrans.epi_iff_epi_appₓ'. -/
theorem NatTrans.epi_iff_epi_app {F G : C ⥤ D} (η : F ⟶ G) : Epi η ↔ ∀ c, Epi (η.app c) :=
  by
  constructor
  · intro h c
    exact (inferInstance : epi (((evaluation _ _).obj c).map η))
  · intros
    apply nat_trans.epi_of_epi_app
#align category_theory.nat_trans.epi_iff_epi_app CategoryTheory.NatTrans.epi_iff_epi_app

end

end CategoryTheory

