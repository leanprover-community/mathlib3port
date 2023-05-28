/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Andrew Yang

! This file was ported from Lean 3 source module category_theory.monoidal.End
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Functor

/-!
# Endofunctors as a monoidal category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/


universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

#print CategoryTheory.endofunctorMonoidalCategory /-
/-- The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).
-/
def endofunctorMonoidalCategory : MonoidalCategory (C ⥤ C)
    where
  tensorObj F G := F ⋙ G
  tensorHom F G F' G' α β := α ◫ β
  tensorUnit := 𝟭 C
  associator F G H := Functor.associator F G H
  leftUnitor F := Functor.leftUnitor F
  rightUnitor F := Functor.rightUnitor F
#align category_theory.endofunctor_monoidal_category CategoryTheory.endofunctorMonoidalCategory
-/

open CategoryTheory.MonoidalCategory

attribute [local instance] endofunctor_monoidal_category

attribute [local reducible] endofunctor_monoidal_category

#print CategoryTheory.tensoringRightMonoidal /-
/-- Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
@[simps]
def tensoringRightMonoidal [MonoidalCategory.{v} C] : MonoidalFunctor C (C ⥤ C) :=
  {-- We could avoid needing to do this explicitly by
      -- constructing a partially applied analogue of `associator_nat_iso`.
      tensoringRight
      C with
    ε := (rightUnitorNatIso C).inv
    μ := fun X Y =>
      { app := fun Z => (α_ Z X Y).Hom
        naturality' := fun Z Z' f => by dsimp; rw [associator_naturality]; simp }
    μ_natural' := fun X Y X' Y' f g => by
      ext Z; dsimp
      simp only [← id_tensor_comp_tensor_id g f, id_tensor_comp, ← tensor_id, category.assoc,
        associator_naturality, associator_naturality_assoc]
    associativity' := fun X Y Z => by ext W; dsimp; simp [pentagon]
    left_unitality' := fun X => by ext Y; dsimp; rw [category.id_comp, triangle, ← tensor_comp];
      simp
    right_unitality' := fun X => by
      ext Y; dsimp
      rw [tensor_id, category.comp_id, right_unitor_tensor_inv, category.assoc,
        iso.inv_hom_id_assoc, ← id_tensor_comp, iso.inv_hom_id, tensor_id]
    ε_isIso := by infer_instance
    μ_isIso := fun X Y =>
      ⟨⟨{   app := fun Z => (α_ Z X Y).inv
            naturality' := fun Z Z' f => by dsimp; rw [← associator_inv_naturality]; simp }, by
          tidy⟩⟩ }
#align category_theory.tensoring_right_monoidal CategoryTheory.tensoringRightMonoidal
-/

variable {C}

variable {M : Type _} [Category M] [MonoidalCategory M] (F : MonoidalFunctor M (C ⥤ C))

/- warning: category_theory.μ_hom_inv_app -> CategoryTheory.μ_hom_inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_hom_inv_app CategoryTheory.μ_hom_inv_appₓ'. -/
@[simp, reassoc]
theorem μ_hom_inv_app (i j : M) (X : C) : (F.μ i j).app X ≫ (F.μIso i j).inv.app X = 𝟙 _ :=
  (F.μIso i j).hom_inv_id_app X
#align category_theory.μ_hom_inv_app CategoryTheory.μ_hom_inv_app

/- warning: category_theory.μ_inv_hom_app -> CategoryTheory.μ_inv_hom_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_inv_hom_app CategoryTheory.μ_inv_hom_appₓ'. -/
@[simp, reassoc]
theorem μ_inv_hom_app (i j : M) (X : C) : (F.μIso i j).inv.app X ≫ (F.μ i j).app X = 𝟙 _ :=
  (F.μIso i j).inv_hom_id_app X
#align category_theory.μ_inv_hom_app CategoryTheory.μ_inv_hom_app

/- warning: category_theory.ε_hom_inv_app -> CategoryTheory.ε_hom_inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.ε_hom_inv_app CategoryTheory.ε_hom_inv_appₓ'. -/
@[simp, reassoc]
theorem ε_hom_inv_app (X : C) : F.ε.app X ≫ F.εIso.inv.app X = 𝟙 _ :=
  F.εIso.hom_inv_id_app X
#align category_theory.ε_hom_inv_app CategoryTheory.ε_hom_inv_app

/- warning: category_theory.ε_inv_hom_app -> CategoryTheory.ε_inv_hom_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.ε_inv_hom_app CategoryTheory.ε_inv_hom_appₓ'. -/
@[simp, reassoc]
theorem ε_inv_hom_app (X : C) : F.εIso.inv.app X ≫ F.ε.app X = 𝟙 _ :=
  F.εIso.inv_hom_id_app X
#align category_theory.ε_inv_hom_app CategoryTheory.ε_inv_hom_app

/- warning: category_theory.ε_naturality -> CategoryTheory.ε_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.ε_naturality CategoryTheory.ε_naturalityₓ'. -/
@[simp, reassoc]
theorem ε_naturality {X Y : C} (f : X ⟶ Y) : F.ε.app X ≫ (F.obj (𝟙_ M)).map f = f ≫ F.ε.app Y :=
  (F.ε.naturality f).symm
#align category_theory.ε_naturality CategoryTheory.ε_naturality

/- warning: category_theory.ε_inv_naturality -> CategoryTheory.ε_inv_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.ε_inv_naturality CategoryTheory.ε_inv_naturalityₓ'. -/
@[simp, reassoc]
theorem ε_inv_naturality {X Y : C} (f : X ⟶ Y) :
    (F.obj (𝟙_ M)).map f ≫ F.εIso.inv.app Y = F.εIso.inv.app X ≫ f :=
  F.εIso.inv.naturality f
#align category_theory.ε_inv_naturality CategoryTheory.ε_inv_naturality

/- warning: category_theory.μ_naturality -> CategoryTheory.μ_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_naturality CategoryTheory.μ_naturalityₓ'. -/
@[simp, reassoc]
theorem μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
    (F.obj n).map ((F.obj m).map f) ≫ (F.μ m n).app Y = (F.μ m n).app X ≫ (F.obj _).map f :=
  (F.toLaxMonoidalFunctor.μ m n).naturality f
#align category_theory.μ_naturality CategoryTheory.μ_naturality

/- warning: category_theory.μ_inv_naturality -> CategoryTheory.μ_inv_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_inv_naturality CategoryTheory.μ_inv_naturalityₓ'. -/
-- This is a simp lemma in the reverse direction via `nat_trans.naturality`.
@[reassoc]
theorem μ_inv_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
    (F.μIso m n).inv.app X ≫ (F.obj n).map ((F.obj m).map f) =
      (F.obj _).map f ≫ (F.μIso m n).inv.app Y :=
  ((F.μIso m n).inv.naturality f).symm
#align category_theory.μ_inv_naturality CategoryTheory.μ_inv_naturality

/- warning: category_theory.μ_naturality₂ -> CategoryTheory.μ_naturality₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_naturality₂ CategoryTheory.μ_naturality₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- This is not a simp lemma since it could be proved by the lemmas later.
@[reassoc]
theorem μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) :
    (F.map g).app ((F.obj m).obj X) ≫ (F.obj n').map ((F.map f).app X) ≫ (F.μ m' n').app X =
      (F.μ m n).app X ≫ (F.map (f ⊗ g)).app X :=
  by
  have := congr_app (F.to_lax_monoidal_functor.μ_natural f g) X
  dsimp at this
  simpa using this
#align category_theory.μ_naturality₂ CategoryTheory.μ_naturality₂

/- warning: category_theory.μ_naturalityₗ -> CategoryTheory.μ_naturalityₗ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_naturalityₗ CategoryTheory.μ_naturalityₗₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc]
theorem μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
    (F.obj n).map ((F.map f).app X) ≫ (F.μ m' n).app X =
      (F.μ m n).app X ≫ (F.map (f ⊗ 𝟙 n)).app X :=
  by
  rw [← μ_naturality₂ F f (𝟙 n) X]
  simp
#align category_theory.μ_naturalityₗ CategoryTheory.μ_naturalityₗ

/- warning: category_theory.μ_naturalityᵣ -> CategoryTheory.μ_naturalityᵣ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_naturalityᵣ CategoryTheory.μ_naturalityᵣₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc]
theorem μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
    (F.map g).app ((F.obj m).obj X) ≫ (F.μ m n').app X =
      (F.μ m n).app X ≫ (F.map (𝟙 m ⊗ g)).app X :=
  by
  rw [← μ_naturality₂ F (𝟙 m) g X]
  simp
#align category_theory.μ_naturalityᵣ CategoryTheory.μ_naturalityᵣ

/- warning: category_theory.μ_inv_naturalityₗ -> CategoryTheory.μ_inv_naturalityₗ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_inv_naturalityₗ CategoryTheory.μ_inv_naturalityₗₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc]
theorem μ_inv_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
    (F.μIso m n).inv.app X ≫ (F.obj n).map ((F.map f).app X) =
      (F.map (f ⊗ 𝟙 n)).app X ≫ (F.μIso m' n).inv.app X :=
  by
  rw [← is_iso.comp_inv_eq, category.assoc, ← is_iso.eq_inv_comp]
  simp
#align category_theory.μ_inv_naturalityₗ CategoryTheory.μ_inv_naturalityₗ

/- warning: category_theory.μ_inv_naturalityᵣ -> CategoryTheory.μ_inv_naturalityᵣ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.μ_inv_naturalityᵣ CategoryTheory.μ_inv_naturalityᵣₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, reassoc]
theorem μ_inv_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
    (F.μIso m n).inv.app X ≫ (F.map g).app ((F.obj m).obj X) =
      (F.map (𝟙 m ⊗ g)).app X ≫ (F.μIso m n').inv.app X :=
  by
  rw [← is_iso.comp_inv_eq, category.assoc, ← is_iso.eq_inv_comp]
  simp
#align category_theory.μ_inv_naturalityᵣ CategoryTheory.μ_inv_naturalityᵣ

/- warning: category_theory.left_unitality_app -> CategoryTheory.left_unitality_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.left_unitality_app CategoryTheory.left_unitality_appₓ'. -/
@[reassoc]
theorem left_unitality_app (n : M) (X : C) :
    (F.obj n).map (F.ε.app X) ≫ (F.μ (𝟙_ M) n).app X ≫ (F.map (λ_ n).Hom).app X = 𝟙 _ :=
  by
  have := congr_app (F.to_lax_monoidal_functor.left_unitality n) X
  dsimp at this
  simpa using this.symm
#align category_theory.left_unitality_app CategoryTheory.left_unitality_app

/- warning: category_theory.obj_ε_app -> CategoryTheory.obj_ε_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.obj_ε_app CategoryTheory.obj_ε_appₓ'. -/
@[reassoc, simp]
theorem obj_ε_app (n : M) (X : C) :
    (F.obj n).map (F.ε.app X) = (F.map (λ_ n).inv).app X ≫ (F.μIso (𝟙_ M) n).inv.app X :=
  by
  refine' Eq.trans _ (category.id_comp _)
  rw [← category.assoc, ← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc]
  convert left_unitality_app F n X
  · simp
  · ext; simpa
#align category_theory.obj_ε_app CategoryTheory.obj_ε_app

/- warning: category_theory.obj_ε_inv_app -> CategoryTheory.obj_ε_inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.obj_ε_inv_app CategoryTheory.obj_ε_inv_appₓ'. -/
@[reassoc, simp]
theorem obj_ε_inv_app (n : M) (X : C) :
    (F.obj n).map (F.εIso.inv.app X) = (F.μ (𝟙_ M) n).app X ≫ (F.map (λ_ n).Hom).app X :=
  by
  rw [← cancel_mono ((F.obj n).map (F.ε.app X)), ← functor.map_comp]
  simpa
#align category_theory.obj_ε_inv_app CategoryTheory.obj_ε_inv_app

/- warning: category_theory.right_unitality_app -> CategoryTheory.right_unitality_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.right_unitality_app CategoryTheory.right_unitality_appₓ'. -/
@[reassoc]
theorem right_unitality_app (n : M) (X : C) :
    F.ε.app ((F.obj n).obj X) ≫ (F.μ n (𝟙_ M)).app X ≫ (F.map (ρ_ n).Hom).app X = 𝟙 _ :=
  by
  have := congr_app (F.to_lax_monoidal_functor.right_unitality n) X
  dsimp at this
  simpa using this.symm
#align category_theory.right_unitality_app CategoryTheory.right_unitality_app

/- warning: category_theory.ε_app_obj -> CategoryTheory.ε_app_obj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.ε_app_obj CategoryTheory.ε_app_objₓ'. -/
@[simp]
theorem ε_app_obj (n : M) (X : C) :
    F.ε.app ((F.obj n).obj X) = (F.map (ρ_ n).inv).app X ≫ (F.μIso n (𝟙_ M)).inv.app X :=
  by
  refine' Eq.trans _ (category.id_comp _)
  rw [← category.assoc, ← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc]
  convert right_unitality_app F n X
  · simp
  · ext; simpa
#align category_theory.ε_app_obj CategoryTheory.ε_app_obj

/- warning: category_theory.ε_inv_app_obj -> CategoryTheory.ε_inv_app_obj is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.ε_inv_app_obj CategoryTheory.ε_inv_app_objₓ'. -/
@[simp]
theorem ε_inv_app_obj (n : M) (X : C) :
    F.εIso.inv.app ((F.obj n).obj X) = (F.μ n (𝟙_ M)).app X ≫ (F.map (ρ_ n).Hom).app X :=
  by
  rw [← cancel_mono (F.ε.app ((F.obj n).obj X)), ε_inv_hom_app]
  simpa
#align category_theory.ε_inv_app_obj CategoryTheory.ε_inv_app_obj

/- warning: category_theory.associativity_app -> CategoryTheory.associativity_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.associativity_app CategoryTheory.associativity_appₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[reassoc]
theorem associativity_app (m₁ m₂ m₃ : M) (X : C) :
    (F.obj m₃).map ((F.μ m₁ m₂).app X) ≫
        (F.μ (m₁ ⊗ m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).Hom).app X =
      (F.μ m₂ m₃).app ((F.obj m₁).obj X) ≫ (F.μ m₁ (m₂ ⊗ m₃)).app X :=
  by
  have := congr_app (F.to_lax_monoidal_functor.associativity m₁ m₂ m₃) X
  dsimp at this
  simpa using this
#align category_theory.associativity_app CategoryTheory.associativity_app

/- warning: category_theory.obj_μ_app -> CategoryTheory.obj_μ_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.obj_μ_app CategoryTheory.obj_μ_appₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[reassoc, simp]
theorem obj_μ_app (m₁ m₂ m₃ : M) (X : C) :
    (F.obj m₃).map ((F.μ m₁ m₂).app X) =
      (F.μ m₂ m₃).app ((F.obj m₁).obj X) ≫
        (F.μ m₁ (m₂ ⊗ m₃)).app X ≫
          (F.map (α_ m₁ m₂ m₃).inv).app X ≫ (F.μIso (m₁ ⊗ m₂) m₃).inv.app X :=
  by
  rw [← associativity_app_assoc]
  dsimp
  simp
  dsimp
  simp
#align category_theory.obj_μ_app CategoryTheory.obj_μ_app

/- warning: category_theory.obj_μ_inv_app -> CategoryTheory.obj_μ_inv_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.obj_μ_inv_app CategoryTheory.obj_μ_inv_appₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[reassoc, simp]
theorem obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) :
    (F.obj m₃).map ((F.μIso m₁ m₂).inv.app X) =
      (F.μ (m₁ ⊗ m₂) m₃).app X ≫
        (F.map (α_ m₁ m₂ m₃).Hom).app X ≫
          (F.μIso m₁ (m₂ ⊗ m₃)).inv.app X ≫ (F.μIso m₂ m₃).inv.app ((F.obj m₁).obj X) :=
  by
  rw [← is_iso.inv_eq_inv]
  convert obj_μ_app F m₁ m₂ m₃ X using 1
  · ext; rw [← functor.map_comp]; simp
  · simp only [monoidal_functor.μ_iso_hom, category.assoc, nat_iso.inv_inv_app, is_iso.inv_comp]
    congr
    · ext; simp
    · ext; simpa
#align category_theory.obj_μ_inv_app CategoryTheory.obj_μ_inv_app

/- warning: category_theory.obj_zero_map_μ_app -> CategoryTheory.obj_zero_map_μ_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.obj_zero_map_μ_app CategoryTheory.obj_zero_map_μ_appₓ'. -/
@[simp, reassoc]
theorem obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) :
    (F.obj (𝟙_ M)).map f ≫ (F.μ m (𝟙_ M)).app _ = F.εIso.inv.app _ ≫ f ≫ (F.map (ρ_ m).inv).app _ :=
  by
  rw [← is_iso.inv_comp_eq, ← is_iso.comp_inv_eq]
  simp
#align category_theory.obj_zero_map_μ_app CategoryTheory.obj_zero_map_μ_app

/- warning: category_theory.obj_μ_zero_app -> CategoryTheory.obj_μ_zero_app is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.obj_μ_zero_app CategoryTheory.obj_μ_zero_appₓ'. -/
@[simp]
theorem obj_μ_zero_app (m₁ m₂ : M) (X : C) :
    (F.obj m₂).map ((F.μ m₁ (𝟙_ M)).app X) =
      (F.μ (𝟙_ M) m₂).app ((F.obj m₁).obj X) ≫
        (F.map (λ_ m₂).Hom).app ((F.obj m₁).obj X) ≫ (F.obj m₂).map ((F.map (ρ_ m₁).inv).app X) :=
  by
  rw [← obj_ε_inv_app_assoc, ← functor.map_comp]
  congr ; simp
#align category_theory.obj_μ_zero_app CategoryTheory.obj_μ_zero_app

/- warning: category_theory.unit_of_tensor_iso_unit -> CategoryTheory.unitOfTensorIsoUnit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {M : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} M] [_inst_3 : CategoryTheory.MonoidalCategory.{u4, u3} M _inst_2] (F : CategoryTheory.MonoidalFunctor.{u4, max u2 u1, u3, max u1 u2} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1)) (m : M) (n : M), (CategoryTheory.Iso.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) -> (CategoryTheory.Iso.{max u2 u1, max u1 u2} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (CategoryTheory.Functor.obj.{u4, max u2 u1, u3, max u1 u2} M _inst_2 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, max u2 u1, u3, max u1 u2} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, max u2 u1, u3, max u1 u2} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) F)) m) (CategoryTheory.Functor.obj.{u4, max u2 u1, u3, max u1 u2} M _inst_2 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, max u2 u1, u3, max u1 u2} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, max u2 u1, u3, max u1 u2} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) F)) n)) (CategoryTheory.Functor.id.{u1, u2} C _inst_1))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {M : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} M] [_inst_3 : CategoryTheory.MonoidalCategory.{u4, u3} M _inst_2] (F : CategoryTheory.MonoidalFunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1)) (m : M) (n : M), (CategoryTheory.Iso.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) -> (CategoryTheory.Iso.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.comp.{u1, u1, u1, u2, u2, u2} C _inst_1 C _inst_1 C _inst_1 (Prefunctor.obj.{succ u4, max (succ u2) (succ u1), u3, max u2 u1} M (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2)) (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) F))) m) (Prefunctor.obj.{succ u4, max (succ u2) (succ u1), u3, max u2 u1} M (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2)) (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u2 u1, max u2 u1} (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1) F))) n)) (CategoryTheory.Functor.id.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.unit_of_tensor_iso_unit CategoryTheory.unitOfTensorIsoUnitₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`. -/
@[simps]
noncomputable def unitOfTensorIsoUnit (m n : M) (h : m ⊗ n ≅ 𝟙_ M) : F.obj m ⋙ F.obj n ≅ 𝟭 C :=
  F.μIso m n ≪≫ F.toFunctor.mapIso h ≪≫ F.εIso.symm
#align category_theory.unit_of_tensor_iso_unit CategoryTheory.unitOfTensorIsoUnit

/- warning: category_theory.equiv_of_tensor_iso_unit -> CategoryTheory.equivOfTensorIsoUnit is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {M : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} M] [_inst_3 : CategoryTheory.MonoidalCategory.{u4, u3} M _inst_2], (CategoryTheory.MonoidalFunctor.{u4, max u2 u1, u3, max u1 u2} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1)) -> (forall (m : M) (n : M) (h₁ : CategoryTheory.Iso.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) (h₂ : CategoryTheory.Iso.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)), (Eq.{succ u4} (Quiver.Hom.{succ u4, u3} M (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2)) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) m) (CategoryTheory.CategoryStruct.comp.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) m) m (CategoryTheory.MonoidalCategory.tensorHom.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) m m (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) h₁) (CategoryTheory.CategoryStruct.id.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) m)) (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) m) m (CategoryTheory.MonoidalCategory.leftUnitor.{u4, u3} M _inst_2 _inst_3 m))) (CategoryTheory.CategoryStruct.comp.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m)) m (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m)) (CategoryTheory.MonoidalCategory.associator.{u4, u3} M _inst_2 _inst_3 m n m)) (CategoryTheory.CategoryStruct.comp.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m)) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) m (CategoryTheory.MonoidalCategory.tensorHom.{u4, u3} M _inst_2 _inst_3 m m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) (CategoryTheory.CategoryStruct.id.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) m) (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) h₂)) (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) m (CategoryTheory.MonoidalCategory.rightUnitor.{u4, u3} M _inst_2 _inst_3 m))))) -> (CategoryTheory.Equivalence.{u1, u1, u2, u2} C _inst_1 C _inst_1))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {M : Type.{u3}} [_inst_2 : CategoryTheory.Category.{u4, u3} M] [_inst_3 : CategoryTheory.MonoidalCategory.{u4, u3} M _inst_2], (CategoryTheory.MonoidalFunctor.{u4, max u2 u1, u3, max u2 u1} M _inst_2 _inst_3 (CategoryTheory.Functor.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u1, u1, u2, u2} C _inst_1 C _inst_1) (CategoryTheory.endofunctorMonoidalCategory.{u1, u2} C _inst_1)) -> (forall (m : M) (n : M) (h₁ : CategoryTheory.Iso.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) (h₂ : CategoryTheory.Iso.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)), (Eq.{succ u4} (Quiver.Hom.{succ u4, u3} M (CategoryTheory.CategoryStruct.toQuiver.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2)) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) m) (CategoryTheory.CategoryStruct.comp.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) m) m (CategoryTheory.MonoidalCategory.tensorHom.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) m m (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) h₁) (CategoryTheory.CategoryStruct.id.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) m)) (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorUnit'.{u4, u3} M _inst_2 _inst_3) m) m (CategoryTheory.MonoidalCategory.leftUnitor.{u4, u3} M _inst_2 _inst_3 m))) (CategoryTheory.CategoryStruct.comp.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m)) m (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m n) m) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m)) (CategoryTheory.MonoidalCategory.associator.{u4, u3} M _inst_2 _inst_3 m n m)) (CategoryTheory.CategoryStruct.comp.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m)) (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3)) m (CategoryTheory.MonoidalCategory.tensorHom.{u4, u3} M _inst_2 _inst_3 m m (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) (CategoryTheory.CategoryStruct.id.{u4, u3} M (CategoryTheory.Category.toCategoryStruct.{u4, u3} M _inst_2) m) (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 n m) (CategoryTheory.MonoidalCategory.tensorUnit.{u4, u3} M _inst_2 _inst_3) h₂)) (CategoryTheory.Iso.hom.{u4, u3} M _inst_2 (CategoryTheory.MonoidalCategory.tensorObj.{u4, u3} M _inst_2 _inst_3 m (CategoryTheory.MonoidalCategory.tensorUnit'.{u4, u3} M _inst_2 _inst_3)) m (CategoryTheory.MonoidalCategory.rightUnitor.{u4, u3} M _inst_2 _inst_3 m))))) -> (CategoryTheory.Equivalence.{u1, u1, u2, u2} C C _inst_1 _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.equiv_of_tensor_iso_unit CategoryTheory.equivOfTensorIsoUnitₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`. -/
@[simps]
noncomputable def equivOfTensorIsoUnit (m n : M) (h₁ : m ⊗ n ≅ 𝟙_ M) (h₂ : n ⊗ m ≅ 𝟙_ M)
    (H : (h₁.Hom ⊗ 𝟙 m) ≫ (λ_ m).Hom = (α_ m n m).Hom ≫ (𝟙 m ⊗ h₂.Hom) ≫ (ρ_ m).Hom) : C ≌ C
    where
  Functor := F.obj m
  inverse := F.obj n
  unitIso := (unitOfTensorIsoUnit F m n h₁).symm
  counitIso := unitOfTensorIsoUnit F n m h₂
  functor_unitIso_comp' := by
    intro X
    dsimp
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, ε_inv_app_obj, category.assoc,
      obj_μ_inv_app, functor.map_comp, μ_inv_hom_app_assoc, obj_ε_app,
      unit_of_tensor_iso_unit_inv_app]
    simp [← nat_trans.comp_app, ← F.to_functor.map_comp, ← H, -functor.map_comp]
#align category_theory.equiv_of_tensor_iso_unit CategoryTheory.equivOfTensorIsoUnit

end CategoryTheory

