/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module category_theory.category.Kleisli
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Basic

/-!
# The Kleisli construction on the Type category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Define the Kleisli category for (control) monads.
`category_theory/monad/kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with category_theory.monad
-/


universe u v

namespace CategoryTheory

#print CategoryTheory.KleisliCat /-
/-- The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unused_arguments]
def KleisliCat (m : Type u → Type v) :=
  Type u
#align category_theory.Kleisli CategoryTheory.KleisliCat
-/

#print CategoryTheory.KleisliCat.mk /-
/-- Construct an object of the Kleisli category from a type. -/
def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  α
#align category_theory.Kleisli.mk CategoryTheory.KleisliCat.mk
-/

#print CategoryTheory.KleisliCat.categoryStruct /-
instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] : CategoryStruct (KleisliCat m)
    where
  Hom α β := α → m β
  id α x := pure x
  comp X Y Z f g := f >=> g
#align category_theory.Kleisli.category_struct CategoryTheory.KleisliCat.categoryStruct
-/

#print CategoryTheory.KleisliCat.category /-
instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  refine' {   id_comp' := _
              comp_id' := _
              assoc' := _ } <;> intros <;> ext <;> unfold_projs <;>
    simp only [(· >=> ·), functor_norm]
#align category_theory.Kleisli.category CategoryTheory.KleisliCat.category
-/

/- warning: category_theory.Kleisli.id_def -> CategoryTheory.KleisliCat.id_def is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] (α : CategoryTheory.KleisliCat.{u1, u2} m), Eq.{succ (max u1 u2)} (Quiver.Hom.{succ (max u1 u2), succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u2} m _inst_1)) α α) (CategoryTheory.CategoryStruct.id.{max u1 u2, succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u2} m _inst_1) α) (Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m (Monad.toApplicative.{u1, u2} m _inst_1)) α)
but is expected to have type
  forall {m : Type.{u2} -> Type.{u1}} [_inst_1 : Monad.{u2, u1} m] (α : CategoryTheory.KleisliCat.{u2, u1} m), Eq.{max (succ u1) (succ u2)} (Quiver.Hom.{succ (max u1 u2), succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u2, u1} m _inst_1)) α α) (CategoryTheory.CategoryStruct.id.{max u1 u2, succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u2, u1} m _inst_1) α) (Pure.pure.{u2, u1} m (Applicative.toPure.{u2, u1} m (Monad.toApplicative.{u2, u1} m _inst_1)) α)
Case conversion may be inaccurate. Consider using '#align category_theory.Kleisli.id_def CategoryTheory.KleisliCat.id_defₓ'. -/
@[simp]
theorem KleisliCat.id_def {m} [Monad m] (α : KleisliCat m) : 𝟙 α = @pure m _ α :=
  rfl
#align category_theory.Kleisli.id_def CategoryTheory.KleisliCat.id_def

/- warning: category_theory.Kleisli.comp_def -> CategoryTheory.KleisliCat.comp_def is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] (α : CategoryTheory.KleisliCat.{u1, u2} m) (β : CategoryTheory.KleisliCat.{u1, u2} m) (γ : CategoryTheory.KleisliCat.{u1, u2} m) (xs : Quiver.Hom.{succ (max u1 u2), succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u2} m _inst_1)) α β) (ys : Quiver.Hom.{succ (max u1 u2), succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u2} m _inst_1)) β γ) (a : α), Eq.{succ u2} (m γ) (CategoryTheory.CategoryStruct.comp.{max u1 u2, succ u1} (CategoryTheory.KleisliCat.{u1, u2} m) (CategoryTheory.KleisliCat.categoryStruct.{u1, u2} m _inst_1) α β γ xs ys a) (Bind.bind.{u1, u2} m (Monad.toHasBind.{u1, u2} m _inst_1) β γ (xs a) ys)
but is expected to have type
  forall {m : Type.{u2} -> Type.{u1}} [_inst_1 : Monad.{u2, u1} m] (α : CategoryTheory.KleisliCat.{u2, u1} m) (β : CategoryTheory.KleisliCat.{u2, u1} m) (γ : CategoryTheory.KleisliCat.{u2, u1} m) (xs : Quiver.Hom.{max (succ u1) (succ u2), succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u2, u1} m _inst_1)) α β) (ys : Quiver.Hom.{max (succ u1) (succ u2), succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u2, u1} m _inst_1)) β γ) (a : α), Eq.{succ u1} (m γ) (CategoryTheory.CategoryStruct.comp.{max u1 u2, succ u2} (CategoryTheory.KleisliCat.{u2, u1} m) (CategoryTheory.KleisliCat.categoryStruct.{u2, u1} m _inst_1) α β γ xs ys a) (Bind.bind.{u2, u1} m (Monad.toBind.{u2, u1} m _inst_1) β γ (xs a) ys)
Case conversion may be inaccurate. Consider using '#align category_theory.Kleisli.comp_def CategoryTheory.KleisliCat.comp_defₓ'. -/
theorem KleisliCat.comp_def {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    (xs ≫ ys) a = xs a >>= ys :=
  rfl
#align category_theory.Kleisli.comp_def CategoryTheory.KleisliCat.comp_def

instance : Inhabited (KleisliCat id) :=
  ⟨PUnit⟩

instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α) :=
  ⟨show α from default⟩

end CategoryTheory

