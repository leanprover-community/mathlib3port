/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import CategoryTheory.Products.Basic

#align_import category_theory.products.associator from "leanprover-community/mathlib"@"1ead22342e1a078bd44744ace999f85756555d35"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.prod

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] (E : Type u₃)
  [Category.{v₃} E]

#print CategoryTheory.prod.associator /-
/-- The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
@[simps]
def associator : (C × D) × E ⥤ C × D × E
    where
  obj X := (X.1.1, (X.1.2, X.2))
  map _ _ f := (f.1.1, (f.1.2, f.2))
#align category_theory.prod.associator CategoryTheory.prod.associator
-/

#print CategoryTheory.prod.inverseAssociator /-
/-- The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simps]
def inverseAssociator : C × D × E ⥤ (C × D) × E
    where
  obj X := ((X.1, X.2.1), X.2.2)
  map _ _ f := ((f.1, f.2.1), f.2.2)
#align category_theory.prod.inverse_associator CategoryTheory.prod.inverseAssociator
-/

#print CategoryTheory.prod.associativity /-
/-- The equivalence of categories expressing associativity of products of categories.
-/
def associativity : (C × D) × E ≌ C × D × E :=
  Equivalence.mk (associator C D E) (inverseAssociator C D E)
    (NatIso.ofComponents (fun X => eqToIso (by simp)) (by tidy))
    (NatIso.ofComponents (fun X => eqToIso (by simp)) (by tidy))
#align category_theory.prod.associativity CategoryTheory.prod.associativity
-/

#print CategoryTheory.prod.associatorIsEquivalence /-
instance associatorIsEquivalence : CategoryTheory.Functor.IsEquivalence (associator C D E) :=
  (by infer_instance : CategoryTheory.Functor.IsEquivalence (associativity C D E).Functor)
#align category_theory.prod.associator_is_equivalence CategoryTheory.prod.associatorIsEquivalence
-/

#print CategoryTheory.prod.inverseAssociatorIsEquivalence /-
instance inverseAssociatorIsEquivalence :
    CategoryTheory.Functor.IsEquivalence (inverseAssociator C D E) :=
  (by infer_instance : CategoryTheory.Functor.IsEquivalence (associativity C D E).inverse)
#align category_theory.prod.inverse_associator_is_equivalence CategoryTheory.prod.inverseAssociatorIsEquivalence
-/

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.prod

