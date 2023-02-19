/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison

! This file was ported from Lean 3 source module category_theory.products.associator
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Products.Basic

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

/- warning: category_theory.prod.associativity -> CategoryTheory.prod.associativity is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u4}) [_inst_1 : CategoryTheory.Category.{u1, u4} C] (D : Type.{u5}) [_inst_2 : CategoryTheory.Category.{u2, u5} D] (E : Type.{u6}) [_inst_3 : CategoryTheory.Category.{u3, u6} E], CategoryTheory.Equivalence.{max (max u1 u2) u3, max u1 u2 u3, max (max u4 u5) u6, max u4 u5 u6} (Prod.{max u4 u5, u6} (Prod.{u4, u5} C D) E) (CategoryTheory.prod.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3) (Prod.{u4, max u5 u6} C (Prod.{u5, u6} D E)) (CategoryTheory.prod.{u1, max u2 u3, u4, max u5 u6} C _inst_1 (Prod.{u5, u6} D E) (CategoryTheory.prod.{u2, u3, u5, u6} D _inst_2 E _inst_3))
but is expected to have type
  forall (C : Type.{u4}) [_inst_1 : CategoryTheory.Category.{u1, u4} C] (D : Type.{u5}) [_inst_2 : CategoryTheory.Category.{u2, u5} D] (E : Type.{u6}) [_inst_3 : CategoryTheory.Category.{u3, u6} E], CategoryTheory.Equivalence.{max (max u1 u2) u3, max (max u1 u2) u3, max u6 u5 u4, max (max u6 u5) u4} (Prod.{max u5 u4, u6} (Prod.{u4, u5} C D) E) (Prod.{u4, max u6 u5} C (Prod.{u5, u6} D E)) (CategoryTheory.prod.{max u1 u2, u3, max u4 u5, u6} (Prod.{u4, u5} C D) (CategoryTheory.prod.{u1, u2, u4, u5} C _inst_1 D _inst_2) E _inst_3) (CategoryTheory.prod.{u1, max u2 u3, u4, max u5 u6} C _inst_1 (Prod.{u5, u6} D E) (CategoryTheory.prod.{u2, u3, u5, u6} D _inst_2 E _inst_3))
Case conversion may be inaccurate. Consider using '#align category_theory.prod.associativity CategoryTheory.prod.associativityₓ'. -/
/-- The equivalence of categories expressing associativity of products of categories.
-/
def associativity : (C × D) × E ≌ C × D × E :=
  Equivalence.mk (associator C D E) (inverseAssociator C D E)
    (NatIso.ofComponents (fun X => eqToIso (by simp)) (by tidy))
    (NatIso.ofComponents (fun X => eqToIso (by simp)) (by tidy))
#align category_theory.prod.associativity CategoryTheory.prod.associativity

#print CategoryTheory.prod.associatorIsEquivalence /-
instance associatorIsEquivalence : IsEquivalence (associator C D E) :=
  (by infer_instance : IsEquivalence (associativity C D E).Functor)
#align category_theory.prod.associator_is_equivalence CategoryTheory.prod.associatorIsEquivalence
-/

#print CategoryTheory.prod.inverseAssociatorIsEquivalence /-
instance inverseAssociatorIsEquivalence : IsEquivalence (inverseAssociator C D E) :=
  (by infer_instance : IsEquivalence (associativity C D E).inverse)
#align category_theory.prod.inverse_associator_is_equivalence CategoryTheory.prod.inverseAssociatorIsEquivalence
-/

-- TODO unitors?
-- TODO pentagon natural transformation? ...satisfying?
end CategoryTheory.prod

