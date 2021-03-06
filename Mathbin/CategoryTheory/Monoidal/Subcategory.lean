/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathbin.CategoryTheory.Monoidal.Braided
import Mathbin.CategoryTheory.ConcreteCategory.Basic

/-!
# Full monoidal subcategories

Given a monidal category `C` and a monoidal predicate on `C`, that is a function `P : C â Prop`
closed under `ð_` and `â`, we can put a monoidal structure on `{X : C // P X}` (the category
structure is defined in `category_theory.full_subcategory`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `category_theory.full_subcategory.lift`
-/


universe u v

namespace CategoryTheory

namespace MonoidalCategory

open Iso

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : C â Prop)

/-- A property `C â Prop` is a monoidal predicate if it is closed under `ð_` and `â`.
-/
class MonoidalPredicate where
  prop_id' : P (ð_ C) := by
    run_tac
      obviously
  prop_tensor' : â {X Y}, P X â P Y â P (X â Y) := by
    run_tac
      obviously

restate_axiom monoidal_predicate.prop_id'

restate_axiom monoidal_predicate.prop_tensor'

open MonoidalPredicate

variable [MonoidalPredicate P]

/-- When `P` is a monoidal predicate, the full subcategory `{X : C // P X}` inherits the monoidal
structure of `C`
-/
instance fullMonoidalSubcategory : MonoidalCategory { X : C // P X } where
  tensorObj := fun X Y => â¨X â Y, prop_tensor X.2 Y.2â©
  tensorHom := fun Xâ Yâ Xâ Yâ f g => by
    change Xâ.1 â Xâ.1 â¶ Yâ.1 â Yâ.1
    change Xâ.1 â¶ Yâ.1 at f
    change Xâ.1 â¶ Yâ.1 at g
    exact f â g
  tensorUnit := â¨ð_ C, prop_idâ©
  associator := fun X Y Z =>
    â¨(Î±_ X.1 Y.1 Z.1).Hom, (Î±_ X.1 Y.1 Z.1).inv, hom_inv_id (Î±_ X.1 Y.1 Z.1), inv_hom_id (Î±_ X.1 Y.1 Z.1)â©
  leftUnitor := fun X => â¨(Î»_ X.1).Hom, (Î»_ X.1).inv, hom_inv_id (Î»_ X.1), inv_hom_id (Î»_ X.1)â©
  rightUnitor := fun X => â¨(Ï_ X.1).Hom, (Ï_ X.1).inv, hom_inv_id (Ï_ X.1), inv_hom_id (Ï_ X.1)â©
  tensor_id' := fun X Y => tensor_id X.1 Y.1
  tensor_comp' := fun Xâ Yâ Zâ Xâ Yâ Zâ fâ fâ gâ gâ => tensor_comp fâ fâ gâ gâ
  associator_naturality' := fun Xâ Xâ Xâ Yâ Yâ Yâ fâ fâ fâ => associator_naturality fâ fâ fâ
  left_unitor_naturality' := fun X Y f => left_unitor_naturality f
  right_unitor_naturality' := fun X Y f => right_unitor_naturality f
  pentagon' := fun W X Y Z => pentagon W.1 X.1 Y.1 Z.1
  triangle' := fun X Y => triangle X.1 Y.1

/-- The forgetful monoidal functor from a full monoidal subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def fullMonoidalSubcategoryInclusion : MonoidalFunctor { X : C // P X } C where
  toFunctor := fullSubcategoryInclusion P
  Îµ := ð _
  Î¼ := fun X Y => ð _

instance fullMonoidalSubcategory.full : Full (fullMonoidalSubcategoryInclusion P).toFunctor :=
  fullSubcategory.full P

instance fullMonoidalSubcategory.faithful : Faithful (fullMonoidalSubcategoryInclusion P).toFunctor :=
  fullSubcategory.faithful P

variable {P} {P' : C â Prop} [MonoidalPredicate P']

/-- An implication of predicates `P â P'` induces a monoidal functor between full monoidal
subcategories. -/
@[simps]
def fullMonoidalSubcategory.map (h : â â¦Xâ¦, P X â P' X) : MonoidalFunctor { X : C // P X } { X : C // P' X } where
  toFunctor := fullSubcategory.map h
  Îµ := ð _
  Î¼ := fun X Y => ð _

instance fullMonoidalSubcategory.mapFull (h : â â¦Xâ¦, P X â P' X) :
    Full (fullMonoidalSubcategory.map h).toFunctor where preimage := fun X Y f => f

instance fullMonoidalSubcategory.map_faithful (h : â â¦Xâ¦, P X â P' X) :
    Faithful (fullMonoidalSubcategory.map h).toFunctor where

section Braided

variable (P) [BraidedCategory C]

/-- The braided structure on `{X : C // P X}` inherited by the braided structure on `C`.
-/
instance fullBraidedSubcategory : BraidedCategory { X : C // P X } :=
  braidedCategoryOfFaithful (fullMonoidalSubcategoryInclusion P)
    (fun X Y => â¨(Î²_ X.1 Y.1).Hom, (Î²_ X.1 Y.1).inv, (Î²_ X.1 Y.1).hom_inv_id, (Î²_ X.1 Y.1).inv_hom_idâ©) fun X Y => by
    tidy

/-- The forgetful braided functor from a full braided subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def fullBraidedSubcategoryInclusion : BraidedFunctor { X : C // P X } C where
  toMonoidalFunctor := fullMonoidalSubcategoryInclusion P
  braided' := fun X Y => by
    rw [is_iso.eq_inv_comp]
    tidy

instance fullBraidedSubcategory.full : Full (fullBraidedSubcategoryInclusion P).toFunctor :=
  fullMonoidalSubcategory.full P

instance fullBraidedSubcategory.faithful : Faithful (fullBraidedSubcategoryInclusion P).toFunctor :=
  fullMonoidalSubcategory.faithful P

variable {P}

/-- An implication of predicates `P â P'` induces a braided functor between full braided
subcategories. -/
@[simps]
def fullBraidedSubcategory.map (h : â â¦Xâ¦, P X â P' X) : BraidedFunctor { X : C // P X } { X : C // P' X } where
  toMonoidalFunctor := fullMonoidalSubcategory.map h
  braided' := fun X Y => by
    rw [is_iso.eq_inv_comp]
    tidy

instance fullBraidedSubcategory.mapFull (h : â â¦Xâ¦, P X â P' X) : Full (fullBraidedSubcategory.map h).toFunctor :=
  fullMonoidalSubcategory.mapFull h

instance fullBraidedSubcategory.map_faithful (h : â â¦Xâ¦, P X â P' X) :
    Faithful (fullBraidedSubcategory.map h).toFunctor :=
  fullMonoidalSubcategory.map_faithful h

end Braided

section Symmetric

variable (P) [SymmetricCategory C]

instance fullSymmetricSubcategory : SymmetricCategory { X : C // P X } :=
  symmetricCategoryOfFaithful (fullBraidedSubcategoryInclusion P)

end Symmetric

end MonoidalCategory

end CategoryTheory

