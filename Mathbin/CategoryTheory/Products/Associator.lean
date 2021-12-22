import Mathbin.CategoryTheory.Products.Basic

/-!
The associator functor `((C × D) × E) ⥤ (C × (D × E))` and its inverse form an equivalence.
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

namespace CategoryTheory.prod

variable (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] (E : Type u₃) [category.{v₃} E]

/-- 
The associator functor `(C × D) × E ⥤ C × (D × E)`.
-/
@[simps]
def associator : (C × D) × E ⥤ C × D × E :=
  { obj := fun X => (X.1.1, (X.1.2, X.2)), map := fun _ _ f => (f.1.1, (f.1.2, f.2)) }

/-- 
The inverse associator functor `C × (D × E) ⥤ (C × D) × E `.
-/
@[simps]
def inverse_associator : C × D × E ⥤ (C × D) × E :=
  { obj := fun X => ((X.1, X.2.1), X.2.2), map := fun _ _ f => ((f.1, f.2.1), f.2.2) }

/-- 
The equivalence of categories expressing associativity of products of categories.
-/
def associativity : (C × D) × E ≌ C × D × E :=
  equivalence.mk (associator C D E) (inverse_associator C D E)
    (nat_iso.of_components
      (fun X =>
        eq_to_iso
          (by
            simp ))
      (by
        tidy))
    (nat_iso.of_components
      (fun X =>
        eq_to_iso
          (by
            simp ))
      (by
        tidy))

instance associator_is_equivalence : is_equivalence (associator C D E) :=
  (by
    infer_instance : is_equivalence (associativity C D E).Functor)

instance inverse_associator_is_equivalence : is_equivalence (inverse_associator C D E) :=
  (by
    infer_instance : is_equivalence (associativity C D E).inverse)

end CategoryTheory.prod

