import Mathbin.CategoryTheory.Limits.Shapes.WideEqualizers 
import Mathbin.CategoryTheory.Limits.Shapes.Products 
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Constructions related to weakly initial objects

This file gives constructions related to weakly initial objects, namely:
* If a category has small products and a small weakly initial set of objects, then it has a weakly
  initial object.
* If a category has wide equalizers and a weakly initial object, then it has an initial object.

These are primarily useful to show the General Adjoint Functor Theorem.
-/


universe v u

namespace CategoryTheory

open Limits

variable{C : Type u}[category.{v} C]

/--
If `C` has (small) products and a small weakly initial set of objects, then it has a weakly initial
object.
-/
theorem has_weakly_initial_of_weakly_initial_set_and_has_products [has_products C] {ι : Type v} {B : ι → C}
  (hB : ∀ A : C, ∃ i, Nonempty (B i ⟶ A)) : ∃ T : C, ∀ X, Nonempty (T ⟶ X) :=
  ⟨∏ B, fun X => ⟨pi.π _ _ ≫ (hB X).some_spec.some⟩⟩

-- error in CategoryTheory.Limits.Constructions.WeaklyInitial: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `C` has (small) wide equalizers and a weakly initial object, then it has an initial object.

The initial object is constructed as the wide equalizer of all endomorphisms on the given weakly
initial object.
-/
theorem has_initial_of_weakly_initial_and_has_wide_equalizers
[has_wide_equalizers C]
{T : C}
(hT : ∀ X, nonempty «expr ⟶ »(T, X)) : has_initial C :=
begin
  let [ident endos] [] [":=", expr «expr ⟶ »(T, T)],
  let [ident i] [] [":=", expr wide_equalizer.ι (id : endos → endos)],
  haveI [] [":", expr nonempty endos] [":=", expr ⟨«expr𝟙»() _⟩],
  have [] [":", expr ∀ X : C, unique «expr ⟶ »(wide_equalizer (id : endos → endos), X)] [],
  { intro [ident X],
    refine [expr ⟨⟨«expr ≫ »(i, classical.choice (hT X))⟩, λ a, _⟩],
    let [ident E] [] [":=", expr equalizer a «expr ≫ »(i, classical.choice (hT _))],
    let [ident e] [":", expr «expr ⟶ »(E, wide_equalizer id)] [":=", expr equalizer.ι _ _],
    let [ident h] [":", expr «expr ⟶ »(T, E)] [":=", expr classical.choice (hT E)],
    have [] [":", expr «expr = »(«expr ≫ »(«expr ≫ »(«expr ≫ »(i, h), e), i), «expr ≫ »(i, «expr𝟙»() _))] [],
    { rw ["[", expr category.assoc, ",", expr category.assoc, "]"] [],
      apply [expr wide_equalizer.condition (id : endos → endos) «expr ≫ »(h, «expr ≫ »(e, i))] },
    rw ["[", expr category.comp_id, ",", expr cancel_mono_id i, "]"] ["at", ident this],
    haveI [] [":", expr split_epi e] [":=", expr ⟨«expr ≫ »(i, h), this⟩],
    rw ["<-", expr cancel_epi e] [],
    apply [expr equalizer.condition] },
  exactI [expr has_initial_of_unique (wide_equalizer (id : endos → endos))]
end

end CategoryTheory

