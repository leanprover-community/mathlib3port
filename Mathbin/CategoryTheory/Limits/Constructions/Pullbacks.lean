import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks

/-!
# Constructing pullbacks from binary products and equalizers

If a category as binary products and equalizers, then it has pullbacks.
Also, if a category has binary coproducts and coequalizers, then it has pushouts
-/


universe v u

open CategoryTheory

namespace CategoryTheory.Limits

/--  If the product `X ⨯ Y` and the equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
    pullback of `f` and `g` exists: It is given by composing the equalizer with the projections. -/
theorem has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair {C : Type u} [𝒞 : category.{v} C] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [has_limit (pair X Y)] [has_limit (parallel_pair (Prod.fst ≫ f) (Prod.snd ≫ g))] :
    has_limit (cospan f g) :=
  let π₁ : X ⨯ Y ⟶ X := Prod.fst
  let π₂ : X ⨯ Y ⟶ Y := Prod.snd
  let e := equalizer.ι (π₁ ≫ f) (π₂ ≫ g)
  has_limit.mk
    { Cone :=
        pullback_cone.mk (e ≫ π₁) (e ≫ π₂) $ by
          simp only [category.assoc, equalizer.condition],
      IsLimit :=
        pullback_cone.is_limit.mk _
            (fun s =>
              equalizer.lift (prod.lift (s.π.app walking_cospan.left) (s.π.app walking_cospan.right)) $ by
                rw [← category.assoc, limit.lift_π, ← category.assoc, limit.lift_π] <;> exact pullback_cone.condition _)
            (by
              simp )
            (by
              simp ) $
          fun s m h₁ h₂ => by
          ext
          ·
            simpa using h₁
          ·
            simpa using h₂ }

section

attribute [local instance] has_limit_cospan_of_has_limit_pair_of_has_limit_parallel_pair

/--  If a category has all binary products and all equalizers, then it also has all pullbacks.
    As usual, this is not an instance, since there may be a more direct way to construct
    pullbacks. -/
theorem has_pullbacks_of_has_binary_products_of_has_equalizers (C : Type u) [𝒞 : category.{v} C] [has_binary_products C]
    [has_equalizers C] : has_pullbacks C :=
  { HasLimit := fun F => has_limit_of_iso (diagram_iso_cospan F).symm }

end

/--  If the coproduct `Y ⨿ Z` and the coequalizer of `f ≫ ι₁` and `g ≫ ι₂` exist, then the
    pushout of `f` and `g` exists: It is given by composing the inclusions with the coequalizer. -/
theorem has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair {C : Type u} [𝒞 : category.{v} C] {X Y Z : C}
    (f : X ⟶ Y) (g : X ⟶ Z) [has_colimit (pair Y Z)] [has_colimit (parallel_pair (f ≫ coprod.inl) (g ≫ coprod.inr))] :
    has_colimit (span f g) :=
  let ι₁ : Y ⟶ Y ⨿ Z := coprod.inl
  let ι₂ : Z ⟶ Y ⨿ Z := coprod.inr
  let c := coequalizer.π (f ≫ ι₁) (g ≫ ι₂)
  has_colimit.mk
    { Cocone :=
        pushout_cocone.mk (ι₁ ≫ c) (ι₂ ≫ c) $ by
          rw [← category.assoc, ← category.assoc, coequalizer.condition],
      IsColimit :=
        pushout_cocone.is_colimit.mk _
            (fun s =>
              coequalizer.desc (coprod.desc (s.ι.app walking_span.left) (s.ι.app walking_span.right)) $ by
                rw [category.assoc, colimit.ι_desc, category.assoc, colimit.ι_desc] <;>
                  exact pushout_cocone.condition _)
            (by
              simp )
            (by
              simp ) $
          fun s m h₁ h₂ => by
          ext
          ·
            simpa using h₁
          ·
            simpa using h₂ }

section

attribute [local instance] has_colimit_span_of_has_colimit_pair_of_has_colimit_parallel_pair

/--  If a category has all binary coproducts and all coequalizers, then it also has all pushouts.
    As usual, this is not an instance, since there may be a more direct way to construct
    pushouts. -/
theorem has_pushouts_of_has_binary_coproducts_of_has_coequalizers (C : Type u) [𝒞 : category.{v} C]
    [has_binary_coproducts C] [has_coequalizers C] : has_pushouts C :=
  has_pushouts_of_has_colimit_span C

end

end CategoryTheory.Limits

