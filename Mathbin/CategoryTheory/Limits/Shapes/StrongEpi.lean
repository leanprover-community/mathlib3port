import Mathbin.CategoryTheory.Arrow

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`, such
that for every commutative square with `f` at the top and a monomorphism at the bottom, there is
a diagonal morphism making the two triangles commute. This lift is necessarily unique (as shown in
`comma.lean`).

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

## Future work

There is also the dual notion of strong monomorphism.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/


universe v u

namespace CategoryTheory

variable{C : Type u}[category.{v} C]

variable{P Q : C}

/-- A strong epimorphism `f` is an epimorphism such that every commutative square with `f` at the
    top and a monomorphism at the bottom has a lift. -/
class strong_epi(f : P ⟶ Q) : Prop where 
  Epi : epi f 
  HasLift :
  ∀ {X Y : C} {u : P ⟶ X} {v : Q ⟶ Y} {z : X ⟶ Y} [mono z] (h : u ≫ z = f ≫ v), arrow.has_lift$ arrow.hom_mk' h

attribute [instance] strong_epi.has_lift

instance (priority := 100)epi_of_strong_epi (f : P ⟶ Q) [strong_epi f] : epi f :=
  strong_epi.epi

section 

variable{R : C}(f : P ⟶ Q)(g : Q ⟶ R)

-- error in CategoryTheory.Limits.Shapes.StrongEpi: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The composition of two strong epimorphisms is a strong epimorphism. -/
theorem strong_epi_comp [strong_epi f] [strong_epi g] : strong_epi «expr ≫ »(f, g) :=
{ epi := epi_comp _ _,
  has_lift := begin
    introsI [],
    have [ident h₀] [":", expr «expr = »(«expr ≫ »(u, z), «expr ≫ »(f, «expr ≫ »(g, v)))] [],
    by simpa [] [] [] ["[", expr category.assoc, "]"] [] ["using", expr h],
    let [ident w] [":", expr «expr ⟶ »(Q, X)] [":=", expr arrow.lift (arrow.hom_mk' h₀)],
    have [ident h₁] [":", expr «expr = »(«expr ≫ »(w, z), «expr ≫ »(g, v))] [],
    by rw [expr arrow.lift_mk'_right] [],
    exact [expr arrow.has_lift.mk ⟨(arrow.lift (arrow.hom_mk' h₁) : «expr ⟶ »(R, X)), by simp [] [] [] [] [] [], by simp [] [] [] [] [] []⟩]
  end }

-- error in CategoryTheory.Limits.Shapes.StrongEpi: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f ≫ g` is a strong epimorphism, then so is g. -/
theorem strong_epi_of_strong_epi [strong_epi «expr ≫ »(f, g)] : strong_epi g :=
{ epi := epi_of_epi f g,
  has_lift := begin
    introsI [],
    have [ident h₀] [":", expr «expr = »(«expr ≫ »(«expr ≫ »(f, u), z), «expr ≫ »(«expr ≫ »(f, g), v))] [],
    by simp [] [] ["only"] ["[", expr category.assoc, ",", expr h, "]"] [] [],
    exact [expr arrow.has_lift.mk ⟨(arrow.lift (arrow.hom_mk' h₀) : «expr ⟶ »(R, X)), (cancel_mono z).1 (by simp [] [] [] ["[", expr h, "]"] [] []), by simp [] [] [] [] [] []⟩]
  end }

/-- An isomorphism is in particular a strong epimorphism. -/
instance (priority := 100)strong_epi_of_is_iso [is_iso f] : strong_epi f :=
  { Epi :=
      by 
        infer_instance,
    HasLift :=
      fun X Y u v z _ h =>
        arrow.has_lift.mk
          ⟨inv f ≫ u,
            by 
              simp ,
            by 
              simp [h]⟩ }

end 

/-- A strong epimorphism that is a monomorphism is an isomorphism. -/
theorem is_iso_of_mono_of_strong_epi (f : P ⟶ Q) [mono f] [strong_epi f] : is_iso f :=
  ⟨⟨arrow.lift$
        arrow.hom_mk'$
          show 𝟙 P ≫ f = f ≫ 𝟙 Q by 
            simp ,
      by 
        tidy⟩⟩

end CategoryTheory

