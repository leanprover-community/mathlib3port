import Mathbin.CategoryTheory.Adjunction.Basic 
import Mathbin.CategoryTheory.Punit 
import Mathbin.CategoryTheory.StructuredArrow

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`structured_arrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunction_of_structured_arrow_initials` gives the left adjoint assuming the
appropriate initial objects exist, and `mk_initial_of_left_adjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/


universe v u₁ u₂

noncomputable theory

namespace CategoryTheory

open Limits

variable{C : Type u₁}{D : Type u₂}[category.{v} C][category.{v} D](G : D ⥤ C)

section OfInitials

variable[∀ A, has_initial (structured_arrow A G)]

-- error in CategoryTheory.Adjunction.Comma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps #[]]
def left_adjoint_of_structured_arrow_initials_aux
(A : C)
(B : D) : «expr ≃ »(«expr ⟶ »(«expr⊥_ »(structured_arrow A G).right, B), «expr ⟶ »(A, G.obj B)) :=
{ to_fun := λ g, «expr ≫ »(«expr⊥_ »(structured_arrow A G).hom, G.map g),
  inv_fun := λ f, comma_morphism.right (initial.to (structured_arrow.mk f)),
  left_inv := λ g, begin
    let [ident B'] [":", expr structured_arrow A G] [":=", expr structured_arrow.mk «expr ≫ »(«expr⊥_ »(structured_arrow A G).hom, G.map g)],
    let [ident g'] [":", expr «expr ⟶ »(«expr⊥_ »(structured_arrow A G), B')] [":=", expr structured_arrow.hom_mk g rfl],
    have [] [":", expr «expr = »(initial.to _, g')] [],
    { apply [expr colimit.hom_ext],
      rintro ["⟨", "⟩"] },
    change [expr «expr = »(comma_morphism.right (initial.to B'), _)] [] [],
    rw [expr this] [],
    refl
  end,
  right_inv := λ f, begin
    let [ident B'] [":", expr structured_arrow A G] [":=", expr { right := B, hom := f }],
    apply [expr (comma_morphism.w (initial.to B')).symm.trans (category.id_comp _)]
  end }

/--
If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunction_of_structured_arrow_initials`.
-/
def left_adjoint_of_structured_arrow_initials : C ⥤ D :=
  adjunction.left_adjoint_of_equiv (left_adjoint_of_structured_arrow_initials_aux G)
    fun _ _ =>
      by 
        simp 

/--
If each structured arrow category on `G` has an initial object, we have a constructed left adjoint
to `G`.
-/
def adjunction_of_structured_arrow_initials : left_adjoint_of_structured_arrow_initials G ⊣ G :=
  adjunction.adjunction_of_equiv_left _ _

/-- If each structured arrow category on `G` has an initial object, `G` is a right adjoint. -/
def is_right_adjoint_of_structured_arrow_initials : is_right_adjoint G :=
  { left := _, adj := adjunction_of_structured_arrow_initials G }

end OfInitials

section OfTerminals

variable[∀ A, has_terminal (costructured_arrow G A)]

-- error in CategoryTheory.Adjunction.Comma: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps #[]]
def right_adjoint_of_costructured_arrow_terminals_aux
(B : D)
(A : C) : «expr ≃ »(«expr ⟶ »(G.obj B, A), «expr ⟶ »(B, «expr⊤_ »(costructured_arrow G A).left)) :=
{ to_fun := λ g, comma_morphism.left (terminal.from (costructured_arrow.mk g)),
  inv_fun := λ g, «expr ≫ »(G.map g, «expr⊤_ »(costructured_arrow G A).hom),
  left_inv := by tidy [],
  right_inv := λ g, begin
    let [ident B'] [":", expr costructured_arrow G A] [":=", expr costructured_arrow.mk «expr ≫ »(G.map g, «expr⊤_ »(costructured_arrow G A).hom)],
    let [ident g'] [":", expr «expr ⟶ »(B', «expr⊤_ »(costructured_arrow G A))] [":=", expr costructured_arrow.hom_mk g rfl],
    have [] [":", expr «expr = »(terminal.from _, g')] [],
    { apply [expr limit.hom_ext],
      rintro ["⟨", "⟩"] },
    change [expr «expr = »(comma_morphism.left (terminal.from B'), _)] [] [],
    rw [expr this] [],
    refl
  end }

/--
If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunction_of_structured_arrow_initials`.
-/
def right_adjoint_of_costructured_arrow_terminals : C ⥤ D :=
  adjunction.right_adjoint_of_equiv (right_adjoint_of_costructured_arrow_terminals_aux G)
    fun B₁ B₂ A f g =>
      by 
        rw [←Equiv.eq_symm_apply]
        simp 

/--
If each costructured arrow category on `G` has a terminal object, we have a constructed right
adjoint to `G`.
-/
def adjunction_of_costructured_arrow_terminals : G ⊣ right_adjoint_of_costructured_arrow_terminals G :=
  adjunction.adjunction_of_equiv_right _ _

/-- If each costructured arrow category on `G` has an terminal object, `G` is a left adjoint. -/
def is_right_adjoint_of_costructured_arrow_terminals : is_left_adjoint G :=
  { right := right_adjoint_of_costructured_arrow_terminals G, adj := adjunction.adjunction_of_equiv_right _ _ }

end OfTerminals

section 

variable{F : C ⥤ D}

/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
def mk_initial_of_left_adjoint (h : F ⊣ G) (A : C) :
  is_initial (structured_arrow.mk (h.unit.app A) : structured_arrow A G) :=
  { desc :=
      fun B =>
        structured_arrow.hom_mk ((h.hom_equiv _ _).symm B.X.hom)
          (by 
            tidy),
    uniq' :=
      fun s m w =>
        by 
          ext 
          dsimp 
          rw [Equiv.eq_symm_apply, adjunction.hom_equiv_unit]
          apply structured_arrow.w m }

/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
def mk_terminal_of_right_adjoint (h : F ⊣ G) (A : D) :
  is_terminal (costructured_arrow.mk (h.counit.app A) : costructured_arrow F A) :=
  { lift :=
      fun B =>
        costructured_arrow.hom_mk (h.hom_equiv _ _ B.X.hom)
          (by 
            tidy),
    uniq' :=
      fun s m w =>
        by 
          ext 
          dsimp 
          rw [h.eq_hom_equiv_apply, adjunction.hom_equiv_counit]
          exact costructured_arrow.w m }

end 

end CategoryTheory

