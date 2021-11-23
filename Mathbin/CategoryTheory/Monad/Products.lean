import Mathbin.CategoryTheory.Over 
import Mathbin.CategoryTheory.Monad.Algebra 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of comonads is equivalent to the
over category of `X`.

## TODO

Show that `over.forget X : over X ⥤ C` is a comonadic left adjoint and `under.forget : under X ⥤ C`
is a monadic right adjoint.
-/


noncomputable theory

universe v u

namespace CategoryTheory

open Category Limits

variable{C : Type u}[category.{v} C](X : C)

section 

open Comonad

variable[has_binary_products C]

/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
@[simps]
def prod_comonad : comonad C :=
  { toFunctor := prod.functor.obj X, ε' := { app := fun Y => limits.prod.snd },
    δ' := { app := fun Y => prod.lift limits.prod.fst (𝟙 _) } }

/--
The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def coalgebra_to_over : coalgebra (prod_comonad X) ⥤ over X :=
  { obj := fun A => over.mk (A.a ≫ limits.prod.fst),
    map :=
      fun A₁ A₂ f =>
        over.hom_mk f.f
          (by 
            rw [over.mk_hom, ←f.h_assoc]
            dsimp 
            simp ) }

/--
The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def over_to_coalgebra : over X ⥤ coalgebra (prod_comonad X) :=
  { obj := fun f => { A := f.left, a := prod.lift f.hom (𝟙 _) }, map := fun f₁ f₂ g => { f := g.left } }

/-- The equivalence from coalgebras for the product comonad to the over category. -/
@[simps]
def coalgebra_equiv_over : coalgebra (prod_comonad X) ≌ over X :=
  { Functor := coalgebra_to_over X, inverse := over_to_coalgebra X,
    unitIso :=
      nat_iso.of_components
        (fun A =>
          coalgebra.iso_mk (iso.refl _)
            (prod.hom_ext
              (by 
                dsimp 
                simp )
              (by 
                dsimp 
                simpa using A.counit)))
        fun A₁ A₂ f =>
          by 
            ext 
            simp ,
    counitIso :=
      nat_iso.of_components (fun f => over.iso_mk (iso.refl _))
        fun f g k =>
          by 
            tidy }

end 

section 

open _Root_.Monad

variable[has_binary_coproducts C]

/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simps]
def coprod_monad : Monadₓ C :=
  { toFunctor := coprod.functor.obj X, η' := { app := fun Y => coprod.inr },
    μ' := { app := fun Y => coprod.desc coprod.inl (𝟙 _) } }

/--
The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def algebra_to_under : monad.algebra (coprod_monad X) ⥤ under X :=
  { obj := fun A => under.mk (coprod.inl ≫ A.a),
    map :=
      fun A₁ A₂ f =>
        under.hom_mk f.f
          (by 
            rw [under.mk_hom, assoc, ←f.h]
            dsimp 
            simp ) }

/--
The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def under_to_algebra : under X ⥤ monad.algebra (coprod_monad X) :=
  { obj := fun f => { A := f.right, a := coprod.desc f.hom (𝟙 _) }, map := fun f₁ f₂ g => { f := g.right } }

/--
The equivalence from algebras for the coproduct monad to the under category.
-/
@[simps]
def algebra_equiv_under : monad.algebra (coprod_monad X) ≌ under X :=
  { Functor := algebra_to_under X, inverse := under_to_algebra X,
    unitIso :=
      nat_iso.of_components
        (fun A =>
          monad.algebra.iso_mk (iso.refl _)
            (coprod.hom_ext
              (by 
                tidy)
              (by 
                dsimp 
                simpa using A.unit.symm)))
        fun A₁ A₂ f =>
          by 
            ext 
            simp ,
    counitIso :=
      nat_iso.of_components
        (fun f =>
          under.iso_mk (iso.refl _)
            (by 
              tidy))
        fun f g k =>
          by 
            tidy }

end 

end CategoryTheory

