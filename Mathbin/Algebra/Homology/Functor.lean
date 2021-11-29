import Mathbin.Algebra.Homology.HomologicalComplex

/-!
# Complexes in functor categories

We can view a complex valued in a functor category `T ⥤ V` as
a functor from `T` to complexes valued in `V`.

## Future work
In fact this is an equivalence of categories.

-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type u} [category.{v} V] [has_zero_morphisms V]

variable {ι : Type _} {c : ComplexShape ι}

-- error in Algebra.Homology.Functor: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A complex of functors gives a functor to complexes. -/
@[simps #[ident obj, ident map]]
def as_functor
{T : Type*}
[category T]
(C : homological_complex «expr ⥤ »(T, V) c) : «expr ⥤ »(T, homological_complex V c) :=
{ obj := λ
  t, { X := λ i, (C.X i).obj t,
    d := λ i j, (C.d i j).app t,
    d_comp_d' := λ i j k hij hjk, begin
      have [] [] [":=", expr C.d_comp_d i j k],
      rw ["[", expr nat_trans.ext_iff, ",", expr function.funext_iff, "]"] ["at", ident this],
      exact [expr this t]
    end,
    shape' := λ i j h, begin
      have [] [] [":=", expr C.shape _ _ h],
      rw ["[", expr nat_trans.ext_iff, ",", expr function.funext_iff, "]"] ["at", ident this],
      exact [expr this t]
    end },
  map := λ t₁ t₂ h, { f := λ i, (C.X i).map h, comm' := λ i j hij, nat_trans.naturality _ _ },
  map_id' := λ t, by { ext [] [ident i] [],
    dsimp [] [] [] [],
    rw [expr (C.X i).map_id] [] },
  map_comp' := λ t₁ t₂ t₃ h₁ h₂, by { ext [] [ident i] [],
    dsimp [] [] [] [],
    rw [expr functor.map_comp] [] } }

/-- The functorial version of `homological_complex.as_functor`. -/
@[simps]
def complex_of_functors_to_functor_to_complex {T : Type _} [category T] :
  HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c :=
  { obj := fun C => C.as_functor,
    map :=
      fun C D f =>
        { app := fun t => { f := fun i => (f.f i).app t, comm' := fun i j w => nat_trans.congr_app (f.comm i j) t },
          naturality' :=
            fun t t' g =>
              by 
                ext i 
                exact (f.f i).naturality g } }

end HomologicalComplex

