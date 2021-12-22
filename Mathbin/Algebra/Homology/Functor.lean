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

/--  A complex of functors gives a functor to complexes. -/
@[simps obj map]
def as_functor {T : Type _} [category T] (C : HomologicalComplex (T ⥤ V) c) : T ⥤ HomologicalComplex V c :=
  { obj := fun t =>
      { x := fun i => (C.X i).obj t, d := fun i j => (C.d i j).app t,
        d_comp_d' := fun i j k hij hjk => by
          have := C.d_comp_d i j k
          rw [nat_trans.ext_iff, Function.funext_iffₓ] at this
          exact this t,
        shape' := fun i j h => by
          have := C.shape _ _ h
          rw [nat_trans.ext_iff, Function.funext_iffₓ] at this
          exact this t },
    map := fun t₁ t₂ h => { f := fun i => (C.X i).map h, comm' := fun i j hij => nat_trans.naturality _ _ },
    map_id' := fun t => by
      ext i
      dsimp
      rw [(C.X i).map_id],
    map_comp' := fun t₁ t₂ t₃ h₁ h₂ => by
      ext i
      dsimp
      rw [functor.map_comp] }

/--  The functorial version of `homological_complex.as_functor`. -/
@[simps]
def complex_of_functors_to_functor_to_complex {T : Type _} [category T] :
    HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c :=
  { obj := fun C => C.as_functor,
    map := fun C D f =>
      { app := fun t => { f := fun i => (f.f i).app t, comm' := fun i j w => nat_trans.congr_app (f.comm i j) t },
        naturality' := fun t t' g => by
          ext i
          exact (f.f i).naturality g } }

end HomologicalComplex

