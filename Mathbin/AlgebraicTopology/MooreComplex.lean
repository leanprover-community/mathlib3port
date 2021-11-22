import Mathbin.AlgebraicTopology.SimplicialObject 
import Mathbin.CategoryTheory.Abelian.Basic 
import Mathbin.CategoryTheory.Subobject.Default 
import Mathbin.Algebra.Homology.HomologicalComplex

/-!
## Moore complex

We construct the normalized Moore complex, as a functor
`simplicial_object C ⥤ chain_complex C ℕ`,
for any abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.

This functor is one direction of the Dold-Kan equivalence, which we're still working towards.

### References

* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex
-/


universe v u

noncomputable theory

open CategoryTheory CategoryTheory.Limits

open Opposite

namespace AlgebraicTopology

variable{C : Type _}[category C][abelian C]

attribute [local instance] abelian.has_pullbacks

/-! The definitions in this namespace are all auxiliary definitions for `normalized_Moore_complex`
and should usually only be accessed via that. -/


namespace NormalizedMooreComplex

open CategoryTheory.Subobject

variable(X : simplicial_object C)

/--
The normalized Moore complex in degree `n`, as a subobject of `X n`.
-/
@[simp]
def obj_X : ∀ n : ℕ, subobject (X.obj (op (SimplexCategory.mk n)))
| 0 => ⊤
| n+1 => Finset.univ.inf fun k : Finₓ (n+1) => kernel_subobject (X.δ k.succ)

/--
The differentials in the normalized Moore complex.
-/
@[simp]
def obj_d : ∀ n : ℕ, (obj_X X (n+1) : C) ⟶ (obj_X X n : C)
| 0 => subobject.arrow _ ≫ X.δ (0 : Finₓ 2) ≫ inv (⊤ : subobject _).arrow
| n+1 =>
  by 
    refine' factor_thru _ (arrow _ ≫ X.δ (0 : Finₓ (n+3))) _ 
    refine' (finset_inf_factors _).mpr fun i m => _ 
    apply kernel_subobject_factors 
    dsimp [obj_X]
    erw [category.assoc, ←X.δ_comp_δ (Finₓ.zero_le i.succ), ←category.assoc]
    convert zero_comp 
    rw
      [←factor_thru_arrow _ _
        (finset_inf_arrow_factors Finset.univ _ i.succ
          (by 
            simp ))]
    rw [category.assoc]
    convert comp_zero 
    exact kernel_subobject_arrow_comp _

theorem d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
  by 
    cases n <;> dsimp
    ·
      simp only [subobject.factor_thru_arrow_assoc]
      sliceLHS 2 3 => erw [←X.δ_comp_δ (Finₓ.zero_le 0)]
      rw
        [←factor_thru_arrow _ _
          (finset_inf_arrow_factors Finset.univ _ (0 : Finₓ 2)
            (by 
              simp ))]
      sliceLHS 2 3 => rw [kernel_subobject_arrow_comp]
      simp 
    ·
      simp [factor_thru_right]
      sliceLHS 2 3 => erw [←X.δ_comp_δ (Finₓ.zero_le 0)]
      rw
        [←factor_thru_arrow _ _
          (finset_inf_arrow_factors Finset.univ _ (0 : Finₓ (n+3))
            (by 
              simp ))]
      sliceLHS 2 3 => rw [kernel_subobject_arrow_comp]
      simp 

/--
The normalized Moore complex functor, on objects.
-/
@[simps]
def obj (X : simplicial_object C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n => (obj_X X n : C)) (obj_d X) (d_squared X)

variable{X}{Y : simplicial_object C}(f : X ⟶ Y)

/--
The normalized Moore complex functor, on morphisms.
-/
@[simps]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n =>
      by 
        refine' factor_thru _ (arrow _ ≫ f.app (op (SimplexCategory.mk n))) _ 
        cases n <;> dsimp
        ·
          apply top_factors
        ·
          refine' (finset_inf_factors _).mpr fun i m => _ 
          apply kernel_subobject_factors 
          sliceLHS 2 3 => erw [←f.naturality]
          rw
            [←factor_thru_arrow _ _
              (finset_inf_arrow_factors Finset.univ _ i
                (by 
                  simp ))]
          sliceLHS 2 3 => erw [kernel_subobject_arrow_comp]
          simp )
    fun n =>
      by 
        cases n <;> dsimp
        ·
          ext 
          simp 
          erw [f.naturality]
          rfl
        ·
          ext 
          simp 
          erw [f.naturality]
          rfl

end NormalizedMooreComplex

open NormalizedMooreComplex

variable(C)

/--
The (normalized) Moore complex of a simplicial object `X` in an abelian category `C`.

The `n`-th object is intersection of
the kernels of `X.δ i : X.obj n ⟶ X.obj (n-1)`, for `i = 1, ..., n`.

The differentials are induced from `X.δ 0`,
which maps each of these intersections of kernels to the next.
-/
@[simps]
def normalized_Moore_complex : simplicial_object C ⥤ ChainComplex C ℕ :=
  { obj := obj, map := fun X Y f => map f,
    map_id' :=
      fun X =>
        by 
          ext n 
          cases n <;>
            ·
              dsimp 
              simp ,
    map_comp' :=
      fun X Y Z f g =>
        by 
          ext n 
          cases n <;> simp  }

end AlgebraicTopology

