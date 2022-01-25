import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.AlgebraicTopology.SimplicialObject
import Mathbin.AlgebraicTopology.MooreComplex
import Mathbin.CategoryTheory.Abelian.Basic
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Tactic.RingExp
import Mathbin.Data.Fintype.Card

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

We also construct the natural transformation
`inclusion_of_Moore_complex : normalized_Moore_complex A ⟶ alternating_face_map_complex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/


open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive

open Opposite

open_locale BigOperators

open_locale Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

/-!
## Construction of the alternating face map complex
-/


variable {C : Type _} [category C] [preadditive C]

variable (X : simplicial_object C)

variable (Y : simplicial_object C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
def obj_d (n : ℕ) : X _[n + 1] ⟶ X _[n] :=
  ∑ i : Finₓ (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i

/-- ## The chain complex relation `d ≫ d`
-/
theorem d_squared (n : ℕ) : obj_d X (n + 1) ≫ obj_d X n = 0 := by
  dsimp
  rw [comp_sum]
  let d_l := fun j : Finₓ (n + 3) => (-1 : ℤ) ^ (j : ℕ) • X.δ j
  let d_r := fun i : Finₓ (n + 2) => (-1 : ℤ) ^ (i : ℕ) • X.δ i
  rw
    [show (fun i => (∑ j : Finₓ (n + 3), d_l j) ≫ d_r i) = fun i => ∑ j : Finₓ (n + 3), d_l j ≫ d_r i by
      ext i
      rw [sum_comp]]
  rw [← Finset.sum_product']
  let P := Finₓ (n + 2) × Finₓ (n + 3)
  let S := finset.univ.filter fun ij : P => (ij.2 : ℕ) ≤ (ij.1 : ℕ)
  let term := fun ij : P => d_l ij.2 ≫ d_r ij.1
  erw
    [show (∑ ij : P, term ij) = (∑ ij in S, term ij) + ∑ ij in Sᶜ, term ij by
      rw [Finset.sum_add_sum_compl]]
  rw [← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Finₓ.castLt ij.2 (lt_of_le_of_ltₓ (finset.mem_filter.mp hij).right (Finₓ.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [Finset.mem_univ, Finset.compl_filter, Finset.mem_filter, true_andₓ, Finₓ.coe_succ, Finₓ.coe_cast_lt] at
      hij⊢
    linarith
    
  · rintro ⟨i, j⟩ hij
    simp only [term, d_l, d_r, φ, comp_zsmul, zsmul_comp, ← neg_smul, ← mul_smul, pow_addₓ, neg_mul_eq_neg_mul_symm,
      mul_oneₓ, Finₓ.coe_cast_lt, Finₓ.coe_succ, pow_oneₓ, mul_neg_eq_neg_mul_symm, neg_negₓ]
    let jj : Finₓ (n + 2) := (φ (i, j) hij).1
    have ineq : jj ≤ i := by
      rw [← Finₓ.coe_fin_le]
      simpa using hij
    rw [CategoryTheory.SimplicialObject.δ_comp_δ X ineq, Finₓ.cast_succ_cast_lt, mul_comm]
    
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hij hij' h
    rw [Prod.mk.inj_iffₓ]
    refine'
      ⟨by
        simpa using congr_argₓ Prod.snd h, _⟩
    have h1 := congr_argₓ Finₓ.castSucc (congr_argₓ Prod.fst h)
    simpa [Finₓ.cast_succ_cast_lt] using h1
    
  · rintro ⟨i', j'⟩ hij'
    simp only [true_andₓ, Finset.mem_univ, Finset.compl_filter, not_leₓ, Finset.mem_filter] at hij'
    refine' ⟨(j'.pred _, Finₓ.castSucc i'), _, _⟩
    · intro H
      simpa only [H, Nat.not_lt_zeroₓ, Finₓ.coe_zero] using hij'
      
    · simpa only [true_andₓ, Finset.mem_univ, Finₓ.coe_cast_succ, Finₓ.coe_pred, Finset.mem_filter] using
        Nat.le_pred_of_lt hij'
      
    · simp only [Prod.mk.inj_iffₓ, Finₓ.succ_pred, Finₓ.cast_lt_cast_succ]
      constructor <;> rfl
      
    

/-!
## Construction of the alternating face map complex functor
-/


/-- The alternating face map complex, on objects -/
def obj : ChainComplex C ℕ :=
  ChainComplex.of (fun n => X _[n]) (obj_d X) (d_squared X)

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => f.app (op [n])) fun n => by
    dsimp
    rw [comp_sum, sum_comp]
    apply Finset.sum_congr rfl fun x h => _
    rw [comp_zsmul, zsmul_comp]
    apply congr_argₓ
    erw [f.naturality]
    rfl

end AlternatingFaceMapComplex

variable (C : Type _) [category C] [preadditive C]

/-- The alternating face map complex, as a functor -/
@[simps]
def alternating_face_map_complex : simplicial_object C ⥤ ChainComplex C ℕ where
  obj := alternating_face_map_complex.obj
  map := fun X Y f => alternating_face_map_complex.map f

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/


variable {A : Type _} [category A] [abelian A]

/-- The inclusion map of the Moore complex in the alternating face map complex -/
def inclusion_of_Moore_complex_map (X : simplicial_object A) :
    (normalized_Moore_complex A).obj X ⟶ (alternating_face_map_complex A).obj X :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => (normalized_Moore_complex.obj_X X n).arrow) fun n => by
    simp only [alternating_face_map_complex.obj_d]
    rw [comp_sum]
    let t := fun j : Finₓ (n + 2) => (normalized_Moore_complex.obj_X X (n + 1)).arrow ≫ ((-1 : ℤ) ^ (j : ℕ) • X.δ j)
    have def_t :
      ∀ j : Finₓ (n + 2), t j = (normalized_Moore_complex.obj_X X (n + 1)).arrow ≫ ((-1 : ℤ) ^ (j : ℕ) • X.δ j) := by
      intro j
      rfl
    rw [Finₓ.sum_univ_succ t]
    have null : ∀ j : Finₓ (n + 1), t j.succ = 0 := by
      intro j
      rw [def_t, comp_zsmul, ← zsmul_zero ((-1 : ℤ) ^ (j.succ : ℕ))]
      apply congr_argₓ
      rw [normalized_Moore_complex.obj_X]
      rw [←
        factor_thru_arrow _ _
          (finset_inf_arrow_factors Finset.univ _ j
            (by
              simp only [Finset.mem_univ]))]
      slice_lhs 2 3 => erw [kernel_subobject_arrow_comp (X.δ j.succ)]
      simp only [comp_zero]
    rw [Fintype.sum_eq_zero _ null]
    simp only [add_zeroₓ]
    let eq := def_t 0
    rw
      [show (-1 : ℤ) ^ ((0 : Finₓ (n + 2)) : ℕ) = 1 by
        ring] at
      eq
    rw [one_smul] at eq
    rw [Eq]
    cases n <;> dsimp <;> simp

@[simp]
theorem inclusion_of_Moore_complex_map_f (X : simplicial_object A) (n : ℕ) :
    (inclusion_of_Moore_complex_map X).f n = (normalized_Moore_complex.obj_X X n).arrow :=
  ChainComplex.of_hom_f _ _ _ _ _ _ _ _ n

variable (A)

/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
def inclusion_of_Moore_complex : normalized_Moore_complex A ⟶ alternating_face_map_complex A where
  app := inclusion_of_Moore_complex_map

end AlgebraicTopology

