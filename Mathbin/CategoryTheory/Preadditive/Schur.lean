/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import Mathbin.Algebra.Group.Ext
import Mathbin.CategoryTheory.Simple
import Mathbin.CategoryTheory.Linear.Default
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.Algebra.Algebra.Spectrum

/-!
# Schur's lemma
We first prove the part of Schur's Lemma that holds in any preadditive category with kernels,
that any nonzero morphism between simple objects
is an isomorphism.

Second, we prove Schur's lemma for `ð`-linear categories with finite dimensional hom spaces,
over an algebraically closed field `ð`:
the hom space `X â¶ Y` between simple objects `X` and `Y` is at most one dimensional,
and is 1-dimensional iff `X` and `Y` are isomorphic.
-/


namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type _} [Category C]

variable [Preadditive C]

-- See also `epi_of_nonzero_to_simple`, which does not require `preadditive C`.
theorem mono_of_nonzero_from_simple [HasKernels C] {X Y : C} [Simple X] {f : X â¶ Y} (w : f â  0) : Mono f :=
  Preadditive.mono_of_kernel_zero (kernel_zero_of_nonzero_from_simple w)

/-- The part of **Schur's lemma** that holds in any preadditive category with kernels:
that a nonzero morphism between simple objects is an isomorphism.
-/
theorem is_iso_of_hom_simple [HasKernels C] {X Y : C} [Simple X] [Simple Y] {f : X â¶ Y} (w : f â  0) : IsIso f := by
  have := mono_of_nonzero_from_simple w
  exact is_iso_of_mono_of_nonzero w

/-- As a corollary of Schur's lemma for preadditive categories,
any morphism between simple objects is (exclusively) either an isomorphism or zero.
-/
theorem is_iso_iff_nonzero [HasKernels C] {X Y : C} [Simple X] [Simple Y] (f : X â¶ Y) : IsIso f â f â  0 :=
  â¨fun I => by
    intro h
    apply id_nonzero X
    simp only [is_iso.hom_inv_id f, â h, â zero_comp], fun w => is_iso_of_hom_simple wâ©

/-- In any preadditive category with kernels,
the endomorphisms of a simple object form a division ring.
-/
noncomputable instance [HasKernels C] {X : C} [Simple X] : DivisionRing (End X) := by
  classical <;>
    exact
      { (inferInstance : Ringâ (End X)) with
        inv := fun f =>
          if h : f = 0 then 0
          else by
            have := is_iso_of_hom_simple h
            exact inv f,
        exists_pair_ne := â¨ð X, 0, id_nonzero _â©, inv_zero := dif_pos rfl,
        mul_inv_cancel := fun f h => by
          have := is_iso_of_hom_simple h
          convert is_iso.inv_hom_id f
          exact dif_neg h }

open FiniteDimensional

section

variable (ð : Type _) [DivisionRing ð]

/-- Part of **Schur's lemma** for `ð`-linear categories:
the hom space between two non-isomorphic simple objects is 0-dimensional.
-/
theorem finrank_hom_simple_simple_eq_zero_of_not_iso [HasKernels C] [Linear ð C] {X Y : C} [Simple X] [Simple Y]
    (h : (X â Y) â False) : finrank ð (X â¶ Y) = 0 := by
  have :=
    subsingleton_of_forall_eq (0 : X â¶ Y) fun f => by
      have p := not_congr (is_iso_iff_nonzero f)
      simp only [â not_not, â Ne.def] at p
      refine' p.mp fun _ => h (as_iso f)
  exact finrank_zero_of_subsingleton

end

variable (ð : Type _) [Field ð]

variable [IsAlgClosed ð] [Linear ð C]

/-- An auxiliary lemma for Schur's lemma.

If `X â¶ X` is finite dimensional, and every nonzero endomorphism is invertible,
then `X â¶ X` is 1-dimensional.
-/
-- In the proof below we have some difficulty using `I : finite_dimensional ð (X â¶ X)`
-- where we need a `finite_dimensional ð (End X)`.
-- These are definitionally equal, but without eta reduction Lean can't see this.
-- To get around this, we use `convert I`,
-- then check the various instances agree field-by-field,
-- We prove this with the explicit `is_iso_iff_nonzero` assumption,
-- rather than just `[simple X]`, as this form is useful for
-- MÃ¼ger's formulation of semisimplicity.
theorem finrank_endomorphism_eq_one {X : C} (is_iso_iff_nonzero : â f : X â¶ X, IsIso f â f â  0)
    [I : FiniteDimensional ð (X â¶ X)] : finrank ð (X â¶ X) = 1 := by
  have id_nonzero :=
    (is_iso_iff_nonzero (ð X)).mp
      (by
        infer_instance)
  apply finrank_eq_one (ð X)
  Â· exact id_nonzero
    
  Â· intro f
    have : Nontrivial (End X) := nontrivial_of_ne _ _ id_nonzero
    obtain â¨c, nuâ© :=
      @Spectrum.nonempty_of_is_alg_closed_of_finite_dimensional ð (End X) _ _ _ _ _
        (by
          convert I
          ext
          rfl
          ext
          rfl)
        (End.of f)
    use c
    rw [Spectrum.mem_iff, IsUnit.sub_iff, is_unit_iff_is_iso, is_iso_iff_nonzero, Ne.def, not_not, sub_eq_zero,
      Algebra.algebra_map_eq_smul_one] at nu
    exact nu.symm
    

variable [HasKernels C]

/-- **Schur's lemma** for endomorphisms in `ð`-linear categories.
-/
theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] [I : FiniteDimensional ð (X â¶ X)] :
    finrank ð (X â¶ X) = 1 :=
  finrank_endomorphism_eq_one ð is_iso_iff_nonzero

theorem endomorphism_simple_eq_smul_id {X : C} [Simple X] [I : FiniteDimensional ð (X â¶ X)] (f : X â¶ X) :
    â c : ð, c â¢ ð X = f :=
  (finrank_eq_one_iff_of_nonzero' (ð X) (id_nonzero X)).mp (finrank_endomorphism_simple_eq_one ð X) f

/-- Endomorphisms of a simple object form a field if they are finite dimensional.
This can't be an instance as `ð` would be undetermined.
-/
noncomputable def fieldEndOfFiniteDimensional (X : C) [Simple X] [I : FiniteDimensional ð (X â¶ X)] : Field (End X) := by
  classical <;>
    exact
      { (inferInstance : DivisionRing (End X)) with
        mul_comm := fun f g => by
          obtain â¨c, rflâ© := endomorphism_simple_eq_smul_id ð f
          obtain â¨d, rflâ© := endomorphism_simple_eq_smul_id ð g
          simp [mul_smul, â mul_comm c d] }

/-- **Schur's lemma** for `ð`-linear categories:
if hom spaces are finite dimensional, then the hom space between simples is at most 1-dimensional.

See `finrank_hom_simple_simple_eq_one_iff` and `finrank_hom_simple_simple_eq_zero_iff` below
for the refinements when we know whether or not the simples are isomorphic.
-/
-- There is a symmetric argument that uses `[finite_dimensional ð (Y â¶ Y)]` instead,
-- but we don't bother proving that here.
theorem finrank_hom_simple_simple_le_one (X Y : C) [FiniteDimensional ð (X â¶ X)] [Simple X] [Simple Y] :
    finrank ð (X â¶ Y) â¤ 1 := by
  cases' subsingleton_or_nontrivial (X â¶ Y) with h
  Â· skip
    rw [finrank_zero_of_subsingleton]
    exact zero_le_one
    
  Â· obtain â¨f, nzâ© := (nontrivial_iff_exists_ne 0).mp h
    have fi := (is_iso_iff_nonzero f).mpr nz
    apply finrank_le_one f
    intro g
    obtain â¨c, wâ© := endomorphism_simple_eq_smul_id ð (g â« inv f)
    exact
      â¨c, by
        simpa using w =â« fâ©
    

theorem finrank_hom_simple_simple_eq_one_iff (X Y : C) [FiniteDimensional ð (X â¶ X)] [FiniteDimensional ð (X â¶ Y)]
    [Simple X] [Simple Y] : finrank ð (X â¶ Y) = 1 â Nonempty (X â Y) := by
  fconstructor
  Â· intro h
    rw [finrank_eq_one_iff'] at h
    obtain â¨f, nz, -â© := h
    rw [â is_iso_iff_nonzero] at nz
    exact â¨as_iso fâ©
    
  Â· rintro â¨fâ©
    have le_one := finrank_hom_simple_simple_le_one ð X Y
    have zero_lt : 0 < finrank ð (X â¶ Y) :=
      finrank_pos_iff_exists_ne_zero.mpr â¨f.hom, (is_iso_iff_nonzero f.hom).mp inferInstanceâ©
    linarith
    

theorem finrank_hom_simple_simple_eq_zero_iff (X Y : C) [FiniteDimensional ð (X â¶ X)] [FiniteDimensional ð (X â¶ Y)]
    [Simple X] [Simple Y] : finrank ð (X â¶ Y) = 0 â IsEmpty (X â Y) := by
  rw [â not_nonempty_iff, â not_congr (finrank_hom_simple_simple_eq_one_iff ð X Y)]
  refine'
    â¨fun h => by
      rw [h]
      simp , fun h => _â©
  have := finrank_hom_simple_simple_le_one ð X Y
  interval_cases finrank ð (X â¶ Y) with h'
  Â· exact h'
    
  Â· exact False.elim (h h')
    

end CategoryTheory

