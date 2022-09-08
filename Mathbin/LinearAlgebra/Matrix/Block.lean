/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.Tactic.FinCases

/-!
# Block matrices and their determinant

This file defines a predicate `matrix.block_triangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → α`

## Main results
  * `matrix.det_of_block_triangular`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `matrix.det_of_upper_triangular` and `matrix.det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/


open Finset Function OrderDual

open BigOperators Matrix

universe v

variable {α m n : Type _}

variable {R : Type v} [CommRingₓ R] {M : Matrix m m R} {b : m → α}

namespace Matrix

section LT

variable [LT α]

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then
`block_triangular M n b` says the matrix is block triangular. -/
def BlockTriangular (M : Matrix m m R) (b : m → α) : Prop :=
  ∀ ⦃i j⦄, b j < b i → M i j = 0

@[simp]
protected theorem BlockTriangular.submatrix {f : n → m} (h : M.BlockTriangular b) :
    (M.submatrix f f).BlockTriangular (b ∘ f) := fun i j hij => h hij

theorem block_triangular_reindex_iff {b : n → α} {e : m ≃ n} :
    (reindex e e M).BlockTriangular b ↔ M.BlockTriangular (b ∘ e) := by
  refine' ⟨fun h => _, fun h => _⟩
  · convert h.submatrix
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, Equivₓ.symm_comp_self]
    
  · convert h.submatrix
    simp only [comp.assoc b e e.symm, Equivₓ.self_comp_symm, comp.right_id]
    

protected theorem BlockTriangular.transpose : M.BlockTriangular b → Mᵀ.BlockTriangular (to_dual ∘ b) :=
  swap

@[simp]
protected theorem block_triangular_transpose_iff {b : m → αᵒᵈ} :
    Mᵀ.BlockTriangular b ↔ M.BlockTriangular (of_dual ∘ b) :=
  forall_swap

end LT

theorem upper_two_block_triangular [Preorderₓ α] (A : Matrix m m R) (B : Matrix m n R) (D : Matrix n n R) {a b : α}
    (hab : a < b) : BlockTriangular (fromBlocks A B 0 D) (Sum.elim (fun i => a) fun j => b) := by
  intro k1 k2 hk12
  have hor : ∀ k : Sum m n, Sum.elim (fun i => a) (fun j => b) k = a ∨ Sum.elim (fun i => a) (fun j => b) k = b := by
    simp
  have hne : a ≠ b := fun h => lt_irreflₓ _ (lt_of_lt_of_eqₓ hab h.symm)
  have ha : ∀ k : Sum m n, Sum.elim (fun i => a) (fun j => b) k = a → ∃ i, k = Sum.inl i := by
    simp [hne.symm]
  have hb : ∀ k : Sum m n, Sum.elim (fun i => a) (fun j => b) k = b → ∃ j, k = Sum.inr j := by
    simp [hne]
  cases' hor k1 with hk1 hk1 <;> cases' hor k2 with hk2 hk2 <;> rw [hk1, hk2] at hk12
  · exact False.elim (lt_irreflₓ a hk12)
    
  · exact False.elim (lt_irreflₓ _ (lt_transₓ hab hk12))
    
  · obtain ⟨i, hi⟩ := hb k1 hk1
    obtain ⟨j, hj⟩ := ha k2 hk2
    rw [hi, hj]
    simp
    
  · exact absurd hk12 (irrefl b)
    

/-! ### Determinant -/


variable [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q] (e : ∀ x, q x ↔ p x) :
    (toSquareBlockProp M p).det = (toSquareBlockProp M q).det := by
  convert Matrix.det_reindex_self (Equivₓ.subtypeEquivRight e) (to_square_block_prop M q)

@[simp]
theorem det_to_square_block_id (M : Matrix m m R) (i : m) : (M.toSquareBlock id i).det = M i i := by
  letI : Unique { a // id a = i } := ⟨⟨⟨i, rfl⟩⟩, fun j => Subtype.ext j.property⟩
  exact (det_unique _).trans rfl

theorem det_to_block (M : Matrix m m R) (p : m → Prop) [DecidablePred p] :
    M.det =
      (fromBlocks (toBlock M p p) ((toBlock M p) fun j => ¬p j) (toBlock M (fun j => ¬p j) p) <|
          (toBlock M fun j => ¬p j) fun j => ¬p j).det :=
  by
  rw [← Matrix.det_reindex_self (Equivₓ.sumCompl p).symm M]
  rw [det_apply', det_apply']
  congr
  ext σ
  congr
  ext
  generalize hy : σ x = y
  cases x <;>
    cases y <;>
      simp only [Matrix.reindex_apply, to_block_apply, Equivₓ.symm_symm, Equivₓ.sum_compl_apply_inr,
        Equivₓ.sum_compl_apply_inl, from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
        Matrix.submatrix_apply]

theorem two_block_triangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, ¬p i → ∀ j, p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [det_to_block M p]
  convert
    det_from_blocks_zero₂₁ (to_block M p p) (to_block M p fun j => ¬p j) (to_block M (fun j => ¬p j) fun j => ¬p j)
  ext
  exact h (↑i) i.2 (↑j) j.2

theorem two_block_triangular_det' (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
    (h : ∀ i, p i → ∀ j, ¬p j → M i j = 0) :
    M.det = (toSquareBlockProp M p).det * (toSquareBlockProp M fun i => ¬p i).det := by
  rw [M.two_block_triangular_det fun i => ¬p i, mul_comm]
  simp_rw [not_not]
  congr 1
  exact equiv_block_det _ fun _ => not_not.symm
  simpa only [not_not] using h

protected theorem BlockTriangular.det [DecidableEq α] [LinearOrderₓ α] (hM : BlockTriangular M b) :
    M.det = ∏ a in univ.Image b, (M.toSquareBlock b a).det := by
  induction' hs : univ.image b using Finset.strongInductionₓ with s ih generalizing m
  subst hs
  by_cases' h : univ.image b = ∅
  · haveI := univ_eq_empty_iff.1 (image_eq_empty.1 h)
    simp [h]
    
  · let k := (univ.image b).max' (nonempty_of_ne_empty h)
    rw [two_block_triangular_det' M fun i => b i = k]
    · have : univ.image b = insert k ((univ.image b).erase k) := by
        rw [insert_erase]
        apply max'_mem
      rw [this, prod_insert (not_mem_erase _ _)]
      refine' congr_argₓ _ _
      let b' := fun i : { a // b a ≠ k } => b ↑i
      have h' : block_triangular (M.to_square_block_prop fun i : m => b i ≠ k) b' := by
        intro i j
        apply hM
      have hb' : image b' univ = (image b univ).erase k := by
        apply subset_antisymm
        · rw [image_subset_iff]
          intro i _
          apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
          
        · intro i hi
          rw [mem_image]
          rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
          subst ha
          exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩
          
      rw [ih ((univ.image b).erase k) (erase_ssubset (max'_mem _ _)) h' hb']
      apply Finset.prod_congr rfl
      intro l hl
      let he : { a // b' a = l } ≃ { a // b a = l } := by
        have hc : ∀ i : m, (fun a => b a = l) i → (fun a => b a ≠ k) i := by
          intro i hbi
          rw [hbi]
          exact ne_of_mem_erase hl
        exact Equivₓ.subtypeSubtypeEquivSubtype hc
      simp only [to_square_block_def]
      rw [← Matrix.det_reindex_self he.symm fun i j : { a // b a = l } => M ↑i ↑j]
      refine' congr_argₓ _ _
      ext
      simp [to_square_block_def, to_square_block_prop_def]
      
    · intro i hi j hj
      apply hM
      rw [hi]
      apply lt_of_le_of_neₓ _ hj
      exact Finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _))
      
    

theorem BlockTriangular.det_fintype [DecidableEq α] [Fintype α] [LinearOrderₓ α] (h : BlockTriangular M b) :
    M.det = ∏ k : α, (M.toSquareBlock b k).det := by
  refine' h.det.trans ((prod_subset (subset_univ _)) fun a _ ha => _)
  have : IsEmpty { i // b i = a } := ⟨fun i => ha <| mem_image.2 ⟨i, mem_univ _, i.2⟩⟩
  exact det_is_empty

theorem det_of_upper_triangular [LinearOrderₓ m] (h : M.BlockTriangular id) : M.det = ∏ i : m, M i i := by
  haveI : DecidableEq R := Classical.decEq _
  simp_rw [h.det, image_id, det_to_square_block_id]

theorem det_of_lower_triangular [LinearOrderₓ m] (M : Matrix m m R) (h : M.BlockTriangular toDual) :
    M.det = ∏ i : m, M i i := by
  rw [← det_transpose]
  exact det_of_upper_triangular h.transpose

end Matrix

