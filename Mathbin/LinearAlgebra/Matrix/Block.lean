import Mathbin.LinearAlgebra.Matrix.Determinant 
import Mathbin.Tactic.FinCases

/-!
# Block matrices and their determinant

This file defines a predicate `matrix.block_triangular_matrix` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular_matrix` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → ℕ`

## Main results
  * `det_of_block_triangular_matrix`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `det_of_upper_triangular` and `det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/


open_locale BigOperators

universe v

variable{m n : Type _}[DecidableEq n][Fintype n][DecidableEq m][Fintype m]

variable{R : Type v}[CommRingₓ R]

namespace Matrix

theorem det_to_block (M : Matrix m m R) (p : m → Prop) [DecidablePred p] :
  M.det =
    (Matrix.fromBlocks (to_block M p p) (to_block M p fun j => ¬p j) (to_block M (fun j => ¬p j) p)
        (to_block M (fun j => ¬p j) fun j => ¬p j)).det :=
  by 
    rw [←Matrix.det_reindex_self (Equiv.sumCompl p).symm M]
    rw [det_apply', det_apply']
    congr 
    ext σ 
    congr 
    ext 
    generalize hy : σ x = y 
    cases x <;>
      cases y <;>
        simp only [Matrix.reindex_apply, to_block_apply, Equiv.symm_symm, Equiv.sum_compl_apply_inr,
          Equiv.sum_compl_apply_inl, from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
          Matrix.minor_apply]

theorem det_to_square_block (M : Matrix m m R) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
  (to_square_block M b k).det = (to_square_block_prop M fun i => b i = k).det :=
  by 
    simp 

theorem det_to_square_block' (M : Matrix m m R) (b : m → ℕ) (k : ℕ) :
  (to_square_block' M b k).det = (to_square_block_prop M fun i => b i = k).det :=
  by 
    simp 

theorem two_block_triangular_det (M : Matrix m m R) (p : m → Prop) [DecidablePred p]
  (h : ∀ i h1 : ¬p i j h2 : p j, M i j = 0) :
  M.det = (to_square_block_prop M p).det*(to_square_block_prop M fun i => ¬p i).det :=
  by 
    rw [det_to_block M p]
    convert
      upper_two_block_triangular_det (to_block M p p) (to_block M p fun j => ¬p j)
        (to_block M (fun j => ¬p j) fun j => ¬p j)
    ext 
    exact h («expr↑ » i) i.2 («expr↑ » j) j.2

theorem equiv_block_det (M : Matrix m m R) {p q : m → Prop} [DecidablePred p] [DecidablePred q] (e : ∀ x, q x ↔ p x) :
  (to_square_block_prop M p).det = (to_square_block_prop M q).det :=
  by 
    convert Matrix.det_reindex_self (Equiv.subtypeEquivRight e) (to_square_block_prop M q)

theorem to_square_block_det'' (M : Matrix m m R) {n : Nat} (b : m → Finₓ n) (k : Finₓ n) :
  (to_square_block M b k).det = (to_square_block' M (fun i => «expr↑ » (b i)) («expr↑ » k)).det :=
  by 
    rw [to_square_block_def', to_square_block_def]
    apply equiv_block_det 
    intro x 
    apply (Finₓ.ext_iff _ _).symm

/-- Let `b` map rows and columns of a square matrix `M` to `n` blocks. Then
  `block_triangular_matrix' M n b` says the matrix is block triangular. -/
def block_triangular_matrix' {o : Type _} (M : Matrix o o R) {n : ℕ} (b : o → Finₓ n) : Prop :=
  ∀ i j, b j < b i → M i j = 0

-- error in LinearAlgebra.Matrix.Block: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem upper_two_block_triangular'
{m n : Type*}
(A : matrix m m R)
(B : matrix m n R)
(D : matrix n n R) : block_triangular_matrix' (from_blocks A B 0 D) (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) :=
begin
  intros [ident k1, ident k2, ident hk12],
  have [ident h0] [":", expr ∀
   k : «expr ⊕ »(m, n), «expr = »(sum.elim (λ
     i, (0 : fin 2)) (λ j, 1) k, 0) → «expr∃ , »((i), «expr = »(k, sum.inl i))] [],
  { simp [] [] [] [] [] [] },
  have [ident h1] [":", expr ∀
   k : «expr ⊕ »(m, n), «expr = »(sum.elim (λ
     i, (0 : fin 2)) (λ j, 1) k, 1) → «expr∃ , »((j), «expr = »(k, sum.inr j))] [],
  { simp [] [] [] [] [] [] },
  set [] [ident mk1] [] [":="] [expr sum.elim (λ i, (0 : fin 2)) (λ j, 1) k1] ["with", ident hmk1],
  set [] [ident mk2] [] [":="] [expr sum.elim (λ i, (0 : fin 2)) (λ j, 1) k2] ["with", ident hmk2],
  fin_cases [ident mk1] []; fin_cases [ident mk2] []; rw ["[", expr h, ",", expr h_1, "]"] ["at", ident hk12],
  { exact [expr absurd hk12 (nat.not_lt_zero 0)] },
  { exact [expr absurd hk12 (by norm_num [] [])] },
  { rw [expr hmk1] ["at", ident h],
    obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr h1 k1 h],
    rw [expr hmk2] ["at", ident h_1],
    obtain ["⟨", ident j, ",", ident hj, "⟩", ":=", expr h0 k2 h_1],
    rw ["[", expr hi, ",", expr hj, "]"] [],
    simp [] [] [] [] [] [] },
  { exact [expr absurd hk12 (irrefl 1)] }
end

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `ℕ`s. Then
  `block_triangular_matrix M n b` says the matrix is block triangular. -/
def block_triangular_matrix {o : Type _} (M : Matrix o o R) (b : o → ℕ) : Prop :=
  ∀ i j, b j < b i → M i j = 0

-- error in LinearAlgebra.Matrix.Block: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem upper_two_block_triangular
{m n : Type*}
(A : matrix m m R)
(B : matrix m n R)
(D : matrix n n R) : block_triangular_matrix (from_blocks A B 0 D) (sum.elim (λ i, 0) (λ j, 1)) :=
begin
  intros [ident k1, ident k2, ident hk12],
  have [ident h01] [":", expr ∀
   k : «expr ⊕ »(m, n), «expr ∨ »(«expr = »(sum.elim (λ
      i, 0) (λ j, 1) k, 0), «expr = »(sum.elim (λ i, 0) (λ j, 1) k, 1))] [],
  { simp [] [] [] [] [] [] },
  have [ident h0] [":", expr ∀
   k : «expr ⊕ »(m, n), «expr = »(sum.elim (λ i, 0) (λ j, 1) k, 0) → «expr∃ , »((i), «expr = »(k, sum.inl i))] [],
  { simp [] [] [] [] [] [] },
  have [ident h1] [":", expr ∀
   k : «expr ⊕ »(m, n), «expr = »(sum.elim (λ i, 0) (λ j, 1) k, 1) → «expr∃ , »((j), «expr = »(k, sum.inr j))] [],
  { simp [] [] [] [] [] [] },
  cases [expr h01 k1] ["with", ident hk1, ident hk1]; cases [expr h01 k2] ["with", ident hk2, ident hk2]; rw ["[", expr hk1, ",", expr hk2, "]"] ["at", ident hk12],
  { exact [expr absurd hk12 (nat.not_lt_zero 0)] },
  { exact [expr absurd hk12 (nat.not_lt_zero 1)] },
  { obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr h1 k1 hk1],
    obtain ["⟨", ident j, ",", ident hj, "⟩", ":=", expr h0 k2 hk2],
    rw ["[", expr hi, ",", expr hj, "]"] [],
    simp [] [] [] [] [] [] },
  { exact [expr absurd hk12 (irrefl 1)] }
end

-- error in LinearAlgebra.Matrix.Block: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_of_block_triangular_matrix
(M : matrix m m R)
(b : m → exprℕ())
(h : block_triangular_matrix M b) : ∀
(n : exprℕ())
(hn : ∀ i, «expr < »(b i, n)), «expr = »(M.det, «expr∏ in , »((k), finset.range n, (to_square_block' M b k).det)) :=
begin
  intros [ident n, ident hn],
  tactic.unfreeze_local_instances,
  induction [expr n] [] ["with", ident n, ident hi] ["generalizing", ident m, ident M, ident b],
  { rw [expr finset.prod_range_zero] [],
    apply [expr det_eq_one_of_card_eq_zero],
    apply [expr fintype.card_eq_zero_iff.mpr],
    exact [expr ⟨λ i, nat.not_lt_zero (b i) (hn i)⟩] },
  { rw ["[", expr finset.prod_range_succ_comm, "]"] [],
    have [ident h2] [":", expr «expr = »((M.to_square_block_prop (λ
        i : m, «expr = »(b i, n.succ))).det, (M.to_square_block' b n.succ).det)] [],
    { dunfold [ident to_square_block'] [],
      dunfold [ident to_square_block_prop] [],
      refl },
    rw [expr two_block_triangular_det M (λ i, «expr¬ »(«expr = »(b i, n)))] [],
    { rw [expr mul_comm] [],
      apply [expr congr (congr_arg has_mul.mul _)],
      { let [ident m'] [] [":=", expr {a // «expr¬ »(«expr = »(b a, n))}],
        let [ident b'] [] [":=", expr λ i : m', b «expr↑ »(i)],
        have [ident h'] [":", expr block_triangular_matrix (M.to_square_block_prop (λ
           i : m, «expr¬ »(«expr = »(b i, n)))) b'] [],
        { intros [ident i, ident j],
          apply [expr h «expr↑ »(i) «expr↑ »(j)] },
        have [ident hni] [":", expr ∀ i : {a // «expr¬ »(«expr = »(b a, n))}, «expr < »(b' i, n)] [],
        { exact [expr λ i, (ne.le_iff_lt i.property).mp (nat.lt_succ_iff.mp (hn «expr↑ »(i)))] },
        have [ident h1] [] [":=", expr hi (M.to_square_block_prop (λ i : m, «expr¬ »(«expr = »(b i, n)))) b' h' hni],
        rw ["<-", expr fin.prod_univ_eq_prod_range] ["at", ident h1, "⊢"],
        convert [] [expr h1] [],
        ext [] [ident k] [],
        simp [] [] ["only"] ["[", expr to_square_block_def', ",", expr to_square_block_def, "]"] [] [],
        let [ident he] [":", expr «expr ≃ »({a // «expr = »(b' a, «expr↑ »(k))}, {a // «expr = »(b a, «expr↑ »(k))})] [],
        { have [ident hc] [":", expr ∀
           i : m, λ a, «expr = »(b a, «expr↑ »(k)) i → λ a, «expr¬ »(«expr = »(b a, n)) i] [],
          { intros [ident i, ident hbi],
            rw [expr hbi] [],
            exact [expr ne_of_lt (fin.is_lt k)] },
          exact [expr equiv.subtype_subtype_equiv_subtype hc] },
        exact [expr matrix.det_reindex_self he (λ
          i j : {a // «expr = »(b' a, «expr↑ »(k))}, M «expr↑ »(i) «expr↑ »(j))] },
      { rw [expr det_to_square_block' M b n] [],
        have [ident hh] [":", expr ∀
         a, «expr ↔ »(«expr = »(b a, n), «expr¬ »(λ i : m, «expr¬ »(«expr = »(b i, n)) a))] [],
        { intro [ident i],
          simp [] [] ["only"] ["[", expr not_not, "]"] [] [] },
        exact [expr equiv_block_det M hh] } },
    { intros [ident i, ident hi, ident j, ident hj],
      apply [expr h i],
      simp [] [] ["only"] ["[", expr not_not, "]"] [] ["at", ident hi],
      rw [expr hi] [],
      exact [expr (ne.le_iff_lt hj).mp (nat.lt_succ_iff.mp (hn j))] } }
end

-- error in LinearAlgebra.Matrix.Block: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_of_block_triangular_matrix''
(M : matrix m m R)
(b : m → exprℕ())
(h : block_triangular_matrix M b) : «expr = »(M.det, «expr∏ in , »((k), finset.image b finset.univ, (to_square_block' M b k).det)) :=
begin
  let [ident n] [":", expr exprℕ()] [":=", expr (Sup (finset.image b finset.univ : set exprℕ())).succ],
  have [ident hn] [":", expr ∀ i, «expr < »(b i, n)] [],
  { have [ident hbi] [":", expr ∀ i, «expr ∈ »(b i, finset.image b finset.univ)] [],
    { simp [] [] [] [] [] [] },
    intro [ident i],
    dsimp ["only"] ["[", expr n, "]"] [] [],
    apply [expr nat.lt_succ_iff.mpr],
    exact [expr le_cSup (finset.bdd_above _) (hbi i)] },
  rw [expr det_of_block_triangular_matrix M b h n hn] [],
  refine [expr (finset.prod_subset _ _).symm],
  { intros [ident a, ident ha],
    apply [expr finset.mem_range.mpr],
    obtain ["⟨", ident i, ",", "⟨", ident hi, ",", ident hbi, "⟩", "⟩", ":=", expr finset.mem_image.mp ha],
    rw ["<-", expr hbi] [],
    exact [expr hn i] },
  { intros [ident k, ident hk, ident hbk],
    apply [expr det_eq_one_of_card_eq_zero],
    apply [expr fintype.card_eq_zero_iff.mpr],
    constructor,
    simp [] [] ["only"] ["[", expr subtype.forall, "]"] [] [],
    intros [ident a, ident hba],
    apply [expr hbk],
    apply [expr finset.mem_image.mpr],
    use [expr a],
    exact [expr ⟨finset.mem_univ a, hba⟩] }
end

theorem det_of_block_triangular_matrix' (M : Matrix m m R) {n : ℕ} (b : m → Finₓ n) (h : block_triangular_matrix' M b) :
  M.det = ∏k : Finₓ n, (to_square_block M b k).det :=
  by 
    let b2 : m → ℕ := fun i => «expr↑ » (b i)
    simpRw [to_square_block_det'']
    rw [Finₓ.prod_univ_eq_prod_range (fun k : ℕ => (M.to_square_block' b2 k).det) n]
    apply det_of_block_triangular_matrix
    ·
      intro i j hij 
      exact h i j (fin.coe_fin_lt.mp hij)
    ·
      intro i 
      exact Finₓ.is_lt (b i)

-- error in LinearAlgebra.Matrix.Block: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_of_upper_triangular
{n : exprℕ()}
(M : matrix (fin n) (fin n) R)
(h : ∀ i j : fin n, «expr < »(j, i) → «expr = »(M i j, 0)) : «expr = »(M.det, «expr∏ , »((i : fin n), M i i)) :=
begin
  convert [] [expr det_of_block_triangular_matrix' M id h] [],
  ext [] [ident i] [],
  have [ident h2] [":", expr ∀
   j : {a // «expr = »(id a, i)}, «expr = »(j, ⟨i, rfl⟩)] [":=", expr λ
   j : {a // «expr = »(id a, i)}, subtype.ext j.property],
  haveI [] [":", expr unique {a // «expr = »(id a, i)}] [":=", expr ⟨⟨⟨i, rfl⟩⟩, h2⟩],
  simp [] [] [] ["[", expr h2 (default {a // «expr = »(id a, i)}), "]"] [] []
end

theorem det_of_lower_triangular {n : ℕ} (M : Matrix (Finₓ n) (Finₓ n) R) (h : ∀ i j : Finₓ n, i < j → M i j = 0) :
  M.det = ∏i : Finₓ n, M i i :=
  by 
    rw [←det_transpose]
    exact det_of_upper_triangular _ fun i j : Finₓ n hji : j < i => h j i hji

end Matrix

