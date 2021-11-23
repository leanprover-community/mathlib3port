import Mathbin.Data.Fintype.Card 
import Mathbin.Data.Finset.Sort 
import Mathbin.Algebra.BigOperators.Order

/-!
# Compositions

A composition of a natural number `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum
of positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : composition n` is a structure, made of a list of integers which are all positive and
  add up to `n`.
* `composition_card` states that the cardinality of `composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `composition_as_set n` (see below), which
  is itself in bijection with the subsets of `fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : composition n` be a composition of `n`. Then
* `c.blocks` is the list of blocks in `c`.
* `c.length` is the number of blocks in the composition.
* `c.blocks_fun : fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.size_up_to : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : fin (c.blocks_fun i) → fin n` is the increasing embedding of the `i`-th block in
  `fin n`;
* `c.index j`, for `j : fin n`, is the index of the block containing `j`.

* `composition.ones n` is the composition of `n` made of ones, i.e., `[1, ..., 1]`.
* `composition.single n (hn : 0 < n)` is the composition of `n` made of a single block of size `n`.

Compositions can also be used to split lists. Let `l` be a list of length `n` and `c` a composition
of `n`.
* `l.split_wrt_composition c` is a list of lists, made of the slices of `l` corresponding to the
  blocks of `c`.
* `join_split_wrt_composition` states that splitting a list and then joining it gives back the
  original list.
* `split_wrt_composition_join` states that joining a list of lists, and then splitting it back
  according to the right composition, gives back the original list of lists.

We turn to the second viewpoint on compositions, that we realize as a finset of `fin (n+1)`.
`c : composition_as_set n` is a structure made of a finset of `fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `composition n` and `composition_as_set n`. We
only construct basic API on `composition_as_set` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `composition_equiv n`. Since there is a straightforward equiv
between `composition_as_set n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `composition_as_set` and called `composition_as_set_equiv n`), we deduce that
`composition_as_set n` and `composition n` are both fintypes of cardinality `2^(n - 1)`
(see `composition_as_set_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/


open List

open_locale BigOperators

variable{n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext]
structure Composition(n : ℕ) where 
  blocks : List ℕ 
  blocks_pos : ∀ {i}, i ∈ blocks → 0 < i 
  blocks_sum : blocks.sum = n

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`composition_as_set n`. -/
@[ext]
structure CompositionAsSet(n : ℕ) where 
  boundaries : Finset (Finₓ n.succ)
  zero_mem : (0 : Finₓ n.succ) ∈ boundaries 
  last_mem : Finₓ.last n ∈ boundaries

instance  {n : ℕ} : Inhabited (CompositionAsSet n) :=
  ⟨⟨Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩⟩

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/


namespace Composition

variable(c : Composition n)

instance  (n : ℕ) : HasToString (Composition n) :=
  ⟨fun c => toString c.blocks⟩

/-- The length of a composition, i.e., the number of blocks in the composition. -/
@[reducible]
def length : ℕ :=
  c.blocks.length

theorem blocks_length : c.blocks.length = c.length :=
  rfl

/-- The blocks of a composition, seen as a function on `fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocks_fun : Finₓ c.length → ℕ :=
  fun i => nth_le c.blocks i i.2

theorem of_fn_blocks_fun : of_fn c.blocks_fun = c.blocks :=
  of_fn_nth_le _

theorem sum_blocks_fun : (∑i, c.blocks_fun i) = n :=
  by 
    convRHS => rw [←c.blocks_sum, ←of_fn_blocks_fun, sum_of_fn]

theorem blocks_fun_mem_blocks (i : Finₓ c.length) : c.blocks_fun i ∈ c.blocks :=
  nth_le_mem _ _ _

@[simp]
theorem one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
  c.blocks_pos h

@[simp]
theorem one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ nth_le c.blocks i h :=
  c.one_le_blocks (nth_le_mem (blocks c) i h)

@[simp]
theorem blocks_pos' (i : ℕ) (h : i < c.length) : 0 < nth_le c.blocks i h :=
  c.one_le_blocks' h

theorem one_le_blocks_fun (i : Finₓ c.length) : 1 ≤ c.blocks_fun i :=
  c.one_le_blocks (c.blocks_fun_mem_blocks i)

theorem length_le : c.length ≤ n :=
  by 
    convRHS => rw [←c.blocks_sum]
    exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

theorem length_pos_of_pos (h : 0 < n) : 0 < c.length :=
  by 
    apply length_pos_of_sum_pos 
    convert h 
    exact c.blocks_sum

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def size_up_to (i : ℕ) : ℕ :=
  (c.blocks.take i).Sum

@[simp]
theorem size_up_to_zero : c.size_up_to 0 = 0 :=
  by 
    simp [size_up_to]

theorem size_up_to_of_length_le (i : ℕ) (h : c.length ≤ i) : c.size_up_to i = n :=
  by 
    dsimp [size_up_to]
    convert c.blocks_sum 
    exact take_all_of_le h

@[simp]
theorem size_up_to_length : c.size_up_to c.length = n :=
  c.size_up_to_of_length_le c.length (le_reflₓ _)

theorem size_up_to_le (i : ℕ) : c.size_up_to i ≤ n :=
  by 
    convRHS => rw [←c.blocks_sum, ←sum_take_add_sum_drop _ i]
    exact Nat.le_add_rightₓ _ _

theorem size_up_to_succ {i : ℕ} (h : i < c.length) : c.size_up_to (i+1) = c.size_up_to i+c.blocks.nth_le i h :=
  by 
    simp only [size_up_to]
    rw [sum_take_succ _ _ h]

theorem size_up_to_succ' (i : Finₓ c.length) : c.size_up_to ((i : ℕ)+1) = c.size_up_to i+c.blocks_fun i :=
  c.size_up_to_succ i.2

theorem size_up_to_strict_mono {i : ℕ} (h : i < c.length) : c.size_up_to i < c.size_up_to (i+1) :=
  by 
    rw [c.size_up_to_succ h]
    simp 

theorem monotone_size_up_to : Monotone c.size_up_to :=
  monotone_sum_take _

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundary : Finₓ (c.length+1) ↪o Finₓ (n+1) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨c.size_up_to i, Nat.lt_succ_of_leₓ (c.size_up_to_le i)⟩)$
    Finₓ.strict_mono_iff_lt_succ.2$ fun i hi => c.size_up_to_strict_mono$ lt_of_add_lt_add_right hi

@[simp]
theorem boundary_zero : c.boundary 0 = 0 :=
  by 
    simp [boundary, Finₓ.ext_iff]

@[simp]
theorem boundary_last : c.boundary (Finₓ.last c.length) = Finₓ.last n :=
  by 
    simp [boundary, Finₓ.ext_iff]

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundaries : Finset (Finₓ (n+1)) :=
  Finset.univ.map c.boundary.to_embedding

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length+1 :=
  by 
    simp [boundaries]

/-- To `c : composition n`, one can associate a `composition_as_set n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def to_composition_as_set : CompositionAsSet n :=
  { boundaries := c.boundaries,
    zero_mem :=
      by 
        simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
        exact ⟨0, rfl⟩,
    last_mem :=
      by 
        simp only [boundaries, Finset.mem_univ, exists_prop_of_true, Finset.mem_map]
        exact ⟨Finₓ.last c.length, c.boundary_last⟩ }

/-- The canonical increasing bijection between `fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
theorem order_emb_of_fin_boundaries : c.boundaries.order_emb_of_fin c.card_boundaries_eq_succ_length = c.boundary :=
  by 
    refine' (Finset.order_emb_of_fin_unique' _ _).symm 
    exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

/-- Embedding the `i`-th block of a composition (identified with `fin (c.blocks_fun i)`) into
`fin n` at the relevant position. -/
def embedding (i : Finₓ c.length) : Finₓ (c.blocks_fun i) ↪o Finₓ n :=
  (Finₓ.natAdd$ c.size_up_to i).trans$
    Finₓ.castLe$
      calc (c.size_up_to i+c.blocks_fun i) = c.size_up_to (i+1) := (c.size_up_to_succ _).symm 
        _ ≤ c.size_up_to c.length := monotone_sum_take _ i.2
        _ = n := c.size_up_to_length
        

@[simp]
theorem coe_embedding (i : Finₓ c.length) (j : Finₓ (c.blocks_fun i)) : (c.embedding i j : ℕ) = c.size_up_to i+j :=
  rfl

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
`index_exists` asserts there is some `i` with `j < c.size_up_to (i+1)`.
In the next definition `index` we use `nat.find` to produce the minimal such index.
-/
theorem index_exists
{j : exprℕ()}
(h : «expr < »(j, n)) : «expr∃ , »((i : exprℕ()), «expr ∧ »(«expr < »(j, c.size_up_to i.succ), «expr < »(i, c.length))) :=
begin
  have [ident n_pos] [":", expr «expr < »(0, n)] [":=", expr lt_of_le_of_lt (zero_le j) h],
  have [] [":", expr «expr < »(0, c.blocks.sum)] [],
  by rwa ["[", "<-", expr c.blocks_sum, "]"] ["at", ident n_pos],
  have [ident length_pos] [":", expr «expr < »(0, c.blocks.length)] [":=", expr length_pos_of_sum_pos (blocks c) this],
  refine [expr ⟨c.length.pred, _, nat.pred_lt (ne_of_gt length_pos)⟩],
  have [] [":", expr «expr = »(c.length.pred.succ, c.length)] [":=", expr nat.succ_pred_eq_of_pos length_pos],
  simp [] [] [] ["[", expr this, ",", expr h, "]"] [] []
end

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index (j : Finₓ n) : Finₓ c.length :=
  ⟨Nat.findₓ (c.index_exists j.2), (Nat.find_specₓ (c.index_exists j.2)).2⟩

theorem lt_size_up_to_index_succ (j : Finₓ n) : (j : ℕ) < c.size_up_to (c.index j).succ :=
  (Nat.find_specₓ (c.index_exists j.2)).1

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem size_up_to_index_le (j : fin n) : «expr ≤ »(c.size_up_to (c.index j), j) :=
begin
  by_contradiction [ident H],
  set [] [ident i] [] [":="] [expr c.index j] ["with", ident hi],
  push_neg ["at", ident H],
  have [ident i_pos] [":", expr «expr < »((0 : exprℕ()), i)] [],
  { by_contradiction [ident i_pos],
    push_neg ["at", ident i_pos],
    revert [ident H],
    simp [] [] [] ["[", expr nonpos_iff_eq_zero.1 i_pos, ",", expr c.size_up_to_zero, "]"] [] [] },
  let [ident i₁] [] [":=", expr (i : exprℕ()).pred],
  have [ident i₁_lt_i] [":", expr «expr < »(i₁, i)] [":=", expr nat.pred_lt (ne_of_gt i_pos)],
  have [ident i₁_succ] [":", expr «expr = »(i₁.succ, i)] [":=", expr nat.succ_pred_eq_of_pos i_pos],
  have [] [] [":=", expr nat.find_min (c.index_exists j.2) i₁_lt_i],
  simp [] [] [] ["[", expr lt_trans i₁_lt_i (c.index j).2, ",", expr i₁_succ, "]"] [] ["at", ident this],
  exact [expr nat.lt_le_antisymm H this]
end

/-- Mapping an element `j` of `fin n` to the element in the block containing it, identified with
`fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def inv_embedding (j : Finₓ n) : Finₓ (c.blocks_fun (c.index j)) :=
  ⟨j - c.size_up_to (c.index j),
    by 
      rw [tsub_lt_iff_right, add_commₓ, ←size_up_to_succ']
      ·
        exact lt_size_up_to_index_succ _ _
      ·
        exact size_up_to_index_le _ _⟩

@[simp]
theorem coe_inv_embedding (j : Finₓ n) : (c.inv_embedding j : ℕ) = j - c.size_up_to (c.index j) :=
  rfl

theorem embedding_comp_inv (j : Finₓ n) : c.embedding (c.index j) (c.inv_embedding j) = j :=
  by 
    rw [Finₓ.ext_iff]
    apply add_tsub_cancel_of_le (c.size_up_to_index_le j)

theorem mem_range_embedding_iff {j : Finₓ n} {i : Finₓ c.length} :
  j ∈ Set.Range (c.embedding i) ↔ c.size_up_to i ≤ j ∧ (j : ℕ) < c.size_up_to (i : ℕ).succ :=
  by 
    split 
    ·
      intro h 
      rcases Set.mem_range.2 h with ⟨k, hk⟩
      rw [Finₓ.ext_iff] at hk 
      change (c.size_up_to i+k) = (j : ℕ) at hk 
      rw [←hk]
      simp [size_up_to_succ', k.is_lt]
    ·
      intro h 
      apply Set.mem_range.2
      refine' ⟨⟨j - c.size_up_to i, _⟩, _⟩
      ·
        rw [tsub_lt_iff_left, ←size_up_to_succ']
        ·
          exact h.2
        ·
          exact h.1
      ·
        rw [Finₓ.ext_iff]
        exact add_tsub_cancel_of_le h.1

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The embeddings of different blocks of a composition are disjoint. -/
theorem disjoint_range
{i₁ i₂ : fin c.length}
(h : «expr ≠ »(i₁, i₂)) : disjoint (set.range (c.embedding i₁)) (set.range (c.embedding i₂)) :=
begin
  classical,
  wlog [ident h'] [":", expr «expr ≤ »(i₁, i₂)] [] ["using", ident i₁, ident i₂],
  swap,
  exact [expr (this h.symm).symm],
  by_contradiction [ident d],
  obtain ["⟨", ident x, ",", ident hx₁, ",", ident hx₂, "⟩", ":", expr «expr∃ , »((x : fin n), «expr ∧ »(«expr ∈ »(x, set.range (c.embedding i₁)), «expr ∈ »(x, set.range (c.embedding i₂)))), ":=", expr set.not_disjoint_iff.1 d],
  have [] [":", expr «expr < »(i₁, i₂)] [":=", expr lt_of_le_of_ne h' h],
  have [ident A] [":", expr «expr ≤ »((i₁ : exprℕ()).succ, i₂)] [":=", expr nat.succ_le_of_lt this],
  apply [expr lt_irrefl (x : exprℕ())],
  calc
    «expr < »((x : exprℕ()), c.size_up_to (i₁ : exprℕ()).succ) : (c.mem_range_embedding_iff.1 hx₁).2
    «expr ≤ »(..., c.size_up_to (i₂ : exprℕ())) : monotone_sum_take _ A
    «expr ≤ »(..., x) : (c.mem_range_embedding_iff.1 hx₂).1
end

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_range_embedding (j : fin n) : «expr ∈ »(j, set.range (c.embedding (c.index j))) :=
begin
  have [] [":", expr «expr ∈ »(c.embedding (c.index j) (c.inv_embedding j), set.range (c.embedding (c.index j)))] [":=", expr set.mem_range_self _],
  rwa [expr c.embedding_comp_inv j] ["at", ident this]
end

theorem mem_range_embedding_iff' {j : Finₓ n} {i : Finₓ c.length} : j ∈ Set.Range (c.embedding i) ↔ i = c.index j :=
  by 
    split 
    ·
      rw [←not_imp_not]
      intro h 
      exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
    ·
      intro h 
      rw [h]
      exact c.mem_range_embedding j

theorem index_embedding (i : Finₓ c.length) (j : Finₓ (c.blocks_fun i)) : c.index (c.embedding i j) = i :=
  by 
    symm 
    rw [←mem_range_embedding_iff']
    apply Set.mem_range_self

theorem inv_embedding_comp (i : Finₓ c.length) (j : Finₓ (c.blocks_fun i)) :
  (c.inv_embedding (c.embedding i j) : ℕ) = j :=
  by 
    simpRw [coe_inv_embedding, index_embedding, coe_embedding, add_tsub_cancel_left]

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`fin (c.blocks_fun i)`) with `fin n`. -/
def blocks_fin_equiv : (Σi : Finₓ c.length, Finₓ (c.blocks_fun i)) ≃ Finₓ n :=
  { toFun := fun x => c.embedding x.1 x.2, invFun := fun j => ⟨c.index j, c.inv_embedding j⟩,
    left_inv :=
      fun x =>
        by 
          rcases x with ⟨i, y⟩
          dsimp 
          congr
          ·
            exact c.index_embedding _ _ 
          rw [Finₓ.heq_ext_iff]
          ·
            exact c.inv_embedding_comp _ _
          ·
            rw [c.index_embedding],
    right_inv := fun j => c.embedding_comp_inv j }

theorem blocks_fun_congr {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Finₓ c₁.length)
  (i₂ : Finₓ c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
  c₁.blocks_fun i₁ = c₂.blocks_fun i₂ :=
  by 
    cases hn 
    rw [←Composition.ext_iff] at hc 
    cases hc 
    congr 
    rwa [Finₓ.ext_iff]

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
theorem sigma_eq_iff_blocks_eq
{c : «exprΣ , »((n), composition n)}
{c' : «exprΣ , »((n), composition n)} : «expr ↔ »(«expr = »(c, c'), «expr = »(c.2.blocks, c'.2.blocks)) :=
begin
  refine [expr ⟨λ H, by rw [expr H] [], λ H, _⟩],
  rcases [expr c, "with", "⟨", ident n, ",", ident c, "⟩"],
  rcases [expr c', "with", "⟨", ident n', ",", ident c', "⟩"],
  have [] [":", expr «expr = »(n, n')] [],
  by { rw ["[", "<-", expr c.blocks_sum, ",", "<-", expr c'.blocks_sum, ",", expr H, "]"] [] },
  induction [expr this] [] [] [],
  simp [] [] ["only"] ["[", expr true_and, ",", expr eq_self_iff_true, ",", expr heq_iff_eq, "]"] [] [],
  ext1 [] [],
  exact [expr H]
end

/-! ### The composition `composition.ones` -/


/-- The composition made of blocks all of size `1`. -/
def ones (n : ℕ) : Composition n :=
  ⟨repeat (1 : ℕ) n,
    fun i hi =>
      by 
        simp [List.eq_of_mem_repeat hi],
    by 
      simp ⟩

instance  {n : ℕ} : Inhabited (Composition n) :=
  ⟨Composition.ones n⟩

@[simp]
theorem ones_length (n : ℕ) : (ones n).length = n :=
  List.length_repeat 1 n

@[simp]
theorem ones_blocks (n : ℕ) : (ones n).blocks = repeat (1 : ℕ) n :=
  rfl

@[simp]
theorem ones_blocks_fun (n : ℕ) (i : Finₓ (ones n).length) : (ones n).blocksFun i = 1 :=
  by 
    simp [blocks_fun, ones, blocks, i.2]

@[simp]
theorem ones_size_up_to (n : ℕ) (i : ℕ) : (ones n).sizeUpTo i = min i n :=
  by 
    simp [size_up_to, ones_blocks, take_repeat]

@[simp]
theorem ones_embedding (i : Finₓ (ones n).length) (h : 0 < (ones n).blocksFun i) :
  (ones n).Embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_leₓ i.2 (ones n).length_le⟩ :=
  by 
    ext 
    simpa using i.2.le

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_ones_iff {c : composition n} : «expr ↔ »(«expr = »(c, ones n), ∀ i «expr ∈ » c.blocks, «expr = »(i, 1)) :=
begin
  split,
  { rintro [ident rfl],
    exact [expr λ i, eq_of_mem_repeat] },
  { assume [binders (H)],
    ext1 [] [],
    have [ident A] [":", expr «expr = »(c.blocks, repeat 1 c.blocks.length)] [":=", expr eq_repeat_of_mem H],
    have [] [":", expr «expr = »(c.blocks.length, n)] [],
    by { conv_rhs [] [] { rw ["[", "<-", expr c.blocks_sum, ",", expr A, "]"] },
      simp [] [] [] [] [] [] },
    rw ["[", expr A, ",", expr this, ",", expr ones_blocks, "]"] [] }
end

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ne_ones_iff
{c : composition n} : «expr ↔ »(«expr ≠ »(c, ones n), «expr∃ , »((i «expr ∈ » c.blocks), «expr < »(1, i))) :=
begin
  refine [expr (not_congr eq_ones_iff).trans _],
  have [] [":", expr ∀
   j «expr ∈ » c.blocks, «expr ↔ »(«expr = »(j, 1), «expr ≤ »(j, 1))] [":=", expr λ
   j hj, by simp [] [] [] ["[", expr le_antisymm_iff, ",", expr c.one_le_blocks hj, "]"] [] []],
  simp [] [] [] ["[", expr this, "]"] [] [] { contextual := tt }
end

theorem eq_ones_iff_length {c : Composition n} : c = ones n ↔ c.length = n :=
  by 
    split 
    ·
      rintro rfl 
      exact ones_length n
    ·
      contrapose 
      intro H length_n 
      apply lt_irreflₓ n 
      calc n = ∑i : Finₓ c.length, 1 :=
        by 
          simp [length_n]_ < ∑i : Finₓ c.length, c.blocks_fun i :=
        by 
          obtain ⟨i, hi, i_blocks⟩ : ∃ (i : _)(_ : i ∈ c.blocks), 1 < i := ne_ones_iff.1 H 
          rw [←of_fn_blocks_fun, mem_of_fn c.blocks_fun, Set.mem_range] at hi 
          obtain ⟨j : Finₓ c.length, hj : c.blocks_fun j = i⟩ := hi 
          rw [←hj] at i_blocks 
          exact
            Finset.sum_lt_sum
              (fun i hi =>
                by 
                  simp [blocks_fun])
              ⟨j, Finset.mem_univ _, i_blocks⟩_ = n :=
        c.sum_blocks_fun

theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n ≤ c.length :=
  by 
    simp [eq_ones_iff_length, le_antisymm_iffₓ, c.length_le]

/-! ### The composition `composition.single` -/


/-- The composition made of a single block of size `n`. -/
def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n],
    by 
      simp [h],
    by 
      simp ⟩

@[simp]
theorem single_length {n : ℕ} (h : 0 < n) : (single n h).length = 1 :=
  rfl

@[simp]
theorem single_blocks {n : ℕ} (h : 0 < n) : (single n h).blocks = [n] :=
  rfl

@[simp]
theorem single_blocks_fun {n : ℕ} (h : 0 < n) (i : Finₓ (single n h).length) : (single n h).blocksFun i = n :=
  by 
    simp [blocks_fun, single, blocks, i.2]

@[simp]
theorem single_embedding {n : ℕ} (h : 0 < n) (i : Finₓ n) :
  (single n h).Embedding ⟨0, single_length h ▸ zero_lt_one⟩ i = i :=
  by 
    ext 
    simp 

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_single_iff_length
{n : exprℕ()}
(h : «expr < »(0, n))
{c : composition n} : «expr ↔ »(«expr = »(c, single n h), «expr = »(c.length, 1)) :=
begin
  split,
  { assume [binders (H)],
    rw [expr H] [],
    exact [expr single_length h] },
  { assume [binders (H)],
    ext1 [] [],
    have [ident A] [":", expr «expr = »(c.blocks.length, 1)] [":=", expr «expr ▸ »(H, c.blocks_length)],
    have [ident B] [":", expr «expr = »(c.blocks.sum, n)] [":=", expr c.blocks_sum],
    rw [expr eq_cons_of_length_one A] ["at", ident B, "⊢"],
    simpa [] [] [] ["[", expr single_blocks, "]"] [] ["using", expr B] }
end

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ne_single_iff
{n : exprℕ()}
(hn : «expr < »(0, n))
{c : composition n} : «expr ↔ »(«expr ≠ »(c, single n hn), ∀ i, «expr < »(c.blocks_fun i, n)) :=
begin
  rw ["<-", expr not_iff_not] [],
  push_neg [],
  split,
  { rintros [ident rfl],
    exact [expr ⟨⟨0, by simp [] [] [] [] [] []⟩, by simp [] [] [] [] [] []⟩] },
  { rintros ["⟨", ident i, ",", ident hi, "⟩"],
    rw [expr eq_single_iff_length] [],
    have [] [":", expr ∀ j : fin c.length, «expr = »(j, i)] [],
    { intros [ident j],
      by_contradiction [ident ji],
      apply [expr lt_irrefl «expr∑ , »((k), c.blocks_fun k)],
      calc
        «expr ≤ »(«expr∑ , »((k), c.blocks_fun k), c.blocks_fun i) : by simp [] [] ["only"] ["[", expr c.sum_blocks_fun, ",", expr hi, "]"] [] []
        «expr < »(..., «expr∑ , »((k), c.blocks_fun k)) : finset.single_lt_sum ji (finset.mem_univ _) (finset.mem_univ _) (c.one_le_blocks_fun j) (λ
         _ _ _, zero_le _) },
    simpa [] [] [] [] [] ["using", expr fintype.card_eq_one_of_forall_eq this] }
end

end Composition

/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocks_fun 0`, ..., `c.blocks_fun (c.length-1)`. This is inverse to the
join operation.
-/


namespace List

variable{α : Type _}

/-- Auxiliary for `list.split_wrt_composition`. -/
def split_wrt_composition_aux : List α → List ℕ → List (List α)
| l, [] => []
| l, n :: ns =>
  let (l₁, l₂) := l.split_at n 
  l₁ :: split_wrt_composition_aux l₂ ns

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
def split_wrt_composition (l : List α) (c : Composition n) : List (List α) :=
  split_wrt_composition_aux l c.blocks

attribute [local simp] split_wrt_composition_aux.equations._eqn_1

@[local simp]
theorem split_wrt_composition_aux_cons (l : List α) n ns :
  l.split_wrt_composition_aux (n :: ns) = take n l :: (drop n l).splitWrtCompositionAux ns :=
  by 
    simp [split_wrt_composition_aux]

theorem length_split_wrt_composition_aux (l : List α) ns : length (l.split_wrt_composition_aux ns) = ns.length :=
  by 
    induction ns generalizing l <;> simp 

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp]
theorem length_split_wrt_composition (l : List α) (c : Composition n) : length (l.split_wrt_composition c) = c.length :=
  length_split_wrt_composition_aux _ _

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_length_split_wrt_composition_aux
{ns : list exprℕ()} : ∀
{l : list α}, «expr ≤ »(ns.sum, l.length) → «expr = »(map length (l.split_wrt_composition_aux ns), ns) :=
begin
  induction [expr ns] [] ["with", ident n, ident ns, ident IH] []; intros [ident l, ident h]; simp [] [] [] [] [] ["at", ident h, "⊢"],
  have [] [] [":=", expr le_trans (nat.le_add_right _ _) h],
  rw [expr IH] [],
  { simp [] [] [] ["[", expr this, "]"] [] [] },
  rwa ["[", expr length_drop, ",", expr le_tsub_iff_left this, "]"] []
end

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
theorem map_length_split_wrt_composition (l : List α) (c : Composition l.length) :
  map length (l.split_wrt_composition c) = c.blocks :=
  map_length_split_wrt_composition_aux (le_of_eqₓ c.blocks_sum)

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem length_pos_of_mem_split_wrt_composition
{l l' : list α}
{c : composition l.length}
(h : «expr ∈ »(l', l.split_wrt_composition c)) : «expr < »(0, length l') :=
begin
  have [] [":", expr «expr ∈ »(l'.length, (l.split_wrt_composition c).map list.length)] [":=", expr list.mem_map_of_mem list.length h],
  rw [expr map_length_split_wrt_composition] ["at", ident this],
  exact [expr c.blocks_pos this]
end

theorem sum_take_map_length_split_wrt_composition (l : List α) (c : Composition l.length) (i : ℕ) :
  (((l.split_wrt_composition c).map length).take i).Sum = c.size_up_to i :=
  by 
    congr 
    exact map_length_split_wrt_composition l c

theorem nth_le_split_wrt_composition_aux (l : List α) (ns : List ℕ) {i : ℕ} hi :
  nth_le (l.split_wrt_composition_aux ns) i hi = (l.take (ns.take (i+1)).Sum).drop (ns.take i).Sum :=
  by 
    induction' ns with n ns IH generalizing l i
    ·
      cases hi 
    cases i <;> simp [IH]
    rw [add_commₓ n, drop_add, drop_take]

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.size_up_to i` and `c.size_up_to (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
theorem nth_le_split_wrt_composition (l : List α) (c : Composition n) {i : ℕ}
  (hi : i < (l.split_wrt_composition c).length) :
  nth_le (l.split_wrt_composition c) i hi = (l.take (c.size_up_to (i+1))).drop (c.size_up_to i) :=
  nth_le_split_wrt_composition_aux _ _ _

theorem join_split_wrt_composition_aux {ns : List ℕ} :
  ∀ {l : List α}, ns.sum = l.length → (l.split_wrt_composition_aux ns).join = l :=
  by 
    induction' ns with n ns IH <;> intro l h <;> simp  at h⊢
    ·
      exact (length_eq_zero.1 h.symm).symm 
    rw [IH]
    ·
      simp 
    rwa [length_drop, ←h, add_tsub_cancel_left]

/-- If one splits a list along a composition, and then joins the sublists, one gets back the
original list. -/
@[simp]
theorem join_split_wrt_composition (l : List α) (c : Composition l.length) : (l.split_wrt_composition c).join = l :=
  join_split_wrt_composition_aux c.blocks_sum

/-- If one joins a list of lists and then splits the join along the right composition, one gets
back the original list of lists. -/
@[simp]
theorem split_wrt_composition_join (L : List (List α)) (c : Composition L.join.length) (h : map length L = c.blocks) :
  split_wrt_composition (join L) c = L :=
  by 
    simp only [eq_self_iff_true, and_selfₓ, eq_iff_join_eq, join_split_wrt_composition,
      map_length_split_wrt_composition, h]

end List

/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/


-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def composition_as_set_equiv (n : exprℕ()) : «expr ≃ »(composition_as_set n, finset (fin «expr - »(n, 1))) :=
{ to_fun := λ
  c, {i : fin «expr - »(n, 1) | «expr ∈ »((⟨«expr + »(1, (i : exprℕ())), begin
      apply [expr (add_lt_add_left i.is_lt 1).trans_le],
      rw ["[", expr nat.succ_eq_add_one, ",", expr add_comm, "]"] [],
      exact [expr add_le_add (nat.sub_le n 1) (le_refl 1)]
    end⟩ : fin n.succ), c.boundaries)}.to_finset,
  inv_fun := λ
  s, { boundaries := {i : fin n.succ | «expr ∨ »(«expr = »(i, 0), «expr ∨ »(«expr = »(i, fin.last n), «expr∃ , »((j : fin «expr - »(n, 1))
       (hj : «expr ∈ »(j, s)), «expr = »((i : exprℕ()), «expr + »(j, 1)))))}.to_finset,
    zero_mem := by simp [] [] [] [] [] [],
    last_mem := by simp [] [] [] [] [] [] },
  left_inv := begin
    assume [binders (c)],
    ext [] [ident i] [],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr add_comm, ",", expr set.mem_to_finset, ",", expr true_or, ",", expr or_true, ",", expr set.mem_set_of_eq, "]"] [] [],
    split,
    { rintro ["(", ident rfl, "|", ident rfl, "|", "⟨", ident j, ",", ident hj1, ",", ident hj2, "⟩", ")"],
      { exact [expr c.zero_mem] },
      { exact [expr c.last_mem] },
      { convert [] [expr hj1] [],
        rwa [expr fin.ext_iff] [] } },
    { simp [] [] ["only"] ["[", expr or_iff_not_imp_left, "]"] [] [],
      assume [binders (i_mem i_ne_zero i_ne_last)],
      simp [] [] [] ["[", expr fin.ext_iff, "]"] [] ["at", ident i_ne_zero, ident i_ne_last],
      have [ident A] [":", expr «expr = »((«expr + »(1, «expr - »(i, 1)) : exprℕ()), (i : exprℕ()))] [],
      by { rw [expr add_comm] [],
        exact [expr nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr i_ne_zero)] },
      refine [expr ⟨⟨«expr - »(i, 1), _⟩, _, _⟩],
      { have [] [":", expr «expr < »((i : exprℕ()), «expr + »(n, 1))] [":=", expr i.2],
        simp [] [] [] ["[", expr nat.lt_succ_iff_lt_or_eq, ",", expr i_ne_last, "]"] [] ["at", ident this],
        exact [expr nat.pred_lt_pred i_ne_zero this] },
      { convert [] [expr i_mem] [],
        rw [expr fin.ext_iff] [],
        simp [] [] ["only"] ["[", expr fin.coe_mk, ",", expr A, "]"] [] [] },
      { simp [] [] [] ["[", expr A, "]"] [] [] } }
  end,
  right_inv := begin
    assume [binders (s)],
    ext [] [ident i] [],
    have [] [":", expr «expr ≠ »(«expr + »(1, (i : exprℕ())), n)] [],
    { apply [expr ne_of_lt],
      convert [] [expr add_lt_add_left i.is_lt 1] [],
      rw [expr add_comm] [],
      apply [expr (nat.succ_pred_eq_of_pos _).symm],
      exact [expr (zero_le i.val).trans_lt (i.2.trans_le (nat.sub_le n 1))] },
    simp [] [] ["only"] ["[", expr fin.ext_iff, ",", expr exists_prop, ",", expr fin.coe_zero, ",", expr add_comm, ",", expr set.mem_to_finset, ",", expr set.mem_set_of_eq, ",", expr fin.coe_last, "]"] [] [],
    erw ["[", expr set.mem_set_of_eq, "]"] [],
    simp [] [] ["only"] ["[", expr this, ",", expr false_or, ",", expr add_right_inj, ",", expr add_eq_zero_iff, ",", expr one_ne_zero, ",", expr false_and, ",", expr fin.coe_mk, "]"] [] [],
    split,
    { rintros ["⟨", ident j, ",", ident js, ",", ident hj, "⟩"],
      convert [] [expr js] [],
      exact [expr (fin.ext_iff _ _).2 hj] },
    { assume [binders (h)],
      exact [expr ⟨i, h, rfl⟩] }
  end }

instance compositionAsSetFintype (n : ℕ) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem composition_as_set_card
(n : exprℕ()) : «expr = »(fintype.card (composition_as_set n), «expr ^ »(2, «expr - »(n, 1))) :=
begin
  have [] [":", expr «expr = »(fintype.card (finset (fin «expr - »(n, 1))), «expr ^ »(2, «expr - »(n, 1)))] [],
  by simp [] [] [] [] [] [],
  rw ["<-", expr this] [],
  exact [expr fintype.card_congr (composition_as_set_equiv n)]
end

namespace CompositionAsSet

variable(c : CompositionAsSet n)

theorem boundaries_nonempty : c.boundaries.nonempty :=
  ⟨0, c.zero_mem⟩

theorem card_boundaries_pos : 0 < Finset.card c.boundaries :=
  Finset.card_pos.mpr c.boundaries_nonempty

/-- Number of blocks in a `composition_as_set`. -/
def length : ℕ :=
  Finset.card c.boundaries - 1

theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length+1 :=
  (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_ltₓ c.card_boundaries_pos)).mp rfl

theorem length_lt_card_boundaries : c.length < c.boundaries.card :=
  by 
    rw [c.card_boundaries_eq_succ_length]
    exact lt_add_one _

theorem lt_length (i : Finₓ c.length) : ((i : ℕ)+1) < c.boundaries.card :=
  lt_tsub_iff_right.mp i.2

theorem lt_length' (i : Finₓ c.length) : (i : ℕ) < c.boundaries.card :=
  lt_of_le_of_ltₓ (Nat.le_succₓ i) (c.lt_length i)

/-- Canonical increasing bijection from `fin c.boundaries.card` to `c.boundaries`. -/
def boundary : Finₓ c.boundaries.card ↪o Finₓ (n+1) :=
  c.boundaries.order_emb_of_fin rfl

@[simp]
theorem boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Finₓ (n+1)) = 0 :=
  by 
    rw [boundary, Finset.order_emb_of_fin_zero rfl c.card_boundaries_pos]
    exact le_antisymmₓ (Finset.min'_le _ _ c.zero_mem) (Finₓ.zero_le _)

@[simp]
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Finₓ.last n :=
  by 
    convert Finset.order_emb_of_fin_last rfl c.card_boundaries_pos 
    exact le_antisymmₓ (Finset.le_max' _ _ c.last_mem) (Finₓ.le_last _)

/-- Size of the `i`-th block in a `composition_as_set`, seen as a function on `fin c.length`. -/
def blocks_fun (i : Finₓ c.length) : ℕ :=
  c.boundary ⟨(i : ℕ)+1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem blocks_fun_pos (i : fin c.length) : «expr < »(0, c.blocks_fun i) :=
begin
  have [] [":", expr «expr < »((⟨i, c.lt_length' i⟩ : fin c.boundaries.card), ⟨«expr + »(i, 1), c.lt_length i⟩)] [":=", expr nat.lt_succ_self _],
  exact [expr lt_tsub_iff_left.mpr ((c.boundaries.order_emb_of_fin rfl).strict_mono this)]
end

/-- List of the sizes of the blocks in a `composition_as_set`. -/
def blocks (c : CompositionAsSet n) : List ℕ :=
  of_fn c.blocks_fun

@[simp]
theorem blocks_length : c.blocks.length = c.length :=
  length_of_fn _

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem blocks_partial_sum
{i : exprℕ()}
(h : «expr < »(i, c.boundaries.card)) : «expr = »((c.blocks.take i).sum, c.boundary ⟨i, h⟩) :=
begin
  induction [expr i] [] ["with", ident i, ident IH] [],
  { simp [] [] [] [] [] [] },
  have [ident A] [":", expr «expr < »(i, c.blocks.length)] [],
  { rw [expr c.card_boundaries_eq_succ_length] ["at", ident h],
    simp [] [] [] ["[", expr blocks, ",", expr nat.lt_of_succ_lt_succ h, "]"] [] [] },
  have [ident B] [":", expr «expr < »(i, c.boundaries.card)] [":=", expr lt_of_lt_of_le A (by simp [] [] [] ["[", expr blocks, ",", expr length, ",", expr nat.sub_le, "]"] [] [])],
  rw ["[", expr sum_take_succ _ _ A, ",", expr IH B, "]"] [],
  simp [] [] ["only"] ["[", expr blocks, ",", expr blocks_fun, ",", expr nth_le_of_fn', "]"] [] [],
  apply [expr add_tsub_cancel_of_le],
  simp [] [] [] [] [] []
end

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_boundaries_iff_exists_blocks_sum_take_eq
{j : fin «expr + »(n, 1)} : «expr ↔ »(«expr ∈ »(j, c.boundaries), «expr∃ , »((i «expr < » c.boundaries.card), «expr = »((c.blocks.take i).sum, j))) :=
begin
  split,
  { assume [binders (hj)],
    rcases [expr (c.boundaries.order_iso_of_fin rfl).surjective ⟨j, hj⟩, "with", "⟨", ident i, ",", ident hi, "⟩"],
    rw ["[", expr subtype.ext_iff, ",", expr subtype.coe_mk, "]"] ["at", ident hi],
    refine [expr ⟨i.1, i.2, _⟩],
    rw ["[", "<-", expr hi, ",", expr c.blocks_partial_sum i.2, "]"] [],
    refl },
  { rintros ["⟨", ident i, ",", ident hi, ",", ident H, "⟩"],
    convert [] [expr (c.boundaries.order_iso_of_fin rfl ⟨i, hi⟩).2] [],
    have [] [":", expr «expr = »(c.boundary ⟨i, hi⟩, j)] [],
    by rwa ["[", expr fin.ext_iff, ",", "<-", expr c.blocks_partial_sum hi, "]"] [],
    exact [expr this.symm] }
end

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem blocks_sum : «expr = »(c.blocks.sum, n) :=
begin
  have [] [":", expr «expr = »(c.blocks.take c.length, c.blocks)] [":=", expr take_all_of_le (by simp [] [] [] ["[", expr blocks, "]"] [] [])],
  rw ["[", "<-", expr this, ",", expr c.blocks_partial_sum c.length_lt_card_boundaries, ",", expr c.boundary_length, "]"] [],
  refl
end

/-- Associating a `composition n` to a `composition_as_set n`, by registering the sizes of the
blocks as a list of positive integers. -/
def to_composition : Composition n :=
  { blocks := c.blocks,
    blocks_pos :=
      by 
        simp only [blocks, forall_mem_of_fn_iff, blocks_fun_pos c, forall_true_iff],
    blocks_sum := c.blocks_sum }

end CompositionAsSet

/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `composition` and a
`composition_as_set`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `composition_equiv`.
-/


@[simp]
theorem Composition.to_composition_as_set_length (c : Composition n) : c.to_composition_as_set.length = c.length :=
  by 
    simp [Composition.toCompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length]

@[simp]
theorem CompositionAsSet.to_composition_length (c : CompositionAsSet n) : c.to_composition.length = c.length :=
  by 
    simp [CompositionAsSet.toComposition, Composition.length, Composition.blocks]

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem composition.to_composition_as_set_blocks
(c : composition n) : «expr = »(c.to_composition_as_set.blocks, c.blocks) :=
begin
  let [ident d] [] [":=", expr c.to_composition_as_set],
  change [expr «expr = »(d.blocks, c.blocks)] [] [],
  have [ident length_eq] [":", expr «expr = »(d.blocks.length, c.blocks.length)] [],
  { convert [] [expr c.to_composition_as_set_length] [],
    simp [] [] [] ["[", expr composition_as_set.blocks, "]"] [] [] },
  suffices [ident H] [":", expr ∀ i «expr ≤ » d.blocks.length, «expr = »((d.blocks.take i).sum, (c.blocks.take i).sum)],
  from [expr eq_of_sum_take_eq length_eq H],
  assume [binders (i hi)],
  have [ident i_lt] [":", expr «expr < »(i, d.boundaries.card)] [],
  { convert [] [expr nat.lt_succ_iff.2 hi] [],
    convert [] [expr d.card_boundaries_eq_succ_length] [],
    exact [expr length_of_fn _] },
  have [ident i_lt'] [":", expr «expr < »(i, c.boundaries.card)] [":=", expr i_lt],
  have [ident i_lt''] [":", expr «expr < »(i, «expr + »(c.length, 1))] [],
  by rwa [expr c.card_boundaries_eq_succ_length] ["at", ident i_lt'],
  have [ident A] [":", expr «expr = »(d.boundaries.order_emb_of_fin rfl ⟨i, i_lt⟩, c.boundaries.order_emb_of_fin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩)] [":=", expr rfl],
  have [ident B] [":", expr «expr = »(c.size_up_to i, c.boundary ⟨i, i_lt''⟩)] [":=", expr rfl],
  rw ["[", expr d.blocks_partial_sum i_lt, ",", expr composition_as_set.boundary, ",", "<-", expr composition.size_up_to, ",", expr B, ",", expr A, ",", expr c.order_emb_of_fin_boundaries, "]"] []
end

@[simp]
theorem CompositionAsSet.to_composition_blocks (c : CompositionAsSet n) : c.to_composition.blocks = c.blocks :=
  rfl

-- error in Combinatorics.Composition: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem composition_as_set.to_composition_boundaries
(c : composition_as_set n) : «expr = »(c.to_composition.boundaries, c.boundaries) :=
begin
  ext [] [ident j] [],
  simp [] [] [] ["[", expr c.mem_boundaries_iff_exists_blocks_sum_take_eq, ",", expr c.card_boundaries_eq_succ_length, ",", expr composition.boundary, ",", expr fin.ext_iff, ",", expr composition.size_up_to, ",", expr exists_prop, ",", expr finset.mem_univ, ",", expr take, ",", expr exists_prop_of_true, ",", expr finset.mem_image, ",", expr composition_as_set.to_composition_blocks, ",", expr composition.boundaries, "]"] [] [],
  split,
  { rintros ["⟨", ident i, ",", ident hi, "⟩"],
    refine [expr ⟨i.1, _, hi⟩],
    convert [] [expr i.2] [],
    simp [] [] [] [] [] [] },
  { rintros ["⟨", ident i, ",", ident i_lt, ",", ident hi, "⟩"],
    have [] [":", expr «expr < »(i, «expr + »(c.to_composition.length, 1))] [],
    by simpa [] [] [] [] [] ["using", expr i_lt],
    exact [expr ⟨⟨i, this⟩, hi⟩] }
end

@[simp]
theorem Composition.to_composition_as_set_boundaries (c : Composition n) :
  c.to_composition_as_set.boundaries = c.boundaries :=
  rfl

/-- Equivalence between `composition n` and `composition_as_set n`. -/
def compositionEquiv (n : ℕ) : Composition n ≃ CompositionAsSet n :=
  { toFun := fun c => c.to_composition_as_set, invFun := fun c => c.to_composition,
    left_inv :=
      fun c =>
        by 
          ext1 
          exact c.to_composition_as_set_blocks,
    right_inv :=
      fun c =>
        by 
          ext1 
          exact c.to_composition_boundaries }

instance compositionFintype (n : ℕ) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm

theorem composition_card (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) :=
  by 
    rw [←composition_as_set_card n]
    exact Fintype.card_congr (compositionEquiv n)

