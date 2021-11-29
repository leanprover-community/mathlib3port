import Mathbin.Data.Ordmap.Ordnode 
import Mathbin.Algebra.Order.Ring 
import Mathbin.Data.Nat.Dist 
import Mathbin.Tactic.Linarith.Default

/-!
# Verification of the `ordnode α` datatype

This file proves the correctness of the operations in `data.ordmap.ordnode`.
The public facing version is the type `ordset α`, which is a wrapper around
`ordnode α` which includes the correctness invariant of the type, and it exposes
parallel operations like `insert` as functions on `ordset` that do the same
thing but bundle the correctness proofs. The advantage is that it is possible
to, for example, prove that the result of `find` on `insert` will actually find
the element, while `ordnode` cannot guarantee this if the input tree did not
satisfy the type invariants.

## Main definitions

* `ordset α`: A well formed set of values of type `α`

## Implementation notes

The majority of this file is actually in the `ordnode` namespace, because we first
have to prove the correctness of all the operations (and defining what correctness
means here is actually somewhat subtle). So all the actual `ordset` operations are
at the very end, once we have all the theorems.

An `ordnode α` is an inductive type which describes a tree which stores the `size` at
internal nodes. The correctness invariant of an `ordnode α` is:

* `ordnode.sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `ordnode.balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `ordnode.bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬ (b ≤ a)`. We enforce this using `ordnode.bounded` which includes also a global
  upper and lower bound.

Because the `ordnode` file was ported from Haskell, the correctness invariants of some
of the functions have not been spelled out, and some theorems like
`ordnode.valid'.balance_l_aux` show very intricate assumptions on the sizes,
which may need to be revised if it turns out some operations violate these assumptions,
because there is a decent amount of slop in the actual data structure invariants, so the
theorem will go through with multiple choices of assumption.

**Note:** This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming

-/


variable{α : Type _}

namespace Ordnode

/-! ### delta and ratio -/


theorem not_le_delta {s} (H : 1 ≤ s) : ¬s ≤ delta*0 :=
  not_le_of_gtₓ H

theorem delta_lt_false {a b : ℕ} (h₁ : (delta*a) < b) (h₂ : (delta*b) < a) : False :=
  not_le_of_lt
      (lt_transₓ
        ((mul_lt_mul_left
              (by 
                decide)).2
          h₁)
        h₂)$
    by 
      simpa [mul_assocₓ] using
        Nat.mul_le_mul_rightₓ a
          (by 
            decide :
          1 ≤ delta*delta)

/-! ### `singleton` -/


/-! ### `size` and `empty` -/


/-- O(n). Computes the actual number of elements in the set, ignoring the cached `size` field. -/
def real_size : Ordnode α → ℕ
| nil => 0
| node _ l _ r => (real_size l+real_size r)+1

/-! ### `sized` -/


/-- The `sized` property asserts that all the `size` fields in nodes match the actual size of the
respective subtrees. -/
def sized : Ordnode α → Prop
| nil => True
| node s l _ r => (s = (size l+size r)+1) ∧ sized l ∧ sized r

theorem sized.node' {l x r} (hl : @sized α l) (hr : sized r) : sized (node' l x r) :=
  ⟨rfl, hl, hr⟩

theorem sized.eq_node' {s l x r} (h : @sized α (node s l x r)) : node s l x r = node' l x r :=
  by 
    rw [h.1] <;> rfl

theorem sized.size_eq {s l x r} (H : sized (@node α s l x r)) : size (@node α s l x r) = (size l+size r)+1 :=
  H.1

@[elab_as_eliminator]
theorem sized.induction {t} (hl : @sized α t) {C : Ordnode α → Prop} (H0 : C nil)
  (H1 : ∀ l x r, C l → C r → C (node' l x r)) : C t :=
  by 
    induction t
    ·
      exact H0 
    rw [hl.eq_node']
    exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)

theorem size_eq_real_size : ∀ {t : Ordnode α}, sized t → size t = real_size t
| nil, _ => rfl
| node s l x r, ⟨h₁, h₂, h₃⟩ =>
  by 
    rw [size, h₁, size_eq_real_size h₂, size_eq_real_size h₃] <;> rfl

@[simp]
theorem sized.size_eq_zero {t : Ordnode α} (ht : sized t) : size t = 0 ↔ t = nil :=
  by 
    cases t <;> [simp , simp [ht.1]]

theorem sized.pos {s l x r} (h : sized (@node α s l x r)) : 0 < s :=
  by 
    rw [h.1] <;> apply Nat.le_add_leftₓ

/-! `dual` -/


theorem dual_dual : ∀ (t : Ordnode α), dual (dual t) = t
| nil => rfl
| node s l x r =>
  by 
    rw [dual, dual, dual_dual, dual_dual]

@[simp]
theorem size_dual (t : Ordnode α) : size (dual t) = size t :=
  by 
    cases t <;> rfl

/-! `balanced` -/


/-- The `balanced_sz l r` asserts that a hypothetical tree with children of sizes `l` and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a singleton on one side
and nothing on the other. -/
def balanced_sz (l r : ℕ) : Prop :=
  (l+r) ≤ 1 ∨ (l ≤ delta*r) ∧ r ≤ delta*l

instance balanced_sz.dec : DecidableRel balanced_sz :=
  fun l r => Or.decidable

/-- The `balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level). -/
def balanced : Ordnode α → Prop
| nil => True
| node _ l _ r => balanced_sz (size l) (size r) ∧ balanced l ∧ balanced r

instance balanced.dec : DecidablePred (@balanced α)
| t =>
  by 
    induction t <;> unfold balanced <;> skip <;> infer_instance

theorem balanced_sz.symm {l r : ℕ} : balanced_sz l r → balanced_sz r l :=
  Or.imp
    (by 
      rw [add_commₓ] <;> exact id)
    And.symm

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem balanced_sz_zero {l : exprℕ()} : «expr ↔ »(balanced_sz l 0, «expr ≤ »(l, 1)) :=
by simp [] [] [] ["[", expr balanced_sz, "]"] [] [] { contextual := tt }

theorem balanced_sz_up {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : (l+r₂) ≤ 1 ∨ r₂ ≤ delta*l) (H : balanced_sz l r₁) :
  balanced_sz l r₂ :=
  by 
    refine' or_iff_not_imp_left.2 fun h => _ 
    refine' ⟨_, h₂.resolve_left h⟩
    cases H
    ·
      cases r₂
      ·
        cases h (le_transₓ (Nat.add_le_add_leftₓ (Nat.zero_leₓ _) _) H)
      ·
        exact le_transₓ (le_transₓ (Nat.le_add_rightₓ _ _) H) (Nat.le_add_leftₓ 1 _)
    ·
      exact le_transₓ H.1 (Nat.mul_le_mul_leftₓ _ h₁)

theorem balanced_sz_down {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : (l+r₂) ≤ 1 ∨ l ≤ delta*r₁) (H : balanced_sz l r₂) :
  balanced_sz l r₁ :=
  have  : (l+r₂) ≤ 1 → balanced_sz l r₁ := fun H => Or.inl (le_transₓ (Nat.add_le_add_leftₓ h₁ _) H)
  Or.cases_on H this fun H => Or.cases_on h₂ this fun h₂ => Or.inr ⟨h₂, le_transₓ h₁ H.2⟩

theorem balanced.dual : ∀ {t : Ordnode α}, balanced t → balanced (dual t)
| nil, h => ⟨⟩
| node s l x r, ⟨b, bl, br⟩ =>
  ⟨by 
      rw [size_dual, size_dual] <;> exact b.symm,
    br.dual, bl.dual⟩

/-! ### `rotate` and `balance` -/


/-- Build a tree from three nodes, left associated (ignores the invariants). -/
def node3_l (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' (node' l x m) y r

/-- Build a tree from three nodes, right associated (ignores the invariants). -/
def node3_r (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' l x (node' m y r)

/-- Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b) (c d))`. -/
def node4_l : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
| l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
| l, x, nil, z, r => node3_l l x nil z r

/-- Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b) (c d))`. -/
def node4_r : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
| l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
| l, x, nil, z, r => node3_r l x nil z r

/-- Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset. -/
def rotate_l : Ordnode α → α → Ordnode α → Ordnode α
| l, x, node _ m y r => if size m < ratio*size r then node3_l l x m y r else node4_l l x m y r
| l, x, nil => node' l x nil

/-- Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset. -/
def rotate_r : Ordnode α → α → Ordnode α → Ordnode α
| node _ l x m, y, r => if size m < ratio*size l then node3_r l x m y r else node4_r l x m y r
| nil, y, r => node' nil y r

/-- A left balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balance_l' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if (size l+size r) ≤ 1 then node' l x r else if size l > delta*size r then rotate_r l x r else node' l x r

/-- A right balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
def balance_r' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if (size l+size r) ≤ 1 then node' l x r else if size r > delta*size l then rotate_l l x r else node' l x r

/-- The full balance operation. This is the same as `balance`, but with less manual inlining.
It is somewhat easier to work with this version in proofs. -/
def balance' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if (size l+size r) ≤ 1 then node' l x r else
    if size r > delta*size l then rotate_l l x r else if size l > delta*size r then rotate_r l x r else node' l x r

theorem dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) : dual (node' l x r) = node' (dual r) x (dual l) :=
  by 
    simp [node', add_commₓ]

theorem dual_node3_l (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
  dual (node3_l l x m y r) = node3_r (dual r) y (dual m) x (dual l) :=
  by 
    simp [node3_l, node3_r, dual_node']

theorem dual_node3_r (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
  dual (node3_r l x m y r) = node3_l (dual r) y (dual m) x (dual l) :=
  by 
    simp [node3_l, node3_r, dual_node']

theorem dual_node4_l (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
  dual (node4_l l x m y r) = node4_r (dual r) y (dual m) x (dual l) :=
  by 
    cases m <;> simp [node4_l, node4_r, dual_node3_l, dual_node']

theorem dual_node4_r (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
  dual (node4_r l x m y r) = node4_l (dual r) y (dual m) x (dual l) :=
  by 
    cases m <;> simp [node4_l, node4_r, dual_node3_r, dual_node']

theorem dual_rotate_l (l : Ordnode α) (x : α) (r : Ordnode α) : dual (rotate_l l x r) = rotate_r (dual r) x (dual l) :=
  by 
    cases r <;> simp [rotate_l, rotate_r, dual_node'] <;> splitIfs <;> simp [dual_node3_l, dual_node4_l]

theorem dual_rotate_r (l : Ordnode α) (x : α) (r : Ordnode α) : dual (rotate_r l x r) = rotate_l (dual r) x (dual l) :=
  by 
    rw [←dual_dual (rotate_l _ _ _), dual_rotate_l, dual_dual, dual_dual]

theorem dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balance' l x r) = balance' (dual r) x (dual l) :=
  by 
    simp [balance', add_commₓ]
    splitIfs <;> simp [dual_node', dual_rotate_l, dual_rotate_r]
    cases delta_lt_false h_1 h_2

theorem dual_balance_l (l : Ordnode α) (x : α) (r : Ordnode α) :
  dual (balance_l l x r) = balance_r (dual r) x (dual l) :=
  by 
    unfold balance_l balance_r 
    cases' r with rs rl rx rr
    ·
      cases' l with ls ll lx lr
      ·
        rfl 
      cases' ll with lls lll llx llr <;>
        cases' lr with lrs lrl lrx lrr <;>
          dsimp only [dual] <;>
            try 
              rfl 
      splitIfs <;>
        repeat' 
          simp [h, add_commₓ]
    ·
      cases' l with ls ll lx lr
      ·
        rfl 
      dsimp only [dual]
      splitIfs 
      swap
      ·
        simp [add_commₓ]
      cases' ll with lls lll llx llr <;>
        cases' lr with lrs lrl lrx lrr <;>
          try 
            rfl 
      dsimp only [dual]
      splitIfs <;> simp [h, add_commₓ]

theorem dual_balance_r (l : Ordnode α) (x : α) (r : Ordnode α) :
  dual (balance_r l x r) = balance_l (dual r) x (dual l) :=
  by 
    rw [←dual_dual (balance_l _ _ _), dual_balance_l, dual_dual, dual_dual]

theorem sized.node3_l {l x m y r} (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node3_l l x m y r) :=
  (hl.node' hm).node' hr

theorem sized.node3_r {l x m y r} (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node3_r l x m y r) :=
  hl.node' (hm.node' hr)

theorem sized.node4_l {l x m y r} (hl : @sized α l) (hm : sized m) (hr : sized r) : sized (node4_l l x m y r) :=
  by 
    cases m <;> [exact (hl.node' hm).node' hr, exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]

theorem node3_l_size {l x m y r} : size (@node3_l α l x m y r) = ((size l+size m)+size r)+2 :=
  by 
    dsimp [node3_l, node', size] <;> rw [add_right_commₓ _ 1]

theorem node3_r_size {l x m y r} : size (@node3_r α l x m y r) = ((size l+size m)+size r)+2 :=
  by 
    dsimp [node3_r, node', size] <;> rw [←add_assocₓ, ←add_assocₓ]

theorem node4_l_size {l x m y r} (hm : sized m) : size (@node4_l α l x m y r) = ((size l+size m)+size r)+2 :=
  by 
    cases m <;>
      simp [node4_l, node3_l, node', add_commₓ, add_left_commₓ] <;> [skip, simp [size, hm.1]] <;>
        rw [←add_assocₓ, ←bit0] <;> simp [add_commₓ, add_left_commₓ]

theorem sized.dual : ∀ {t : Ordnode α} (h : sized t), sized (dual t)
| nil, h => ⟨⟩
| node s l x r, ⟨rfl, sl, sr⟩ =>
  ⟨by 
      simp [size_dual, add_commₓ],
    sized.dual sr, sized.dual sl⟩

theorem sized.dual_iff {t : Ordnode α} : sized (dual t) ↔ sized t :=
  ⟨fun h =>
      by 
        rw [←dual_dual t] <;> exact h.dual,
    sized.dual⟩

theorem sized.rotate_l {l x r} (hl : @sized α l) (hr : sized r) : sized (rotate_l l x r) :=
  by 
    cases r
    ·
      exact hl.node' hr 
    rw [rotate_l]
    splitIfs
    ·
      exact hl.node3_l hr.2.1 hr.2.2
    ·
      exact hl.node4_l hr.2.1 hr.2.2

theorem sized.rotate_r {l x r} (hl : @sized α l) (hr : sized r) : sized (rotate_r l x r) :=
  sized.dual_iff.1$
    by 
      rw [dual_rotate_r] <;> exact hr.dual.rotate_l hl.dual

theorem sized.rotate_l_size {l x r} (hm : sized r) : size (@rotate_l α l x r) = (size l+size r)+1 :=
  by 
    cases r <;> simp [rotate_l]
    simp [size, hm.1, add_commₓ, add_left_commₓ]
    rw [←add_assocₓ, ←bit0]
    simp 
    splitIfs <;> simp [node3_l_size, node4_l_size hm.2.1, add_commₓ, add_left_commₓ]

theorem sized.rotate_r_size {l x r} (hl : sized l) : size (@rotate_r α l x r) = (size l+size r)+1 :=
  by 
    rw [←size_dual, dual_rotate_r, hl.dual.rotate_l_size, size_dual, size_dual, add_commₓ (size l)]

theorem sized.balance' {l x r} (hl : @sized α l) (hr : sized r) : sized (balance' l x r) :=
  by 
    unfold balance' 
    splitIfs
    ·
      exact hl.node' hr
    ·
      exact hl.rotate_l hr
    ·
      exact hl.rotate_r hr
    ·
      exact hl.node' hr

theorem size_balance' {l x r} (hl : @sized α l) (hr : sized r) : size (@balance' α l x r) = (size l+size r)+1 :=
  by 
    unfold balance' 
    splitIfs
    ·
      rfl
    ·
      exact hr.rotate_l_size
    ·
      exact hl.rotate_r_size
    ·
      rfl

/-! ## `all`, `any`, `emem`, `amem` -/


theorem all.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, all P t → all Q t
| nil, h => ⟨⟩
| node _ l x r, ⟨h₁, h₂, h₃⟩ => ⟨h₁.imp, H _ h₂, h₃.imp⟩

theorem any.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, any P t → any Q t
| nil => id
| node _ l x r => Or.imp any.imp$ Or.imp (H _) any.imp

theorem all_singleton {P : α → Prop} {x : α} : all P (singleton x) ↔ P x :=
  ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩

theorem any_singleton {P : α → Prop} {x : α} : any P (singleton x) ↔ P x :=
  ⟨by 
      rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩) <;> exact h,
    fun h => Or.inr (Or.inl h)⟩

theorem all_dual {P : α → Prop} : ∀ {t : Ordnode α}, all P (dual t) ↔ all P t
| nil => Iff.rfl
| node s l x r =>
  ⟨fun ⟨hr, hx, hl⟩ => ⟨all_dual.1 hl, hx, all_dual.1 hr⟩, fun ⟨hl, hx, hr⟩ => ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩

theorem all_iff_forall {P : α → Prop} : ∀ {t}, all P t ↔ ∀ x, emem x t → P x
| nil =>
  (iff_true_intro$
      by 
        rintro _ ⟨⟩).symm
| node _ l x r =>
  by 
    simp [all, emem, all_iff_forall, any, or_imp_distrib, forall_and_distrib]

theorem any_iff_exists {P : α → Prop} : ∀ {t}, any P t ↔ ∃ x, emem x t ∧ P x
| nil =>
  ⟨by 
      rintro ⟨⟩,
    by 
      rintro ⟨_, ⟨⟩, _⟩⟩
| node _ l x r =>
  by 
    simp [any, emem, any_iff_exists, or_and_distrib_right, exists_or_distrib]

theorem emem_iff_all {x : α} {t} : emem x t ↔ ∀ P, all P t → P x :=
  ⟨fun h P al => all_iff_forall.1 al _ h, fun H => H _$ all_iff_forall.2$ fun _ => id⟩

theorem all_node' {P l x r} : @all α P (node' l x r) ↔ all P l ∧ P x ∧ all P r :=
  Iff.rfl

theorem all_node3_l {P l x m y r} : @all α P (node3_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  by 
    simp [node3_l, all_node', and_assoc]

theorem all_node3_r {P l x m y r} : @all α P (node3_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  Iff.rfl

theorem all_node4_l {P l x m y r} : @all α P (node4_l l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  by 
    cases m <;> simp [node4_l, all_node', all, all_node3_l, and_assoc]

theorem all_node4_r {P l x m y r} : @all α P (node4_r l x m y r) ↔ all P l ∧ P x ∧ all P m ∧ P y ∧ all P r :=
  by 
    cases m <;> simp [node4_r, all_node', all, all_node3_r, and_assoc]

theorem all_rotate_l {P l x r} : @all α P (rotate_l l x r) ↔ all P l ∧ P x ∧ all P r :=
  by 
    cases r <;> simp [rotate_l, all_node'] <;> splitIfs <;> simp [all_node3_l, all_node4_l, all]

theorem all_rotate_r {P l x r} : @all α P (rotate_r l x r) ↔ all P l ∧ P x ∧ all P r :=
  by 
    rw [←all_dual, dual_rotate_r, all_rotate_l] <;> simp [all_dual, and_comm, And.left_comm]

theorem all_balance' {P l x r} : @all α P (balance' l x r) ↔ all P l ∧ P x ∧ all P r :=
  by 
    rw [balance'] <;> splitIfs <;> simp [all_node', all_rotate_l, all_rotate_r]

/-! ### `to_list` -/


theorem foldr_cons_eq_to_list : ∀ (t : Ordnode α) (r : List α), t.foldr List.cons r = to_list t ++ r
| nil, r => rfl
| node _ l x r, r' =>
  by 
    rw [foldr, foldr_cons_eq_to_list, foldr_cons_eq_to_list, ←List.cons_append, ←List.append_assoc,
        ←foldr_cons_eq_to_list] <;>
      rfl

@[simp]
theorem to_list_nil : to_list (@nil α) = [] :=
  rfl

@[simp]
theorem to_list_node s l x r : to_list (@node α s l x r) = to_list l ++ x :: to_list r :=
  by 
    rw [to_list, foldr, foldr_cons_eq_to_list] <;> rfl

theorem emem_iff_mem_to_list {x : α} {t} : emem x t ↔ x ∈ to_list t :=
  by 
    unfold emem <;> induction t <;> simp [any, or_assoc]

theorem length_to_list' : ∀ (t : Ordnode α), (to_list t).length = t.real_size
| nil => rfl
| node _ l _ r =>
  by 
    rw [to_list_node, List.length_append, List.length_cons, length_to_list', length_to_list'] <;> rfl

theorem length_to_list {t : Ordnode α} (h : sized t) : (to_list t).length = t.size :=
  by 
    rw [length_to_list', size_eq_real_size h]

theorem equiv_iff {t₁ t₂ : Ordnode α} (h₁ : sized t₁) (h₂ : sized t₂) : Equiv t₁ t₂ ↔ to_list t₁ = to_list t₂ :=
  and_iff_right_of_imp$
    fun h =>
      by 
        rw [←length_to_list h₁, h, length_to_list h₂]

/-! ### `mem` -/


theorem pos_size_of_mem [LE α] [@DecidableRel α (· ≤ ·)] {x : α} {t : Ordnode α} (h : sized t) (h_mem : x ∈ t) :
  0 < size t :=
  by 
    cases t
    ·
      contradiction
    ·
      simp [h.1]

/-! ### `(find/erase/split)_(min/max)` -/


theorem find_min'_dual : ∀ t (x : α), find_min' (dual t) x = find_max' x t
| nil, x => rfl
| node _ l x r, _ => find_min'_dual r x

theorem find_max'_dual t (x : α) : find_max' x (dual t) = find_min' t x :=
  by 
    rw [←find_min'_dual, dual_dual]

theorem find_min_dual : ∀ (t : Ordnode α), find_min (dual t) = find_max t
| nil => rfl
| node _ l x r => congr_argₓ some$ find_min'_dual _ _

theorem find_max_dual (t : Ordnode α) : find_max (dual t) = find_min t :=
  by 
    rw [←find_min_dual, dual_dual]

theorem dual_erase_min : ∀ (t : Ordnode α), dual (erase_min t) = erase_max (dual t)
| nil => rfl
| node _ nil x r => rfl
| node _ (l@(node _ _ _ _)) x r =>
  by 
    rw [erase_min, dual_balance_r, dual_erase_min, dual, dual, dual, erase_max]

theorem dual_erase_max (t : Ordnode α) : dual (erase_max t) = erase_min (dual t) :=
  by 
    rw [←dual_dual (erase_min _), dual_erase_min, dual_dual]

theorem split_min_eq : ∀ s l (x : α) r, split_min' l x r = (find_min' l x, erase_min (node s l x r))
| _, nil, x, r => rfl
| _, node ls ll lx lr, x, r =>
  by 
    rw [split_min', split_min_eq, split_min', find_min', erase_min]

theorem split_max_eq : ∀ s l (x : α) r, split_max' l x r = (erase_max (node s l x r), find_max' x r)
| _, l, x, nil => rfl
| _, l, x, node ls ll lx lr =>
  by 
    rw [split_max', split_max_eq, split_max', find_max', erase_max]

@[elab_as_eliminator]
theorem find_min'_all {P : α → Prop} : ∀ t (x : α), all P t → P x → P (find_min' t x)
| nil, x, h, hx => hx
| node _ ll lx lr, x, ⟨h₁, h₂, h₃⟩, hx => find_min'_all _ _ h₁ h₂

@[elab_as_eliminator]
theorem find_max'_all {P : α → Prop} : ∀ (x : α) t, P x → all P t → P (find_max' x t)
| x, nil, hx, h => hx
| x, node _ ll lx lr, hx, ⟨h₁, h₂, h₃⟩ => find_max'_all _ _ h₂ h₃

/-! ### `glue` -/


/-! ### `merge` -/


@[simp]
theorem merge_nil_left (t : Ordnode α) : merge t nil = t :=
  by 
    cases t <;> rfl

@[simp]
theorem merge_nil_right (t : Ordnode α) : merge nil t = t :=
  rfl

@[simp]
theorem merge_node {ls ll lx lr rs rl rx rr} :
  merge (@node α ls ll lx lr) (node rs rl rx rr) =
    if (delta*ls) < rs then balance_l (merge (node ls ll lx lr) rl) rx rr else
      if (delta*rs) < ls then balance_r ll lx (merge lr (node rs rl rx rr)) else
        glue (node ls ll lx lr) (node rs rl rx rr) :=
  rfl

/-! ### `insert` -/


theorem dual_insert [Preorderₓ α] [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) :
  ∀ (t : Ordnode α), dual (Ordnode.insert x t) = @Ordnode.insert (OrderDual α) _ _ x (dual t)
| nil => rfl
| node _ l y r =>
  by 
    rw [Ordnode.insert, dual, Ordnode.insert, OrderDual.cmp_le_flip, ←cmp_le_swap x y]
    cases cmpLe x y <;> simp [Ordering.swap, Ordnode.insert, dual_balance_l, dual_balance_r, dual_insert]

/-! ### `balance` properties -/


-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem balance_eq_balance'
{l x r}
(hl : balanced l)
(hr : balanced r)
(sl : sized l)
(sr : sized r) : «expr = »(@balance α l x r, balance' l x r) :=
begin
  cases [expr l] ["with", ident ls, ident ll, ident lx, ident lr],
  { cases [expr r] ["with", ident rs, ident rl, ident rx, ident rr],
    { refl },
    { rw [expr sr.eq_node'] ["at", ident hr, "⊢"],
      cases [expr rl] ["with", ident rls, ident rll, ident rlx, ident rlr]; cases [expr rr] ["with", ident rrs, ident rrl, ident rrx, ident rrr]; dsimp [] ["[", expr balance, ",", expr balance', "]"] [] [],
      { refl },
      { have [] [":", expr «expr ∧ »(«expr = »(size rrl, 0), «expr = »(size rrr, 0))] [],
        { have [] [] [":=", expr balanced_sz_zero.1 hr.1.symm],
          rwa ["[", expr size, ",", expr sr.2.2.1, ",", expr nat.succ_le_succ_iff, ",", expr nat.le_zero_iff, ",", expr add_eq_zero_iff, "]"] ["at", ident this] },
        cases [expr sr.2.2.2.1.size_eq_zero.1 this.1] [],
        cases [expr sr.2.2.2.2.size_eq_zero.1 this.2] [],
        have [] [":", expr «expr = »(rrs, 1)] [":=", expr sr.2.2.1],
        subst [expr rrs],
        rw ["[", expr if_neg, ",", expr if_pos, ",", expr rotate_l, ",", expr if_pos, "]"] [],
        { refl },
        all_goals { exact [expr exprdec_trivial()] } },
      { have [] [":", expr «expr ∧ »(«expr = »(size rll, 0), «expr = »(size rlr, 0))] [],
        { have [] [] [":=", expr balanced_sz_zero.1 hr.1],
          rwa ["[", expr size, ",", expr sr.2.1.1, ",", expr nat.succ_le_succ_iff, ",", expr nat.le_zero_iff, ",", expr add_eq_zero_iff, "]"] ["at", ident this] },
        cases [expr sr.2.1.2.1.size_eq_zero.1 this.1] [],
        cases [expr sr.2.1.2.2.size_eq_zero.1 this.2] [],
        have [] [":", expr «expr = »(rls, 1)] [":=", expr sr.2.1.1],
        subst [expr rls],
        rw ["[", expr if_neg, ",", expr if_pos, ",", expr rotate_l, ",", expr if_neg, "]"] [],
        { refl },
        all_goals { exact [expr exprdec_trivial()] } },
      { symmetry,
        rw ["[", expr zero_add, ",", expr if_neg, ",", expr if_pos, ",", expr rotate_l, "]"] [],
        { split_ifs [] [],
          { simp [] [] [] ["[", expr node3_l, ",", expr node', ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
          { simp [] [] [] ["[", expr node4_l, ",", expr node', ",", expr sr.2.1.1, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] } },
        { exact [expr exprdec_trivial()] },
        { exact [expr not_le_of_gt (nat.succ_lt_succ (add_pos sr.2.1.pos sr.2.2.pos))] } } } },
  { cases [expr r] ["with", ident rs, ident rl, ident rx, ident rr],
    { rw [expr sl.eq_node'] ["at", ident hl, "⊢"],
      cases [expr ll] ["with", ident lls, ident lll, ident llx, ident llr]; cases [expr lr] ["with", ident lrs, ident lrl, ident lrx, ident lrr]; dsimp [] ["[", expr balance, ",", expr balance', "]"] [] [],
      { refl },
      { have [] [":", expr «expr ∧ »(«expr = »(size lrl, 0), «expr = »(size lrr, 0))] [],
        { have [] [] [":=", expr balanced_sz_zero.1 hl.1.symm],
          rwa ["[", expr size, ",", expr sl.2.2.1, ",", expr nat.succ_le_succ_iff, ",", expr nat.le_zero_iff, ",", expr add_eq_zero_iff, "]"] ["at", ident this] },
        cases [expr sl.2.2.2.1.size_eq_zero.1 this.1] [],
        cases [expr sl.2.2.2.2.size_eq_zero.1 this.2] [],
        have [] [":", expr «expr = »(lrs, 1)] [":=", expr sl.2.2.1],
        subst [expr lrs],
        rw ["[", expr if_neg, ",", expr if_neg, ",", expr if_pos, ",", expr rotate_r, ",", expr if_neg, "]"] [],
        { refl },
        all_goals { exact [expr exprdec_trivial()] } },
      { have [] [":", expr «expr ∧ »(«expr = »(size lll, 0), «expr = »(size llr, 0))] [],
        { have [] [] [":=", expr balanced_sz_zero.1 hl.1],
          rwa ["[", expr size, ",", expr sl.2.1.1, ",", expr nat.succ_le_succ_iff, ",", expr nat.le_zero_iff, ",", expr add_eq_zero_iff, "]"] ["at", ident this] },
        cases [expr sl.2.1.2.1.size_eq_zero.1 this.1] [],
        cases [expr sl.2.1.2.2.size_eq_zero.1 this.2] [],
        have [] [":", expr «expr = »(lls, 1)] [":=", expr sl.2.1.1],
        subst [expr lls],
        rw ["[", expr if_neg, ",", expr if_neg, ",", expr if_pos, ",", expr rotate_r, ",", expr if_pos, "]"] [],
        { refl },
        all_goals { exact [expr exprdec_trivial()] } },
      { symmetry,
        rw ["[", expr if_neg, ",", expr if_neg, ",", expr if_pos, ",", expr rotate_r, "]"] [],
        { split_ifs [] [],
          { simp [] [] [] ["[", expr node3_r, ",", expr node', ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
          { simp [] [] [] ["[", expr node4_r, ",", expr node', ",", expr sl.2.2.1, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] } },
        { exact [expr exprdec_trivial()] },
        { exact [expr exprdec_trivial()] },
        { exact [expr not_le_of_gt (nat.succ_lt_succ (add_pos sl.2.1.pos sl.2.2.pos))] } } },
    { simp [] [] [] ["[", expr balance, ",", expr balance', "]"] [] [],
      symmetry,
      rw ["[", expr if_neg, "]"] [],
      { split_ifs [] [],
        { have [ident rd] [":", expr «expr ≤ »(delta, «expr + »(size rl, size rr))] [],
          { have [] [] [":=", expr lt_of_le_of_lt (nat.mul_le_mul_left _ sl.pos) h],
            rwa ["[", expr sr.1, ",", expr nat.lt_succ_iff, "]"] ["at", ident this] },
          cases [expr rl] ["with", ident rls, ident rll, ident rlx, ident rlr],
          { rw ["[", expr size, ",", expr zero_add, "]"] ["at", ident rd],
            exact [expr absurd (le_trans rd (balanced_sz_zero.1 hr.1.symm)) exprdec_trivial()] },
          cases [expr rr] ["with", ident rrs, ident rrl, ident rrx, ident rrr],
          { exact [expr absurd (le_trans rd (balanced_sz_zero.1 hr.1)) exprdec_trivial()] },
          dsimp [] ["[", expr rotate_l, "]"] [] [],
          split_ifs [] [],
          { simp [] [] [] ["[", expr node3_l, ",", expr node', ",", expr sr.1, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
          { simp [] [] [] ["[", expr node4_l, ",", expr node', ",", expr sr.1, ",", expr sr.2.1.1, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] } },
        { have [ident ld] [":", expr «expr ≤ »(delta, «expr + »(size ll, size lr))] [],
          { have [] [] [":=", expr lt_of_le_of_lt (nat.mul_le_mul_left _ sr.pos) h_1],
            rwa ["[", expr sl.1, ",", expr nat.lt_succ_iff, "]"] ["at", ident this] },
          cases [expr ll] ["with", ident lls, ident lll, ident llx, ident llr],
          { rw ["[", expr size, ",", expr zero_add, "]"] ["at", ident ld],
            exact [expr absurd (le_trans ld (balanced_sz_zero.1 hl.1.symm)) exprdec_trivial()] },
          cases [expr lr] ["with", ident lrs, ident lrl, ident lrx, ident lrr],
          { exact [expr absurd (le_trans ld (balanced_sz_zero.1 hl.1)) exprdec_trivial()] },
          dsimp [] ["[", expr rotate_r, "]"] [] [],
          split_ifs [] [],
          { simp [] [] [] ["[", expr node3_r, ",", expr node', ",", expr sl.1, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
          { simp [] [] [] ["[", expr node4_r, ",", expr node', ",", expr sl.1, ",", expr sl.2.2.1, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] } },
        { simp [] [] [] ["[", expr node', "]"] [] [] } },
      { exact [expr not_le_of_gt (add_le_add sl.pos sr.pos : «expr ≤ »(2, «expr + »(ls, rs)))] } } }
end

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem balance_l_eq_balance
{l x r}
(sl : sized l)
(sr : sized r)
(H1 : «expr = »(size l, 0) → «expr ≤ »(size r, 1))
(H2 : «expr ≤ »(1, size l) → «expr ≤ »(1, size r) → «expr ≤ »(size r, «expr * »(delta, size l))) : «expr = »(@balance_l α l x r, balance l x r) :=
begin
  cases [expr r] ["with", ident rs, ident rl, ident rx, ident rr],
  { refl },
  { cases [expr l] ["with", ident ls, ident ll, ident lx, ident lr],
    { have [] [":", expr «expr ∧ »(«expr = »(size rl, 0), «expr = »(size rr, 0))] [],
      { have [] [] [":=", expr H1 rfl],
        rwa ["[", expr size, ",", expr sr.1, ",", expr nat.succ_le_succ_iff, ",", expr nat.le_zero_iff, ",", expr add_eq_zero_iff, "]"] ["at", ident this] },
      cases [expr sr.2.1.size_eq_zero.1 this.1] [],
      cases [expr sr.2.2.size_eq_zero.1 this.2] [],
      rw [expr sr.eq_node'] [],
      refl },
    { replace [ident H2] [":", expr «expr¬ »(«expr > »(rs, «expr * »(delta, ls)))] [":=", expr not_lt_of_le (H2 sl.pos sr.pos)],
      simp [] [] [] ["[", expr balance_l, ",", expr balance, ",", expr H2, "]"] [] []; split_ifs [] []; simp [] [] [] ["[", expr add_comm, "]"] [] [] } }
end

/-- `raised n m` means `m` is either equal or one up from `n`. -/
def raised (n m : ℕ) : Prop :=
  m = n ∨ m = n+1

theorem raised_iff {n m} : raised n m ↔ n ≤ m ∧ m ≤ n+1 :=
  by 
    split 
    rintro (rfl | rfl)
    ·
      exact ⟨le_reflₓ _, Nat.le_succₓ _⟩
    ·
      exact ⟨Nat.le_succₓ _, le_reflₓ _⟩
    ·
      rintro ⟨h₁, h₂⟩
      rcases eq_or_lt_of_le h₁ with (rfl | h₁)
      ·
        exact Or.inl rfl
      ·
        exact Or.inr (le_antisymmₓ h₂ h₁)

theorem raised.dist_le {n m} (H : raised n m) : Nat.dist n m ≤ 1 :=
  by 
    cases' raised_iff.1 H with H1 H2 <;> rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]

theorem raised.dist_le' {n m} (H : raised n m) : Nat.dist m n ≤ 1 :=
  by 
    rw [Nat.dist_comm] <;> exact H.dist_le

theorem raised.add_left k {n m} (H : raised n m) : raised (k+n) (k+m) :=
  by 
    rcases H with (rfl | rfl)
    ·
      exact Or.inl rfl
    ·
      exact Or.inr rfl

theorem raised.add_right k {n m} (H : raised n m) : raised (n+k) (m+k) :=
  by 
    rw [add_commₓ, add_commₓ m] <;> exact H.add_left _

theorem raised.right {l x₁ x₂ r₁ r₂} (H : raised (size r₁) (size r₂)) :
  raised (size (@node' α l x₁ r₁)) (size (@node' α l x₂ r₂)) :=
  by 
    dsimp [node', size]
    generalize size r₂ = m  at H⊢
    rcases H with (rfl | rfl)
    ·
      exact Or.inl rfl
    ·
      exact Or.inr rfl

theorem balance_l_eq_balance' {l x r} (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨ ∃ r', raised (size r) r' ∧ balanced_sz (size l) r') :
  @balance_l α l x r = balance' l x r :=
  by 
    rw [←balance_eq_balance' hl hr sl sr, balance_l_eq_balance sl sr]
    ·
      intro l0 
      rw [l0] at H 
      rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
      ·
        exact balanced_sz_zero.1 H.symm 
      exact le_transₓ (raised_iff.1 e).1 (balanced_sz_zero.1 H.symm)
    ·
      intro l1 r1 
      rcases H with (⟨l', e, H | ⟨H₁, H₂⟩⟩ | ⟨r', e, H | ⟨H₁, H₂⟩⟩)
      ·
        exact
          le_transₓ (le_transₓ (Nat.le_add_leftₓ _ _) H)
            (mul_pos
              (by 
                decide)
              l1 :
            (0 : ℕ) < _)
      ·
        exact le_transₓ H₂ (Nat.mul_le_mul_leftₓ _ (raised_iff.1 e).1)
      ·
        cases raised_iff.1 e 
        unfold delta 
        linarith
      ·
        exact le_transₓ (raised_iff.1 e).1 H₂

theorem balance_sz_dual {l r}
  (H :
    (∃ l', raised (@size α l) l' ∧ balanced_sz l' (@size α r)) ∨ ∃ r', raised r' (size r) ∧ balanced_sz (size l) r') :
  (∃ l', raised l' (size (dual r)) ∧ balanced_sz l' (size (dual l))) ∨
    ∃ r', raised (size (dual l)) r' ∧ balanced_sz (size (dual r)) r' :=
  by 
    rw [size_dual, size_dual]
    exact
      H.symm.imp (Exists.impₓ$ fun _ => And.imp_right balanced_sz.symm)
        (Exists.impₓ$ fun _ => And.imp_right balanced_sz.symm)

theorem size_balance_l {l x r} (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨ ∃ r', raised (size r) r' ∧ balanced_sz (size l) r') :
  size (@balance_l α l x r) = (size l+size r)+1 :=
  by 
    rw [balance_l_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balance_l {P l x r} (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨ ∃ r', raised (size r) r' ∧ balanced_sz (size l) r') :
  all P (@balance_l α l x r) ↔ all P l ∧ P x ∧ all P r :=
  by 
    rw [balance_l_eq_balance' hl hr sl sr H, all_balance']

theorem balance_r_eq_balance' {l x r} (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨ ∃ r', raised r' (size r) ∧ balanced_sz (size l) r') :
  @balance_r α l x r = balance' l x r :=
  by 
    rw [←dual_dual (balance_r l x r), dual_balance_r,
      balance_l_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H), ←dual_balance', dual_dual]

theorem size_balance_r {l x r} (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨ ∃ r', raised r' (size r) ∧ balanced_sz (size l) r') :
  size (@balance_r α l x r) = (size l+size r)+1 :=
  by 
    rw [balance_r_eq_balance' hl hr sl sr H, size_balance' sl sr]

theorem all_balance_r {P l x r} (hl : balanced l) (hr : balanced r) (sl : sized l) (sr : sized r)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨ ∃ r', raised r' (size r) ∧ balanced_sz (size l) r') :
  all P (@balance_r α l x r) ↔ all P l ∧ P x ∧ all P r :=
  by 
    rw [balance_r_eq_balance' hl hr sl sr H, all_balance']

/-! ### `bounded` -/


section 

variable[Preorderₓ α]

/-- `bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`, and also this
property holds recursively in subtrees, making the full tree a BST. The bounds can be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints. -/
def Bounded : Ordnode α → WithBot α → WithTop α → Prop
| nil, some a, some b => a < b
| nil, _, _ => True
| node _ l x r, o₁, o₂ => Bounded l o₁ («expr↑ » x) ∧ Bounded r («expr↑ » x) o₂

theorem bounded.dual : ∀ {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂), @Bounded (OrderDual α) _ (dual t) o₂ o₁
| nil, o₁, o₂, h =>
  by 
    cases o₁ <;>
      cases o₂ <;>
        try 
            trivial <;>
          exact h
| node s l x r, _, _, ⟨ol, Or⟩ => ⟨or.dual, ol.dual⟩

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bounded.dual_iff
{t : ordnode α}
{o₁ o₂} : «expr ↔ »(bounded t o₁ o₂, @bounded (order_dual α) _ (dual t) o₂ o₁) :=
⟨bounded.dual, λ
 h, by have [] [] [":=", expr bounded.dual h]; rwa ["[", expr dual_dual, ",", expr order_dual.preorder.dual_dual, "]"] ["at", ident this]⟩

theorem bounded.weak_left : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t ⊥ o₂
| nil, o₁, o₂, h =>
  by 
    cases o₂ <;>
      try 
          trivial <;>
        exact h
| node s l x r, _, _, ⟨ol, Or⟩ => ⟨ol.weak_left, Or⟩

theorem bounded.weak_right : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t o₁ ⊤
| nil, o₁, o₂, h =>
  by 
    cases o₁ <;>
      try 
          trivial <;>
        exact h
| node s l x r, _, _, ⟨ol, Or⟩ => ⟨ol, or.weak_right⟩

theorem bounded.weak {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂) : Bounded t ⊥ ⊤ :=
  h.weak_left.weak_right

theorem bounded.mono_left {x y : α} (xy : x ≤ y) :
  ∀ {t : Ordnode α} {o}, Bounded t («expr↑ » y) o → Bounded t («expr↑ » x) o
| nil, none, h => ⟨⟩
| nil, some z, h => lt_of_le_of_ltₓ xy h
| node s l z r, o, ⟨ol, Or⟩ => ⟨ol.mono_left, Or⟩

theorem bounded.mono_right {x y : α} (xy : x ≤ y) :
  ∀ {t : Ordnode α} {o}, Bounded t o («expr↑ » x) → Bounded t o («expr↑ » y)
| nil, none, h => ⟨⟩
| nil, some z, h => lt_of_lt_of_leₓ h xy
| node s l z r, o, ⟨ol, Or⟩ => ⟨ol, or.mono_right⟩

theorem bounded.to_lt : ∀ {t : Ordnode α} {x y : α}, Bounded t x y → x < y
| nil, x, y, h => h
| node _ l y r, x, z, ⟨h₁, h₂⟩ => lt_transₓ h₁.to_lt h₂.to_lt

theorem bounded.to_nil {t : Ordnode α} : ∀ {o₁ o₂}, Bounded t o₁ o₂ → Bounded nil o₁ o₂
| none, _, h => ⟨⟩
| some _, none, h => ⟨⟩
| some x, some y, h => h.to_lt

theorem bounded.trans_left {t₁ t₂ : Ordnode α} {x : α} :
  ∀ {o₁ o₂}, Bounded t₁ o₁ («expr↑ » x) → Bounded t₂ («expr↑ » x) o₂ → Bounded t₂ o₁ o₂
| none, o₂, h₁, h₂ => h₂.weak_left
| some y, o₂, h₁, h₂ => h₂.mono_left (le_of_ltₓ h₁.to_lt)

theorem bounded.trans_right {t₁ t₂ : Ordnode α} {x : α} :
  ∀ {o₁ o₂}, Bounded t₁ o₁ («expr↑ » x) → Bounded t₂ («expr↑ » x) o₂ → Bounded t₁ o₁ o₂
| o₁, none, h₁, h₂ => h₁.weak_right
| o₁, some y, h₁, h₂ => h₁.mono_right (le_of_ltₓ h₂.to_lt)

theorem bounded.mem_lt : ∀ {t o} {x : α}, Bounded t o («expr↑ » x) → all (· < x) t
| nil, o, x, _ => ⟨⟩
| node _ l y r, o, x, ⟨h₁, h₂⟩ => ⟨h₁.mem_lt.imp fun z h => lt_transₓ h h₂.to_lt, h₂.to_lt, h₂.mem_lt⟩

theorem bounded.mem_gt : ∀ {t o} {x : α}, Bounded t («expr↑ » x) o → all (· > x) t
| nil, o, x, _ => ⟨⟩
| node _ l y r, o, x, ⟨h₁, h₂⟩ => ⟨h₁.mem_gt, h₁.to_lt, h₂.mem_gt.imp fun z => lt_transₓ h₁.to_lt⟩

theorem bounded.of_lt :
  ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil o₁ («expr↑ » x) → all (· < x) t → Bounded t o₁ («expr↑ » x)
| nil, o₁, o₂, x, _, hn, _ => hn
| node _ l y r, o₁, o₂, x, ⟨h₁, h₂⟩, hn, ⟨al₁, al₂, al₃⟩ => ⟨h₁, h₂.of_lt al₂ al₃⟩

theorem bounded.of_gt :
  ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil («expr↑ » x) o₂ → all (· > x) t → Bounded t («expr↑ » x) o₂
| nil, o₁, o₂, x, _, hn, _ => hn
| node _ l y r, o₁, o₂, x, ⟨h₁, h₂⟩, hn, ⟨al₁, al₂, al₃⟩ => ⟨h₁.of_gt al₂ al₁, h₂⟩

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem bounded.to_sep
{t₁ t₂ o₁ o₂}
{x : α}
(h₁ : bounded t₁ o₁ «expr↑ »(x))
(h₂ : bounded t₂ «expr↑ »(x) o₂) : t₁.all (λ y, t₂.all (λ z : α, «expr < »(y, z))) :=
«expr $ »(h₁.mem_lt.imp, λ y yx, «expr $ »(h₂.mem_gt.imp, λ z xz, lt_trans yx xz))

end 

/-! ### `valid` -/


section 

variable[Preorderₓ α]

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. This version of `valid` also puts all elements in the tree in the interval `(lo, hi)`. -/
structure valid'(lo : WithBot α)(t : Ordnode α)(hi : WithTop α) : Prop where 
  ord : t.bounded lo hi 
  sz : t.sized 
  bal : t.balanced

/-- The validity predicate for an `ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. -/
def valid (t : Ordnode α) : Prop :=
  valid' ⊥ t ⊤

theorem valid'.mono_left {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : valid' («expr↑ » y) t o) :
  valid' («expr↑ » x) t o :=
  ⟨h.1.mono_left xy, h.2, h.3⟩

theorem valid'.mono_right {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : valid' o t («expr↑ » x)) :
  valid' o t («expr↑ » y) :=
  ⟨h.1.mono_right xy, h.2, h.3⟩

theorem valid'.trans_left {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ («expr↑ » x))
  (H : valid' («expr↑ » x) t₂ o₂) : valid' o₁ t₂ o₂ :=
  ⟨h.trans_left H.1, H.2, H.3⟩

theorem valid'.trans_right {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : valid' o₁ t₁ («expr↑ » x))
  (h : Bounded t₂ («expr↑ » x) o₂) : valid' o₁ t₁ o₂ :=
  ⟨H.1.trans_right h, H.2, H.3⟩

theorem valid'.of_lt {t : Ordnode α} {x : α} {o₁ o₂} (H : valid' o₁ t o₂) (h₁ : Bounded nil o₁ («expr↑ » x))
  (h₂ : all (· < x) t) : valid' o₁ t («expr↑ » x) :=
  ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩

theorem valid'.of_gt {t : Ordnode α} {x : α} {o₁ o₂} (H : valid' o₁ t o₂) (h₁ : Bounded nil («expr↑ » x) o₂)
  (h₂ : all (· > x) t) : valid' («expr↑ » x) t o₂ :=
  ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩

theorem valid'.valid {t o₁ o₂} (h : @valid' α _ o₁ t o₂) : valid t :=
  ⟨h.1.weak, h.2, h.3⟩

theorem valid'_nil {o₁ o₂} (h : Bounded nil o₁ o₂) : valid' o₁ (@nil α) o₂ :=
  ⟨h, ⟨⟩, ⟨⟩⟩

theorem valid_nil : valid (@nil α) :=
  valid'_nil ⟨⟩

theorem valid'.node {s l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H : balanced_sz (size l) (size r)) (hs : s = (size l+size r)+1) : valid' o₁ (@node α s l x r) o₂ :=
  ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

theorem valid'.dual : ∀ {t : Ordnode α} {o₁ o₂} (h : valid' o₁ t o₂), @valid' (OrderDual α) _ o₂ (dual t) o₁
| nil, o₁, o₂, h => valid'_nil h.1.dual
| node s l x r, o₁, o₂, ⟨⟨ol, Or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ =>
  let ⟨ol', sl', bl'⟩ := valid'.dual ⟨ol, sl, bl⟩
  let ⟨or', sr', br'⟩ := valid'.dual ⟨Or, sr, br⟩
  ⟨⟨or', ol'⟩,
    ⟨by 
        simp [size_dual, add_commₓ],
      sr', sl'⟩,
    ⟨by 
        rw [size_dual, size_dual] <;> exact b.symm,
      br', bl'⟩⟩

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.dual_iff {t : ordnode α} {o₁ o₂} : «expr ↔ »(valid' o₁ t o₂, @valid' (order_dual α) _ o₂ (dual t) o₁) :=
⟨valid'.dual, λ
 h, by have [] [] [":=", expr valid'.dual h]; rwa ["[", expr dual_dual, ",", expr order_dual.preorder.dual_dual, "]"] ["at", ident this]⟩

theorem valid.dual {t : Ordnode α} : valid t → @valid (OrderDual α) _ (dual t) :=
  valid'.dual

theorem valid.dual_iff {t : Ordnode α} : valid t ↔ @valid (OrderDual α) _ (dual t) :=
  valid'.dual_iff

theorem valid'.left {s l x r o₁ o₂} (H : valid' o₁ (@node α s l x r) o₂) : valid' o₁ l x :=
  ⟨H.1.1, H.2.2.1, H.3.2.1⟩

theorem valid'.right {s l x r o₁ o₂} (H : valid' o₁ (@node α s l x r) o₂) : valid' («expr↑ » x) r o₂ :=
  ⟨H.1.2, H.2.2.2, H.3.2.2⟩

theorem valid.left {s l x r} (H : valid (@node α s l x r)) : valid l :=
  H.left.valid

theorem valid.right {s l x r} (H : valid (@node α s l x r)) : valid r :=
  H.right.valid

theorem valid.size_eq {s l x r} (H : valid (@node α s l x r)) : size (@node α s l x r) = (size l+size r)+1 :=
  H.2.1

theorem valid'.node' {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H : balanced_sz (size l) (size r)) : valid' o₁ (@node' α l x r) o₂ :=
  hl.node hr H rfl

theorem valid'_singleton {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ («expr↑ » x)) (h₂ : Bounded nil («expr↑ » x) o₂) :
  valid' o₁ (singleton x : Ordnode α) o₂ :=
  (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl

theorem valid_singleton {x : α} : valid (singleton x : Ordnode α) :=
  valid'_singleton ⟨⟩ ⟨⟩

theorem valid'.node3_l {l x m y r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hm : valid' («expr↑ » x) m («expr↑ » y))
  (hr : valid' («expr↑ » y) r o₂) (H1 : balanced_sz (size l) (size m)) (H2 : balanced_sz ((size l+size m)+1) (size r)) :
  valid' o₁ (@node3_l α l x m y r) o₂ :=
  (hl.node' hm H1).node' hr H2

theorem valid'.node3_r {l x m y r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hm : valid' («expr↑ » x) m («expr↑ » y))
  (hr : valid' («expr↑ » y) r o₂) (H1 : balanced_sz (size l) ((size m+size r)+1)) (H2 : balanced_sz (size m) (size r)) :
  valid' o₁ (@node3_r α l x m y r) o₂ :=
  hl.node' (hm.node' hr H2) H1

theorem valid'.node4_l_lemma₁ {a b c d : ℕ} (lr₂ : (3*((b+c)+1)+d) ≤ (16*a)+9) (mr₂ : ((b+c)+1) ≤ 3*d) (mm₁ : b ≤ 3*c) :
  b < (3*a)+1 :=
  by 
    linarith

theorem valid'.node4_l_lemma₂ {b c d : ℕ} (mr₂ : ((b+c)+1) ≤ 3*d) : c ≤ 3*d :=
  by 
    linarith

theorem valid'.node4_l_lemma₃ {b c d : ℕ} (mr₁ : (2*d) ≤ (b+c)+1) (mm₁ : b ≤ 3*c) : d ≤ 3*c :=
  by 
    linarith

theorem valid'.node4_l_lemma₄ {a b c d : ℕ} (lr₁ : (3*a) ≤ ((b+c)+1)+d) (mr₂ : ((b+c)+1) ≤ 3*d) (mm₁ : b ≤ 3*c) :
  ((a+b)+1) ≤ 3*(c+d)+1 :=
  by 
    linarith

theorem valid'.node4_l_lemma₅ {a b c d : ℕ} (lr₂ : (3*((b+c)+1)+d) ≤ (16*a)+9) (mr₁ : (2*d) ≤ (b+c)+1) (mm₂ : c ≤ 3*b) :
  ((c+d)+1) ≤ 3*(a+b)+1 :=
  by 
    linarith

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.node4_l
{l x m y r o₁ o₂}
(hl : valid' o₁ l «expr↑ »(x))
(hm : valid' «expr↑ »(x) m «expr↑ »(y))
(hr : valid' «expr↑ »(y) r o₂)
(Hm : «expr < »(0, size m))
(H : «expr ∨ »(«expr ∧ »(«expr = »(size l, 0), «expr ∧ »(«expr = »(size m, 1), «expr ≤ »(size r, 1))), «expr ∧ »(«expr < »(0, size l), «expr ∧ »(«expr ≤ »(«expr * »(ratio, size r), size m), «expr ∧ »(«expr ≤ »(«expr * »(delta, size l), «expr + »(size m, size r)), «expr ∧ »(«expr ≤ »(«expr * »(3, «expr + »(size m, size r)), «expr + »(«expr * »(16, size l), 9)), «expr ≤ »(size m, «expr * »(delta, size r)))))))) : valid' o₁ (@node4_l α l x m y r) o₂ :=
begin
  cases [expr m] ["with", ident s, ident ml, ident z, ident mr],
  { cases [expr Hm] [] },
  suffices [] [":", expr «expr ∧ »(balanced_sz (size l) (size ml), «expr ∧ »(balanced_sz (size mr) (size r), balanced_sz «expr + »(«expr + »(size l, size ml), 1) «expr + »(«expr + »(size mr, size r), 1)))],
  from [expr valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2],
  rcases [expr H, "with", "⟨", ident l0, ",", ident m1, ",", ident r0, "⟩", "|", "⟨", ident l0, ",", ident mr₁, ",", ident lr₁, ",", ident lr₂, ",", ident mr₂, "⟩"],
  { rw ["[", expr hm.2.size_eq, ",", expr nat.succ_inj', ",", expr add_eq_zero_iff, "]"] ["at", ident m1],
    rw ["[", expr l0, ",", expr m1.1, ",", expr m1.2, "]"] [],
    rcases [expr size r, "with", "_", "|", "_", "|", "_"]; exact [expr exprdec_trivial()] },
  { cases [expr nat.eq_zero_or_pos (size r)] ["with", ident r0, ident r0],
    { rw [expr r0] ["at", ident mr₂],
      cases [expr not_le_of_lt Hm mr₂] [] },
    rw ["[", expr hm.2.size_eq, "]"] ["at", ident lr₁, ident lr₂, ident mr₁, ident mr₂],
    by_cases [expr mm, ":", expr «expr ≤ »(«expr + »(size ml, size mr), 1)],
    { have [ident r1] [] [":=", expr le_antisymm ((mul_le_mul_left exprdec_trivial()).1 (le_trans mr₁ (nat.succ_le_succ mm) : «expr ≤ »(_, «expr * »(ratio, 1)))) r0],
      rw ["[", expr r1, ",", expr add_assoc, "]"] ["at", ident lr₁],
      have [ident l1] [] [":=", expr le_antisymm ((mul_le_mul_left exprdec_trivial()).1 (le_trans lr₁ (add_le_add_right mm 2) : «expr ≤ »(_, «expr * »(delta, 1)))) l0],
      rw ["[", expr l1, ",", expr r1, "]"] [],
      cases [expr size ml] []; cases [expr size mr] [],
      { exact [expr exprdec_trivial()] },
      { rw [expr zero_add] ["at", ident mm],
        rcases [expr mm, "with", "_", "|", "⟨", "_", ",", "⟨", "⟩", "⟩"],
        exact [expr exprdec_trivial()] },
      { rcases [expr mm, "with", "_", "|", "⟨", "_", ",", "⟨", "⟩", "⟩"],
        exact [expr exprdec_trivial()] },
      { rw [expr nat.succ_add] ["at", ident mm],
        rcases [expr mm, "with", "_", "|", "⟨", "_", ",", "⟨", "⟩", "⟩"] } },
    rcases [expr hm.3.1.resolve_left mm, "with", "⟨", ident mm₁, ",", ident mm₂, "⟩"],
    cases [expr nat.eq_zero_or_pos (size ml)] ["with", ident ml0, ident ml0],
    { rw ["[", expr ml0, ",", expr mul_zero, ",", expr nat.le_zero_iff, "]"] ["at", ident mm₂],
      rw ["[", expr ml0, ",", expr mm₂, "]"] ["at", ident mm],
      cases [expr mm exprdec_trivial()] [] },
    cases [expr nat.eq_zero_or_pos (size mr)] ["with", ident mr0, ident mr0],
    { rw ["[", expr mr0, ",", expr mul_zero, ",", expr nat.le_zero_iff, "]"] ["at", ident mm₁],
      rw ["[", expr mr0, ",", expr mm₁, "]"] ["at", ident mm],
      cases [expr mm exprdec_trivial()] [] },
    have [] [":", expr «expr ≤ »(«expr * »(2, size l), «expr + »(«expr + »(size ml, size mr), 1))] [],
    { have [] [] [":=", expr nat.mul_le_mul_left _ lr₁],
      rw ["[", expr mul_left_comm, ",", expr mul_add, "]"] ["at", ident this],
      have [] [] [":=", expr le_trans this (add_le_add_left mr₁ _)],
      rw ["[", "<-", expr nat.succ_mul, "]"] ["at", ident this],
      exact [expr (mul_le_mul_left exprdec_trivial()).1 this] },
    refine [expr ⟨or.inr ⟨_, _⟩, or.inr ⟨_, _⟩, or.inr ⟨_, _⟩⟩],
    { refine [expr (mul_le_mul_left exprdec_trivial()).1 (le_trans this _)],
      rw ["[", expr two_mul, ",", expr nat.succ_le_iff, "]"] [],
      refine [expr add_lt_add_of_lt_of_le _ mm₂],
      simpa [] [] [] [] [] ["using", expr (mul_lt_mul_right ml0).2 (exprdec_trivial() : «expr < »(1, 3))] },
    { exact [expr nat.le_of_lt_succ (valid'.node4_l_lemma₁ lr₂ mr₂ mm₁)] },
    { exact [expr valid'.node4_l_lemma₂ mr₂] },
    { exact [expr valid'.node4_l_lemma₃ mr₁ mm₁] },
    { exact [expr valid'.node4_l_lemma₄ lr₁ mr₂ mm₁] },
    { exact [expr valid'.node4_l_lemma₅ lr₂ mr₁ mm₂] } }
end

theorem valid'.rotate_l_lemma₁ {a b c : ℕ} (H2 : (3*a) ≤ b+c) (hb₂ : c ≤ 3*b) : a ≤ 3*b :=
  by 
    linarith

theorem valid'.rotate_l_lemma₂ {a b c : ℕ} (H3 : (2*b+c) ≤ (9*a)+3) (h : b < 2*c) : b < (3*a)+1 :=
  by 
    linarith

theorem valid'.rotate_l_lemma₃ {a b c : ℕ} (H2 : (3*a) ≤ b+c) (h : b < 2*c) : (a+b) < 3*c :=
  by 
    linarith

theorem valid'.rotate_l_lemma₄ {a b : ℕ} (H3 : (2*b) ≤ (9*a)+3) : (3*b) ≤ (16*a)+9 :=
  by 
    linarith

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.rotate_l
{l x r o₁ o₂}
(hl : valid' o₁ l «expr↑ »(x))
(hr : valid' «expr↑ »(x) r o₂)
(H1 : «expr¬ »(«expr ≤ »(«expr + »(size l, size r), 1)))
(H2 : «expr < »(«expr * »(delta, size l), size r))
(H3 : «expr ∨ »(«expr ≤ »(«expr * »(2, size r), «expr + »(«expr * »(9, size l), 5)), «expr ≤ »(size r, 3))) : valid' o₁ (@rotate_l α l x r) o₂ :=
begin
  cases [expr r] ["with", ident rs, ident rl, ident rx, ident rr],
  { cases [expr H2] [] },
  rw ["[", expr hr.2.size_eq, ",", expr nat.lt_succ_iff, "]"] ["at", ident H2],
  rw ["[", expr hr.2.size_eq, "]"] ["at", ident H3],
  replace [ident H3] [":", expr «expr ∨ »(«expr ≤ »(«expr * »(2, «expr + »(size rl, size rr)), «expr + »(«expr * »(9, size l), 3)), «expr ≤ »(«expr + »(size rl, size rr), 2))] [":=", expr H3.imp (@nat.le_of_add_le_add_right 2 _ _) nat.le_of_succ_le_succ],
  have [ident H3_0] [":", expr «expr = »(size l, 0) → «expr ≤ »(«expr + »(size rl, size rr), 2)] [],
  { intro [ident l0],
    rw [expr l0] ["at", ident H3],
    exact [expr «expr $ »(or_iff_right_of_imp, by exact [expr λ
       h, (mul_le_mul_left exprdec_trivial()).1 (le_trans h exprdec_trivial())]).1 H3] },
  have [ident H3p] [":", expr «expr > »(size l, 0) → «expr ≤ »(«expr * »(2, «expr + »(size rl, size rr)), «expr + »(«expr * »(9, size l), 3))] [":=", expr λ
   l0 : «expr ≤ »(1, size l), «expr $ »(or_iff_left_of_imp, by intro []; linarith [] [] []).1 H3],
  have [ident ablem] [":", expr ∀
   {a b : exprℕ()}, «expr ≤ »(1, a) → «expr ≤ »(«expr + »(a, b), 2) → «expr ≤ »(b, 1)] [],
  { intros [],
    linarith [] [] [] },
  have [ident hlp] [":", expr «expr > »(size l, 0) → «expr¬ »(«expr ≤ »(«expr + »(size rl, size rr), 1))] [":=", expr λ
   l0 hb, absurd (le_trans (le_trans (nat.mul_le_mul_left _ l0) H2) hb) exprdec_trivial()],
  rw [expr rotate_l] [],
  split_ifs [] [],
  { have [ident rr0] [":", expr «expr > »(size rr, 0)] [":=", expr (mul_lt_mul_left exprdec_trivial()).1 (lt_of_le_of_lt (nat.zero_le _) h : «expr < »(«expr * »(ratio, 0), _))],
    suffices [] [":", expr «expr ∧ »(balanced_sz (size l) (size rl), balanced_sz «expr + »(«expr + »(size l, size rl), 1) (size rr))],
    { exact [expr hl.node3_l hr.left hr.right this.1 this.2] },
    cases [expr nat.eq_zero_or_pos (size l)] ["with", ident l0, ident l0],
    { rw [expr l0] [],
      replace [ident H3] [] [":=", expr H3_0 l0],
      have [] [] [":=", expr hr.3.1],
      cases [expr nat.eq_zero_or_pos (size rl)] ["with", ident rl0, ident rl0],
      { rw [expr rl0] ["at", ident this, "⊢"],
        rw [expr le_antisymm (balanced_sz_zero.1 this.symm) rr0] [],
        exact [expr exprdec_trivial()] },
      have [ident rr1] [":", expr «expr = »(size rr, 1)] [":=", expr le_antisymm (ablem rl0 H3) rr0],
      rw [expr add_comm] ["at", ident H3],
      rw ["[", expr rr1, ",", expr show «expr = »(size rl, 1), from le_antisymm (ablem rr0 H3) rl0, "]"] [],
      exact [expr exprdec_trivial()] },
    replace [ident H3] [] [":=", expr H3p l0],
    rcases [expr hr.3.1.resolve_left (hlp l0), "with", "⟨", ident hb₁, ",", ident hb₂, "⟩"],
    cases [expr nat.eq_zero_or_pos (size rl)] ["with", ident rl0, ident rl0],
    { rw [expr rl0] ["at", ident hb₂],
      cases [expr not_le_of_gt rr0 hb₂] [] },
    cases [expr eq_or_lt_of_le (show «expr ≤ »(1, size rr), from rr0)] ["with", ident rr1, ident rr1],
    { rw ["[", "<-", expr rr1, "]"] ["at", ident h, ident H2, "⊢"],
      have [] [":", expr «expr = »(size rl, 1)] [":=", expr le_antisymm (nat.lt_succ_iff.1 h) rl0],
      rw [expr this] ["at", ident H2],
      exact [expr absurd (le_trans (nat.mul_le_mul_left _ l0) H2) exprdec_trivial()] },
    refine [expr ⟨or.inr ⟨_, _⟩, or.inr ⟨_, _⟩⟩],
    { exact [expr valid'.rotate_l_lemma₁ H2 hb₂] },
    { exact [expr nat.le_of_lt_succ (valid'.rotate_l_lemma₂ H3 h)] },
    { exact [expr valid'.rotate_l_lemma₃ H2 h] },
    { exact [expr le_trans hb₂ «expr $ »(nat.mul_le_mul_left _, le_trans (nat.le_add_left _ _) (nat.le_add_right _ _))] } },
  { cases [expr nat.eq_zero_or_pos (size rl)] ["with", ident rl0, ident rl0],
    { rw ["[", expr rl0, ",", expr not_lt, ",", expr nat.le_zero_iff, ",", expr nat.mul_eq_zero, "]"] ["at", ident h],
      replace [ident h] [] [":=", expr h.resolve_left exprdec_trivial()],
      rw ["[", expr rl0, ",", expr h, ",", expr nat.le_zero_iff, ",", expr nat.mul_eq_zero, "]"] ["at", ident H2],
      rw ["[", expr hr.2.size_eq, ",", expr rl0, ",", expr h, ",", expr H2.resolve_left exprdec_trivial(), "]"] ["at", ident H1],
      cases [expr H1 exprdec_trivial()] [] },
    refine [expr hl.node4_l hr.left hr.right rl0 _],
    cases [expr nat.eq_zero_or_pos (size l)] ["with", ident l0, ident l0],
    { replace [ident H3] [] [":=", expr H3_0 l0],
      cases [expr nat.eq_zero_or_pos (size rr)] ["with", ident rr0, ident rr0],
      { have [] [] [":=", expr hr.3.1],
        rw [expr rr0] ["at", ident this],
        exact [expr or.inl ⟨l0, le_antisymm (balanced_sz_zero.1 this) rl0, «expr ▸ »(rr0.symm, zero_le_one)⟩] },
      exact [expr or.inl ⟨l0, le_antisymm «expr $ »(ablem rr0, by rwa [expr add_comm] []) rl0, ablem rl0 H3⟩] },
    exact [expr or.inr ⟨l0, not_lt.1 h, H2, valid'.rotate_l_lemma₄ (H3p l0), (hr.3.1.resolve_left (hlp l0)).1⟩] }
end

theorem valid'.rotate_r {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H1 : ¬(size l+size r) ≤ 1) (H2 : (delta*size r) < size l) (H3 : ((2*size l) ≤ (9*size r)+5) ∨ size l ≤ 3) :
  valid' o₁ (@rotate_r α l x r) o₂ :=
  by 
    refine' valid'.dual_iff.2 _ 
    rw [dual_rotate_r]
    refine' hr.dual.rotate_l hl.dual _ _ _
    ·
      rwa [size_dual, size_dual, add_commₓ]
    ·
      rwa [size_dual, size_dual]
    ·
      rwa [size_dual, size_dual]

theorem valid'.balance'_aux {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H₁ : ((2*@size α r) ≤ (9*size l)+5) ∨ size r ≤ 3) (H₂ : ((2*@size α l) ≤ (9*size r)+5) ∨ size l ≤ 3) :
  valid' o₁ (@balance' α l x r) o₂ :=
  by 
    rw [balance']
    splitIfs
    ·
      exact hl.node' hr (Or.inl h)
    ·
      exact hl.rotate_l hr h h_1 H₁
    ·
      exact hl.rotate_r hr h h_2 H₂
    ·
      exact hl.node' hr (Or.inr ⟨not_ltₓ.1 h_2, not_ltₓ.1 h_1⟩)

theorem valid'.balance'_lemma {α l l' r r'} (H1 : balanced_sz l' r')
  (H2 : Nat.dist (@size α l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l') :
  ((2*@size α r) ≤ (9*size l)+5) ∨ size r ≤ 3 :=
  by 
    suffices  : @size α r ≤ 3*size l+1
    ·
      cases' Nat.eq_zero_or_posₓ (size l) with l0 l0
      ·
        apply Or.inr 
        rwa [l0] at this 
      change 1 ≤ _ at l0 
      apply Or.inl 
      linarith 
    rcases H2 with (⟨hl, rfl⟩ | ⟨hr, rfl⟩) <;> rcases H1 with (h | ⟨h₁, h₂⟩)
    ·
      exact le_transₓ (Nat.le_add_leftₓ _ _) (le_transₓ h (Nat.le_add_leftₓ _ _))
    ·
      exact le_transₓ h₂ (Nat.mul_le_mul_leftₓ _$ le_transₓ (Nat.dist_tri_right _ _) (Nat.add_le_add_leftₓ hl _))
    ·
      exact
        le_transₓ (Nat.dist_tri_left' _ _)
          (le_transₓ (add_le_add hr (le_transₓ (Nat.le_add_leftₓ _ _) h))
            (by 
              decide))
    ·
      rw [Nat.mul_succ]
      exact
        le_transₓ (Nat.dist_tri_right' _ _)
          (add_le_add h₂
            (le_transₓ hr
              (by 
                decide)))

theorem valid'.balance' {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H : ∃ l' r', balanced_sz l' r' ∧ (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
  valid' o₁ (@balance' α l x r) o₂ :=
  let ⟨l', r', H1, H2⟩ := H 
  valid'.balance'_aux hl hr (valid'.balance'_lemma H1 H2) (valid'.balance'_lemma H1.symm H2.symm)

theorem valid'.balance {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H : ∃ l' r', balanced_sz l' r' ∧ (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
  valid' o₁ (@balance α l x r) o₂ :=
  by 
    rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2] <;> exact hl.balance' hr H

theorem valid'.balance_l_aux {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H₁ : size l = 0 → size r ≤ 1) (H₂ : 1 ≤ size l → 1 ≤ size r → size r ≤ delta*size l)
  (H₃ : ((2*@size α l) ≤ (9*size r)+5) ∨ size l ≤ 3) : valid' o₁ (@balance_l α l x r) o₂ :=
  by 
    rw [balance_l_eq_balance hl.2 hr.2 H₁ H₂, balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
    refine' hl.balance'_aux hr (Or.inl _) H₃ 
    cases' Nat.eq_zero_or_posₓ (size r) with r0 r0
    ·
      rw [r0]
      exact Nat.zero_leₓ _ 
    cases' Nat.eq_zero_or_posₓ (size l) with l0 l0
    ·
      rw [l0]
      exact
        le_transₓ (Nat.mul_le_mul_leftₓ _ (H₁ l0))
          (by 
            decide)
    replace H₂ : _ ≤ 3*_ := H₂ l0 r0 
    linarith

theorem valid'.balance_l {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H : (∃ l', raised l' (size l) ∧ balanced_sz l' (size r)) ∨ ∃ r', raised (size r) r' ∧ balanced_sz (size l) r') :
  valid' o₁ (@balance_l α l x r) o₂ :=
  by 
    rw [balance_l_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
    refine' hl.balance' hr _ 
    rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
    ·
      exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
    ·
      exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.balance_r_aux
{l x r o₁ o₂}
(hl : valid' o₁ l «expr↑ »(x))
(hr : valid' «expr↑ »(x) r o₂)
(H₁ : «expr = »(size r, 0) → «expr ≤ »(size l, 1))
(H₂ : «expr ≤ »(1, size r) → «expr ≤ »(1, size l) → «expr ≤ »(size l, «expr * »(delta, size r)))
(H₃ : «expr ∨ »(«expr ≤ »(«expr * »(2, @size α r), «expr + »(«expr * »(9, size l), 5)), «expr ≤ »(size r, 3))) : valid' o₁ (@balance_r α l x r) o₂ :=
begin
  rw ["[", expr valid'.dual_iff, ",", expr dual_balance_r, "]"] [],
  have [] [] [":=", expr hr.dual.balance_l_aux hl.dual],
  rw ["[", expr size_dual, ",", expr size_dual, "]"] ["at", ident this],
  exact [expr this H₁ H₂ H₃]
end

theorem valid'.balance_r {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » x)) (hr : valid' («expr↑ » x) r o₂)
  (H : (∃ l', raised (size l) l' ∧ balanced_sz l' (size r)) ∨ ∃ r', raised r' (size r) ∧ balanced_sz (size l) r') :
  valid' o₁ (@balance_r α l x r) o₂ :=
  by 
    rw [valid'.dual_iff, dual_balance_r] <;> exact hr.dual.balance_l hl.dual (balance_sz_dual H)

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.erase_max_aux
{s l x r o₁ o₂}
(H : valid' o₁ (node s l x r) o₂) : «expr ∧ »(valid' o₁ (@erase_max α (node' l x r)) «expr↑ »(find_max' x r), «expr = »(size (node' l x r), «expr + »(size (erase_max (node' l x r)), 1))) :=
begin
  have [] [] [":=", expr H.2.eq_node'],
  rw [expr this] ["at", ident H],
  clear [ident this],
  induction [expr r] [] ["with", ident rs, ident rl, ident rx, ident rr, ident IHrl, ident IHrr] ["generalizing", ident l, ident x, ident o₁],
  { exact [expr ⟨H.left, rfl⟩] },
  have [] [] [":=", expr H.2.2.2.eq_node'],
  rw [expr this] ["at", ident H, "⊢"],
  rcases [expr IHrr H.right, "with", "⟨", ident h, ",", ident e, "⟩"],
  refine [expr ⟨valid'.balance_l H.left h (or.inr ⟨_, or.inr e, H.3.1⟩), _⟩],
  rw ["[", expr erase_max, ",", expr size_balance_l H.3.2.1 h.3 H.2.2.1 h.2 (or.inr ⟨_, or.inr e, H.3.1⟩), "]"] [],
  rw ["[", expr size, ",", expr e, "]"] [],
  refl
end

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.erase_min_aux
{s l x r o₁ o₂}
(H : valid' o₁ (node s l x r) o₂) : «expr ∧ »(valid' «expr↑ »(find_min' l x) (@erase_min α (node' l x r)) o₂, «expr = »(size (node' l x r), «expr + »(size (erase_min (node' l x r)), 1))) :=
by have [] [] [":=", expr H.dual.erase_max_aux]; rwa ["[", "<-", expr dual_node', ",", expr size_dual, ",", "<-", expr dual_erase_min, ",", expr size_dual, ",", "<-", expr valid'.dual_iff, ",", expr find_max'_dual, "]"] ["at", ident this]

theorem erase_min.valid : ∀ {t} (h : @valid α _ t), valid (erase_min t)
| nil, _ => valid_nil
| node _ l x r, h =>
  by 
    rw [h.2.eq_node'] <;> exact h.erase_min_aux.1.valid

theorem erase_max.valid {t} (h : @valid α _ t) : valid (erase_max t) :=
  by 
    rw [valid.dual_iff, dual_erase_max] <;> exact erase_min.valid h.dual

theorem valid'.glue_aux {l r o₁ o₂} (hl : valid' o₁ l o₂) (hr : valid' o₁ r o₂)
  (sep : l.all fun x => r.all fun y => x < y) (bal : balanced_sz (size l) (size r)) :
  valid' o₁ (@glue α l r) o₂ ∧ size (glue l r) = size l+size r :=
  by 
    cases' l with ls ll lx lr
    ·
      exact ⟨hr, (zero_addₓ _).symm⟩
    cases' r with rs rl rx rr
    ·
      exact ⟨hl, rfl⟩
    dsimp [glue]
    splitIfs
    ·
      rw [split_max_eq, glue]
      cases' valid'.erase_max_aux hl with v e 
      suffices H 
      refine' ⟨valid'.balance_r v (hr.of_gt _ _) H, _⟩
      ·
        refine' find_max'_all lx lr hl.1.2.to_nil (sep.2.2.imp _)
        exact fun x h => hr.1.2.to_nil.mono_left (le_of_ltₓ h.2.1)
      ·
        exact @find_max'_all _ (fun a => all (· > a) (node rs rl rx rr)) lx lr sep.2.1 sep.2.2
      ·
        rw [size_balance_r v.3 hr.3 v.2 hr.2 H, add_right_commₓ, ←e, hl.2.1]
        rfl
      ·
        refine' Or.inl ⟨_, Or.inr e, _⟩
        rwa [hl.2.eq_node'] at bal
    ·
      rw [split_min_eq, glue]
      cases' valid'.erase_min_aux hr with v e 
      suffices H 
      refine' ⟨valid'.balance_l (hl.of_lt _ _) v H, _⟩
      ·
        refine' @find_min'_all _ (fun a => Bounded nil o₁ («expr↑ » a)) rl rx (sep.2.1.1.imp _) hr.1.1.to_nil 
        exact fun y h => hl.1.1.to_nil.mono_right (le_of_ltₓ h)
      ·
        exact
          @find_min'_all _ (fun a => all (· < a) (node ls ll lx lr)) rl rx
            (all_iff_forall.2$ fun x hx => sep.imp$ fun y hy => all_iff_forall.1 hy.1 _ hx)
            (sep.imp$ fun y hy => hy.2.1)
      ·
        rw [size_balance_l hl.3 v.3 hl.2 v.2 H, add_assocₓ, ←e, hr.2.1]
        rfl
      ·
        refine' Or.inr ⟨_, Or.inr e, _⟩
        rwa [hr.2.eq_node'] at bal

theorem valid'.glue {l x r o₁ o₂} (hl : valid' o₁ l («expr↑ » (x : α))) (hr : valid' («expr↑ » x) r o₂) :
  balanced_sz (size l) (size r) → valid' o₁ (@glue α l r) o₂ ∧ size (@glue α l r) = size l+size r :=
  valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)

theorem valid'.merge_lemma {a b c : ℕ} (h₁ : (3*a) < (b+c)+1) (h₂ : b ≤ 3*c) : (2*a+b) ≤ (9*c)+5 :=
  by 
    linarith

theorem valid'.merge_aux₁ {o₁ o₂ ls ll lx lr rs rl rx rr t} (hl : valid' o₁ (@node α ls ll lx lr) o₂)
  (hr : valid' o₁ (node rs rl rx rr) o₂) (h : (delta*ls) < rs) (v : valid' o₁ t («expr↑ » rx))
  (e : size t = ls+size rl) : valid' o₁ (balance_l t rx rr) o₂ ∧ size (balance_l t rx rr) = ls+rs :=
  by 
    rw [hl.2.1] at e 
    rw [hl.2.1, hr.2.1, delta] at h 
    rcases hr.3.1 with (H | ⟨hr₁, hr₂⟩)
    ·
      linarith 
    suffices H₂ 
    suffices H₁ 
    refine' ⟨valid'.balance_l_aux v hr.right H₁ H₂ _, _⟩
    ·
      rw [e]
      exact Or.inl (valid'.merge_lemma h hr₁)
    ·
      rw [balance_l_eq_balance v.2 hr.2.2.2 H₁ H₂, balance_eq_balance' v.3 hr.3.2.2 v.2 hr.2.2.2,
        size_balance' v.2 hr.2.2.2, e, hl.2.1, hr.2.1]
      simp [add_commₓ, add_left_commₓ]
    ·
      rw [e, add_right_commₓ]
      rintro ⟨⟩
    ·
      intro _ h₁ 
      rw [e]
      unfold delta  at hr₂⊢
      linarith

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.merge_aux
{l r o₁ o₂}
(hl : valid' o₁ l o₂)
(hr : valid' o₁ r o₂)
(sep : l.all (λ
  x, r.all (λ
   y, «expr < »(x, y)))) : «expr ∧ »(valid' o₁ (@merge α l r) o₂, «expr = »(size (merge l r), «expr + »(size l, size r))) :=
begin
  induction [expr l] [] ["with", ident ls, ident ll, ident lx, ident lr, ident IHll, ident IHlr] ["generalizing", ident o₁, ident o₂, ident r],
  { exact [expr ⟨hr, (zero_add _).symm⟩] },
  induction [expr r] [] ["with", ident rs, ident rl, ident rx, ident rr, ident IHrl, ident IHrr] ["generalizing", ident o₁, ident o₂],
  { exact [expr ⟨hl, rfl⟩] },
  rw ["[", expr merge_node, "]"] [],
  split_ifs [] [],
  { cases [expr IHrl «expr $ »(sep.imp, λ
      x h, h.1) «expr $ »(hl.of_lt hr.1.1.to_nil, «expr $ »(sep.imp, λ x h, h.2.1)) hr.left] ["with", ident v, ident e],
    exact [expr valid'.merge_aux₁ hl hr h v e] },
  { cases [expr IHlr hl.right (hr.of_gt hl.1.2.to_nil sep.2.1) sep.2.2] ["with", ident v, ident e],
    have [] [] [":=", expr valid'.merge_aux₁ hr.dual hl.dual h_1 v.dual],
    rw ["[", expr size_dual, ",", expr add_comm, ",", expr size_dual, ",", "<-", expr dual_balance_r, ",", "<-", expr valid'.dual_iff, ",", expr size_dual, ",", expr add_comm rs, "]"] ["at", ident this],
    exact [expr this e] },
  { refine [expr valid'.glue_aux hl hr sep (or.inr ⟨not_lt.1 h_1, not_lt.1 h⟩)] }
end

theorem valid.merge {l r} (hl : valid l) (hr : valid r) (sep : l.all fun x => r.all fun y => x < y) :
  valid (@merge α l r) :=
  (valid'.merge_aux hl hr sep).1

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_with.valid_aux
[is_total α ((«expr ≤ »))]
[@decidable_rel α ((«expr ≤ »))]
(f : α → α)
(x : α)
(hf : ∀
 y, «expr ∧ »(«expr ≤ »(x, y), «expr ≤ »(y, x)) → «expr ∧ »(«expr ≤ »(x, f y), «expr ≤ »(f y, x))) : ∀
{t
 o₁
 o₂}, valid' o₁ t o₂ → bounded nil o₁ «expr↑ »(x) → bounded nil «expr↑ »(x) o₂ → «expr ∧ »(valid' o₁ (insert_with f x t) o₂, raised (size t) (size (insert_with f x t)))
| nil, o₁, o₂, _, bl, br := ⟨valid'_singleton bl br, or.inr rfl⟩
| node sz l y r, o₁, o₂, h, bl, br := begin
  rw ["[", expr insert_with, ",", expr cmp_le, "]"] [],
  split_ifs [] []; rw ["[", expr insert_with, "]"] [],
  { rcases [expr h, "with", "⟨", "⟨", ident lx, ",", ident xr, "⟩", ",", ident hs, ",", ident hb, "⟩"],
    rcases [expr hf _ ⟨h_1, h_2⟩, "with", "⟨", ident xf, ",", ident fx, "⟩"],
    refine [expr ⟨⟨⟨lx.mono_right (le_trans h_2 xf), xr.mono_left (le_trans fx h_1)⟩, hs, hb⟩, or.inl rfl⟩] },
  { rcases [expr insert_with.valid_aux h.left bl (lt_of_le_not_le h_1 h_2), "with", "⟨", ident vl, ",", ident e, "⟩"],
    suffices [ident H] [],
    { refine [expr ⟨vl.balance_l h.right H, _⟩],
      rw ["[", expr size_balance_l vl.3 h.3.2.2 vl.2 h.2.2.2 H, ",", expr h.2.size_eq, "]"] [],
      refine [expr (e.add_right _).add_right _] },
    { exact [expr or.inl ⟨_, e, h.3.1⟩] } },
  { have [] [":", expr «expr < »(y, x)] [":=", expr lt_of_le_not_le ((total_of ((«expr ≤ »)) _ _).resolve_left h_1) h_1],
    rcases [expr insert_with.valid_aux h.right this br, "with", "⟨", ident vr, ",", ident e, "⟩"],
    suffices [ident H] [],
    { refine [expr ⟨h.left.balance_r vr H, _⟩],
      rw ["[", expr size_balance_r h.3.2.1 vr.3 h.2.2.1 vr.2 H, ",", expr h.2.size_eq, "]"] [],
      refine [expr (e.add_left _).add_right _] },
    { exact [expr or.inr ⟨_, e, h.3.1⟩] } }
end

theorem insert_with.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (f : α → α) (x : α)
  (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) {t} (h : valid t) : valid (insert_with f x t) :=
  (insert_with.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

theorem insert_eq_insert_with [@DecidableRel α (· ≤ ·)] (x : α) : ∀ t, Ordnode.insert x t = insert_with (fun _ => x) x t
| nil => rfl
| node _ l y r =>
  by 
    unfold Ordnode.insert insert_with <;>
      cases cmpLe x y <;> unfold Ordnode.insert insert_with <;> simp [insert_eq_insert_with]

theorem insert.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : valid t) :
  valid (Ordnode.insert x t) :=
  by 
    rw [insert_eq_insert_with] <;> exact insert_with.valid _ _ (fun _ _ => ⟨le_reflₓ _, le_reflₓ _⟩) h

theorem insert'_eq_insert_with [@DecidableRel α (· ≤ ·)] (x : α) : ∀ t, insert' x t = insert_with id x t
| nil => rfl
| node _ l y r =>
  by 
    unfold insert' insert_with <;> cases cmpLe x y <;> unfold insert' insert_with <;> simp [insert'_eq_insert_with]

theorem insert'.valid [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : valid t) : valid (insert' x t) :=
  by 
    rw [insert'_eq_insert_with] <;> exact insert_with.valid _ _ (fun _ => id) h

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.map_aux
{β}
[preorder β]
{f : α → β}
(f_strict_mono : strict_mono f)
{t a₁ a₂}
(h : valid' a₁ t a₂) : «expr ∧ »(valid' (option.map f a₁) (map f t) (option.map f a₂), «expr = »((map f t).size, t.size)) :=
begin
  induction [expr t] [] [] ["generalizing", ident a₁, ident a₂],
  { simp [] [] [] ["[", expr map, "]"] [] [],
    apply [expr valid'_nil],
    cases [expr a₁] [],
    { trivial },
    cases [expr a₂] [],
    { trivial },
    simp [] [] [] ["[", expr bounded, "]"] [] [],
    exact [expr f_strict_mono h.ord] },
  { have [ident t_ih_l'] [] [":=", expr t_ih_l h.left],
    have [ident t_ih_r'] [] [":=", expr t_ih_r h.right],
    clear [ident t_ih_l, ident t_ih_r],
    cases [expr t_ih_l'] ["with", ident t_l_valid, ident t_l_size],
    cases [expr t_ih_r'] ["with", ident t_r_valid, ident t_r_size],
    simp [] [] [] ["[", expr map, "]"] [] [],
    split,
    { exact [expr and.intro t_l_valid.ord t_r_valid.ord] },
    { repeat { split },
      { rw ["[", expr t_l_size, ",", expr t_r_size, "]"] [],
        exact [expr h.sz.1] },
      { exact [expr t_l_valid.sz] },
      { exact [expr t_r_valid.sz] } },
    { repeat { split },
      { rw ["[", expr t_l_size, ",", expr t_r_size, "]"] [],
        exact [expr h.bal.1] },
      { exact [expr t_l_valid.bal] },
      { exact [expr t_r_valid.bal] } } }
end

theorem map.valid {β} [Preorderₓ β] {f : α → β} (f_strict_mono : StrictMono f) {t} (h : valid t) : valid (map f t) :=
  (valid'.map_aux f_strict_mono h).1

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem valid'.erase_aux
[@decidable_rel α ((«expr ≤ »))]
(x : α)
{t a₁ a₂}
(h : valid' a₁ t a₂) : «expr ∧ »(valid' a₁ (erase x t) a₂, raised (erase x t).size t.size) :=
begin
  induction [expr t] [] [] ["generalizing", ident a₁, ident a₂],
  { simp [] [] [] ["[", expr erase, ",", expr raised, "]"] [] [],
    exact [expr h] },
  { simp [] [] [] ["[", expr erase, "]"] [] [],
    have [ident t_ih_l'] [] [":=", expr t_ih_l h.left],
    have [ident t_ih_r'] [] [":=", expr t_ih_r h.right],
    clear [ident t_ih_l, ident t_ih_r],
    cases [expr t_ih_l'] ["with", ident t_l_valid, ident t_l_size],
    cases [expr t_ih_r'] ["with", ident t_r_valid, ident t_r_size],
    cases [expr cmp_le x t_x] []; simp [] [] [] ["[", expr erase._match_1, "]"] [] []; rw [expr h.sz.1] [],
    { suffices [ident h_balanceable] [],
      split,
      { exact [expr valid'.balance_r t_l_valid h.right h_balanceable] },
      { rw [expr size_balance_r t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz h_balanceable] [],
        repeat { apply [expr raised.add_right] },
        exact [expr t_l_size] },
      { left,
        existsi [expr t_l.size],
        exact [expr and.intro t_l_size h.bal.1] } },
    { have [ident h_glue] [] [":=", expr valid'.glue h.left h.right h.bal.1],
      cases [expr h_glue] ["with", ident h_glue_valid, ident h_glue_sized],
      split,
      { exact [expr h_glue_valid] },
      { right,
        rw [expr h_glue_sized] [] } },
    { suffices [ident h_balanceable] [],
      split,
      { exact [expr valid'.balance_l h.left t_r_valid h_balanceable] },
      { rw [expr size_balance_l h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz h_balanceable] [],
        apply [expr raised.add_right],
        apply [expr raised.add_left],
        exact [expr t_r_size] },
      { right,
        existsi [expr t_r.size],
        exact [expr and.intro t_r_size h.bal.1] } } }
end

theorem erase.valid [@DecidableRel α (· ≤ ·)] (x : α) {t} (h : valid t) : valid (erase x t) :=
  (valid'.erase_aux x h).1

-- error in Data.Ordmap.Ordset: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem size_erase_of_mem
[@decidable_rel α ((«expr ≤ »))]
{x : α}
{t a₁ a₂}
(h : valid' a₁ t a₂)
(h_mem : «expr ∈ »(x, t)) : «expr = »(size (erase x t), «expr - »(size t, 1)) :=
begin
  induction [expr t] [] [] ["generalizing", ident a₁, ident a₂, ident h, ident h_mem],
  { contradiction },
  { have [ident t_ih_l'] [] [":=", expr t_ih_l h.left],
    have [ident t_ih_r'] [] [":=", expr t_ih_r h.right],
    clear [ident t_ih_l, ident t_ih_r],
    unfold [ident has_mem.mem, ident mem] ["at", ident h_mem],
    unfold [ident erase] [],
    cases [expr cmp_le x t_x] []; simp [] [] [] ["[", expr mem._match_1, "]"] [] ["at", ident h_mem]; simp [] [] [] ["[", expr erase._match_1, "]"] [] [],
    { have [ident t_ih_l] [] [":=", expr t_ih_l' h_mem],
      clear [ident t_ih_l', ident t_ih_r'],
      have [ident t_l_h] [] [":=", expr valid'.erase_aux x h.left],
      cases [expr t_l_h] ["with", ident t_l_valid, ident t_l_size],
      rw [expr size_balance_r t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz (or.inl (exists.intro t_l.size (and.intro t_l_size h.bal.1)))] [],
      rw ["[", expr t_ih_l, ",", expr h.sz.1, "]"] [],
      have [ident h_pos_t_l_size] [] [":=", expr pos_size_of_mem h.left.sz h_mem],
      cases [expr t_l.size] ["with", ident t_l_size],
      { cases [expr h_pos_t_l_size] [] },
      simp [] [] [] ["[", expr nat.succ_add, "]"] [] [] },
    { rw ["[", expr (valid'.glue h.left h.right h.bal.1).2, ",", expr h.sz.1, "]"] [],
      refl },
    { have [ident t_ih_r] [] [":=", expr t_ih_r' h_mem],
      clear [ident t_ih_l', ident t_ih_r'],
      have [ident t_r_h] [] [":=", expr valid'.erase_aux x h.right],
      cases [expr t_r_h] ["with", ident t_r_valid, ident t_r_size],
      rw [expr size_balance_l h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz (or.inr (exists.intro t_r.size (and.intro t_r_size h.bal.1)))] [],
      rw ["[", expr t_ih_r, ",", expr h.sz.1, "]"] [],
      have [ident h_pos_t_r_size] [] [":=", expr pos_size_of_mem h.right.sz h_mem],
      cases [expr t_r.size] ["with", ident t_r_size],
      { cases [expr h_pos_t_r_size] [] },
      simp [] [] [] ["[", expr nat.succ_add, ",", expr nat.add_succ, "]"] [] [] } }
end

end 

end Ordnode

/-- An `ordset α` is a finite set of values, represented as a tree. The operations on this type
maintain that the tree is balanced and correctly stores subtree sizes at each level. The
correctness property of the tree is baked into the type, so all operations on this type are correct
by construction. -/
def Ordset (α : Type _) [Preorderₓ α] :=
  { t : Ordnode α // t.valid }

namespace Ordset

open Ordnode

variable[Preorderₓ α]

/-- O(1). The empty set. -/
def nil : Ordset α :=
  ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-- O(1). Get the size of the set. -/
def size (s : Ordset α) : ℕ :=
  s.1.size

/-- O(1). Construct a singleton set containing value `a`. -/
protected def singleton (a : α) : Ordset α :=
  ⟨singleton a, valid_singleton⟩

instance  : HasEmptyc (Ordset α) :=
  ⟨nil⟩

instance  : Inhabited (Ordset α) :=
  ⟨nil⟩

instance  : HasSingleton α (Ordset α) :=
  ⟨Ordset.singleton⟩

/-- O(1). Is the set empty? -/
def Empty (s : Ordset α) : Prop :=
  s = ∅

theorem empty_iff {s : Ordset α} : s = ∅ ↔ s.1.Empty :=
  ⟨fun h =>
      by 
        cases h <;> exact rfl,
    fun h =>
      by 
        cases s <;> cases s_val <;> [exact rfl, cases h]⟩

instance  : DecidablePred (@Empty α _) :=
  fun s => decidableOfIff' _ empty_iff

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, this replaces it. -/
protected def insert [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩

instance  [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] : HasInsert α (Ordset α) :=
  ⟨Ordset.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
def insert' [IsTotal α (· ≤ ·)] [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨insert' x s.1, insert'.valid _ s.2⟩

section 

variable[@DecidableRel α (· ≤ ·)]

/-- O(log n). Does the set contain the element `x`? That is,
  is there an element that is equivalent to `x` in the order? -/
def mem (x : α) (s : Ordset α) : Bool :=
  x ∈ s.val

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
  if it exists. -/
def find (x : α) (s : Ordset α) : Option α :=
  Ordnode.find x s.val

instance  : HasMem α (Ordset α) :=
  ⟨fun x s => mem x s⟩

instance mem.decidable (x : α) (s : Ordset α) : Decidable (x ∈ s) :=
  Bool.decidableEq _ _

theorem pos_size_of_mem {x : α} {t : Ordset α} (h_mem : x ∈ t) : 0 < size t :=
  by 
    simp [HasMem.Mem, mem] at h_mem 
    apply Ordnode.pos_size_of_mem t.property.sz h_mem

end 

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element. -/
def erase [@DecidableRel α (· ≤ ·)] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

/-- O(n). Map a function across a tree, without changing the structure. -/
def map {β} [Preorderₓ β] (f : α → β) (f_strict_mono : StrictMono f) (s : Ordset α) : Ordset β :=
  ⟨Ordnode.mapₓ f s.val, Ordnode.mapₓ.valid f_strict_mono s.property⟩

end Ordset

