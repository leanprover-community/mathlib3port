import Mathbin.Data.Set.Lattice

/-!
# Accumulate

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/


variable{α β γ : Type _}{s : α → Set β}{t : α → Set γ}

namespace Set

/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃(y : _)(_ : y ≤ x), s y

variable{s}

theorem accumulate_def [LE α] {x : α} : accumulate s x = ⋃(y : _)(_ : y ≤ x), s y :=
  rfl

@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ (y : _)(_ : y ≤ x), z ∈ s y :=
  mem_bUnion_iff

theorem subset_accumulate [Preorderₓ α] {x : α} : s x ⊆ accumulate s x :=
  fun z => mem_bUnion le_rfl

theorem monotone_accumulate [Preorderₓ α] : Monotone (accumulate s) :=
  fun x y hxy => bUnion_subset_bUnion_left$ fun z hz => le_transₓ hz hxy

theorem bUnion_accumulate [Preorderₓ α] (x : α) : (⋃(y : _)(_ : y ≤ x), accumulate s y) = ⋃(y : _)(_ : y ≤ x), s y :=
  by 
    apply subset.antisymm
    ·
      exact bUnion_subset fun x hx => (monotone_accumulate hx : _)
    ·
      exact bUnion_mono fun x hx => subset_accumulate

theorem Union_accumulate [Preorderₓ α] : (⋃x, accumulate s x) = ⋃x, s x :=
  by 
    apply subset.antisymm
    ·
      simp only [subset_def, mem_Union, exists_imp_distrib, mem_accumulate]
      intro z x x' hx'x hz 
      exact ⟨x', hz⟩
    ·
      exact Union_subset_Union fun i => subset_accumulate

end Set

