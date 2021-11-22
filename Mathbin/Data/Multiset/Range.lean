import Mathbin.Data.Multiset.Basic 
import Mathbin.Data.List.Range

/-! # `multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/


open List Nat

namespace Multiset

/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : Multiset ℕ :=
  range n

@[simp]
theorem range_zero : range 0 = 0 :=
  rfl

@[simp]
theorem range_succ (n : ℕ) : range (succ n) = n ::ₘ range n :=
  by 
    rw [range, range_succ, ←coe_add, add_commₓ] <;> rfl

@[simp]
theorem card_range (n : ℕ) : card (range n) = n :=
  length_range _

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
  range_subset

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
  mem_range

@[simp]
theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  not_mem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n+1) :=
  List.self_mem_range_succ n

end Multiset

