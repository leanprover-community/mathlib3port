import Mathbin.Combinatorics.Composition 
import Mathbin.Data.Nat.Parity 
import Mathbin.Tactic.ApplyFun

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/


variable{α : Type _}

open Multiset

open_locale BigOperators

namespace Nat

-- error in Combinatorics.Partition: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler decidable_eq
/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext #[], derive #[expr decidable_eq]]
structure partition
(n : exprℕ()) :=
  (parts : multiset exprℕ())
  (parts_pos : ∀ {i}, «expr ∈ »(i, parts) → «expr < »(0, i))
  (parts_sum : «expr = »(parts.sum, n))

namespace Partition

/-- A composition induces a partition (just convert the list to a multiset). -/
def of_composition (n : ℕ) (c : Composition n) : partition n :=
  { parts := c.blocks, parts_pos := fun i hi => c.blocks_pos hi,
    parts_sum :=
      by 
        rw [Multiset.coe_sum, c.blocks_sum] }

theorem of_composition_surj {n : ℕ} : Function.Surjective (of_composition n) :=
  by 
    rintro ⟨b, hb₁, hb₂⟩
    rcases Quotientₓ.exists_rep b with ⟨b, rfl⟩
    refine' ⟨⟨b, fun i hi => hb₁ hi, _⟩, partition.ext _ _ rfl⟩
    simpa using hb₂

/--
Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
def of_sums (n : ℕ) (l : Multiset ℕ) (hl : l.sum = n) : partition n :=
  { parts := l.filter (· ≠ 0),
    parts_pos :=
      fun i hi =>
        Nat.pos_of_ne_zeroₓ$
          by 
            apply of_mem_filter hi,
    parts_sum :=
      by 
        have lt : (l.filter (· = 0)+l.filter (· ≠ 0)) = l := filter_add_not _ l 
        applyFun Multiset.sum  at lt 
        have lz : (l.filter (· = 0)).Sum = 0
        ·
          rw [Multiset.sum_eq_zero_iff]
          simp 
        simpa [lz, hl] using lt }

/-- A `multiset ℕ` induces a partition on its sum. -/
def of_multiset (l : Multiset ℕ) : partition l.sum :=
  of_sums _ l rfl

/-- The partition of exactly one part. -/
def indiscrete_partition (n : ℕ) : partition n :=
  of_sums n {n} rfl

instance  {n : ℕ} : Inhabited (partition n) :=
  ⟨indiscrete_partition n⟩

/--
The number of times a positive integer `i` appears in the partition `of_sums n l hl` is the same
as the number of times it appears in the multiset `l`.
(For `i = 0`, `partition.non_zero` combined with `multiset.count_eq_zero_of_not_mem` gives that
this is `0` instead.)
-/
theorem count_of_sums_of_ne_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
  (of_sums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi

theorem count_of_sums_zero {n : ℕ} {l : Multiset ℕ} (hl : l.sum = n) : (of_sums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl

/--
Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance  (n : ℕ) : Fintype (partition n) :=
  Fintype.ofSurjective (of_composition n) of_composition_surj

/-- The finset of those partitions in which every part is odd. -/
def odds (n : ℕ) : Finset (partition n) :=
  Finset.univ.filter fun c => ∀ i _ : i ∈ c.parts, ¬Even i

/-- The finset of those partitions in which each part is used at most once. -/
def distincts (n : ℕ) : Finset (partition n) :=
  Finset.univ.filter fun c => c.parts.nodup

/-- The finset of those partitions in which every part is odd and used at most once. -/
def odd_distincts (n : ℕ) : Finset (partition n) :=
  odds n ∩ distincts n

end Partition

end Nat

