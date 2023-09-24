/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Topology.StoneCech
import Topology.Algebra.Semigroup
import Data.Stream.Init

#align_import combinatorics.hindman from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# Hindman's theorem on finite sums

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove Hindman's theorem on finite sums, using idempotent ultrafilters.

Given an infinite sequence `a₀, a₁, a₂, …` of positive integers, the set `FS(a₀, …)` is the set
of positive integers that can be expressed as a finite sum of `aᵢ`'s, without repetition. Hindman's
theorem asserts that whenever the positive integers are finitely colored, there exists a sequence
`a₀, a₁, a₂, …` such that `FS(a₀, …)` is monochromatic. There is also a stronger version, saying
that whenever a set of the form `FS(a₀, …)` is finitely colored, there exists a sequence
`b₀, b₁, b₂, …` such that `FS(b₀, …)` is monochromatic and contained in `FS(a₀, …)`. We prove both
these versions for a general semigroup `M` instead of `ℕ+` since it is no harder, although this
special case implies the general case.

The idea of the proof is to extend the addition `(+) : M → M → M` to addition `(+) : βM → βM → βM`
on the space `βM` of ultrafilters on `M`. One can prove that if `U` is an _idempotent_ ultrafilter,
i.e. `U + U = U`, then any `U`-large subset of `M` contains some set `FS(a₀, …)` (see
`exists_FS_of_large`). And with the help of a general topological argument one can show that any set
of the form `FS(a₀, …)` is `U`-large according to some idempotent ultrafilter `U` (see
`exists_idempotent_ultrafilter_le_FS`). This is enough to prove the theorem since in any finite
partition of a `U`-large set, one of the parts is `U`-large.

## Main results

- `FS_partition_regular`: the strong form of Hindman's theorem
- `exists_FS_of_finite_cover`: the weak form of Hindman's theorem

## Tags

Ramsey theory, ultrafilter

-/


open Filter

#print Ultrafilter.mul /-
/-- Multiplication of ultrafilters given by `∀ᶠ m in U*V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m*m')`. -/
@[to_additive
      "Addition of ultrafilters given by\n`∀ᶠ m in U+V, p m ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m+m')`."]
def Ultrafilter.mul {M} [Mul M] : Mul (Ultrafilter M) where mul U V := (· * ·) <$> U <*> V
#align ultrafilter.has_mul Ultrafilter.mul
#align ultrafilter.has_add Ultrafilter.add
-/

attribute [local instance] Ultrafilter.mul Ultrafilter.add

#print Ultrafilter.eventually_mul /-
/- We could have taken this as the definition of `U * V`, but then we would have to prove that it
defines an ultrafilter. -/
@[to_additive]
theorem Ultrafilter.eventually_mul {M} [Mul M] (U V : Ultrafilter M) (p : M → Prop) :
    (∀ᶠ m in ↑(U * V), p m) ↔ ∀ᶠ m in U, ∀ᶠ m' in V, p (m * m') :=
  Iff.rfl
#align ultrafilter.eventually_mul Ultrafilter.eventually_mul
#align ultrafilter.eventually_add Ultrafilter.eventually_add
-/

#print Ultrafilter.semigroup /-
/-- Semigroup structure on `ultrafilter M` induced by a semigroup structure on `M`. -/
@[to_additive
      "Additive semigroup structure on `ultrafilter M` induced by an additive semigroup\nstructure on `M`."]
def Ultrafilter.semigroup {M} [Semigroup M] : Semigroup (Ultrafilter M) :=
  { Ultrafilter.mul with
    mul_assoc := fun U V W =>
      Ultrafilter.coe_inj.mp <|
        Filter.ext' fun p => by simp only [Ultrafilter.eventually_mul, mul_assoc] }
#align ultrafilter.semigroup Ultrafilter.semigroup
#align ultrafilter.add_semigroup Ultrafilter.addSemigroup
-/

attribute [local instance] Ultrafilter.semigroup Ultrafilter.addSemigroup

#print Ultrafilter.continuous_mul_left /-
-- We don't prove `continuous_mul_right`, because in general it is false!
@[to_additive]
theorem Ultrafilter.continuous_mul_left {M} [Semigroup M] (V : Ultrafilter M) :
    Continuous (· * V) :=
  TopologicalSpace.IsTopologicalBasis.continuous ultrafilterBasis_is_basis _ <|
    Set.forall_range_iff.mpr fun s => ultrafilter_isOpen_basic {m : M | ∀ᶠ m' in V, m * m' ∈ s}
#align ultrafilter.continuous_mul_left Ultrafilter.continuous_mul_left
#align ultrafilter.continuous_add_left Ultrafilter.continuous_add_left
-/

namespace Hindman

#print Hindman.FS /-
/-- `FS a` is the set of finite sums in `a`, i.e. `m ∈ FS a` if `m` is the sum of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
inductive FS {M} [AddSemigroup M] : Stream' M → Set M
  | head (a : Stream' M) : FS a a.headI
  | tail (a : Stream' M) (m : M) (h : FS a.tail m) : FS a m
  | cons (a : Stream' M) (m : M) (h : FS a.tail m) : FS a (a.headI + m)
#align hindman.FS Hindman.FS
-/

#print Hindman.FP /-
/-- `FP a` is the set of finite products in `a`, i.e. `m ∈ FP a` if `m` is the product of a nonempty
subsequence of `a`. We give a direct inductive definition instead of talking about subsequences. -/
@[to_additive FS]
inductive FP {M} [Semigroup M] : Stream' M → Set M
  | head (a : Stream' M) : FP a a.headI
  | tail (a : Stream' M) (m : M) (h : FP a.tail m) : FP a m
  | cons (a : Stream' M) (m : M) (h : FP a.tail m) : FP a (a.headI * m)
#align hindman.FP Hindman.FP
#align hindman.FS Hindman.FS
-/

#print Hindman.FP.mul /-
/-- If `m` and `m'` are finite products in `M`, then so is `m * m'`, provided that `m'` is obtained
from a subsequence of `M` starting sufficiently late. -/
@[to_additive
      "If `m` and `m'` are finite sums in `M`, then so is `m + m'`, provided that `m'`\nis obtained from a subsequence of `M` starting sufficiently late."]
theorem FP.mul {M} [Semigroup M] {a : Stream' M} {m : M} (hm : m ∈ FP a) :
    ∃ n, ∀ m' ∈ FP (a.drop n), m * m' ∈ FP a :=
  by
  induction' hm with a a m hm ih a m hm ih
  · exact ⟨1, fun m hm => FP.cons a m hm⟩
  · cases' ih with n hn; use n + 1; intro m' hm'; exact FP.tail _ _ (hn _ hm')
  · cases' ih with n hn; use n + 1; intro m' hm'; rw [mul_assoc]; exact FP.cons _ _ (hn _ hm')
#align hindman.FP.mul Hindman.FP.mul
#align hindman.FS.add Hindman.FS.add
-/

#print Hindman.exists_idempotent_ultrafilter_le_FP /-
@[to_additive exists_idempotent_ultrafilter_le_FS]
theorem exists_idempotent_ultrafilter_le_FP {M} [Semigroup M] (a : Stream' M) :
    ∃ U : Ultrafilter M, U * U = U ∧ ∀ᶠ m in U, m ∈ FP a :=
  by
  let S : Set (Ultrafilter M) := ⋂ n, {U | ∀ᶠ m in U, m ∈ FP (a.drop n)}
  obtain ⟨U, hU, U_idem⟩ := exists_idempotent_in_compact_subsemigroup _ S _ _ _
  · refine' ⟨U, U_idem, _⟩; convert set.mem_Inter.mp hU 0
  · exact Ultrafilter.continuous_mul_left
  · apply IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed
    · intro n U hU
      apply eventually.mono hU
      rw [add_comm, ← Stream'.drop_drop, ← Stream'.tail_eq_drop]
      exact FP.tail _
    · intro n; exact ⟨pure _, mem_pure.mpr <| FP.head _⟩
    · exact (ultrafilter_isClosed_basic _).IsCompact
    · intro n; apply ultrafilter_isClosed_basic
  · exact IsClosed.isCompact (isClosed_iInter fun i => ultrafilter_isClosed_basic _)
  · intro U hU V hV
    rw [Set.mem_iInter] at *
    intro n
    rw [Set.mem_setOf_eq, Ultrafilter.eventually_mul]
    apply eventually.mono (hU n)
    intro m hm
    obtain ⟨n', hn⟩ := FP.mul hm
    apply eventually.mono (hV (n' + n))
    intro m' hm'
    apply hn
    simpa only [Stream'.drop_drop] using hm'
#align hindman.exists_idempotent_ultrafilter_le_FP Hindman.exists_idempotent_ultrafilter_le_FP
#align hindman.exists_idempotent_ultrafilter_le_FS Hindman.exists_idempotent_ultrafilter_le_FS
-/

#print Hindman.exists_FP_of_large /-
@[to_additive exists_FS_of_large]
theorem exists_FP_of_large {M} [Semigroup M] (U : Ultrafilter M) (U_idem : U * U = U) (s₀ : Set M)
    (sU : s₀ ∈ U) : ∃ a, FP a ⊆ s₀ :=
  by
  /- Informally: given a `U`-large set `s₀`, the set `s₀ ∩ { m | ∀ᶠ m' in U, m * m' ∈ s₀ }` is also
  `U`-large (since `U` is idempotent). Thus in particular there is an `a₀` in this intersection. Now
  let `s₁` be the intersection `s₀ ∩ { m | a₀ * m ∈ s₀ }`. By choice of `a₀`, this is again `U`-large,
  so we can repeat the argument starting from `s₁`, obtaining `a₁`, `s₂`, etc. This gives the desired
  infinite sequence. -/
  have exists_elem : ∀ {s : Set M} (hs : s ∈ U), (s ∩ {m | ∀ᶠ m' in U, m * m' ∈ s}).Nonempty :=
    fun s hs => Ultrafilter.nonempty_of_mem (inter_mem hs <| by rw [← U_idem] at hs ; exact hs)
  let elem : { s // s ∈ U } → M := fun p => (exists_elem p.property).some
  let succ : { s // s ∈ U } → { s // s ∈ U } := fun p =>
    ⟨p.val ∩ {m | elem p * m ∈ p.val},
      inter_mem p.2 <| show _ from Set.inter_subset_right _ _ (exists_elem p.2).some_mem⟩
  use Stream'.corec elem succ (Subtype.mk s₀ sU)
  suffices ∀ (a : Stream' M), ∀ m ∈ FP a, ∀ p, a = Stream'.corec elem succ p → m ∈ p.val by
    intro m hm; exact this _ m hm ⟨s₀, sU⟩ rfl
  clear sU s₀
  intro a m h
  induction' h with b b n h ih b n h ih
  · rintro p rfl
    rw [Stream'.corec_eq, Stream'.head_cons]
    exact Set.inter_subset_left _ _ (Set.Nonempty.some_mem _)
  · rintro p rfl
    refine' Set.inter_subset_left _ _ (ih (succ p) _)
    rw [Stream'.corec_eq, Stream'.tail_cons]
  · rintro p rfl
    have := Set.inter_subset_right _ _ (ih (succ p) _)
    · simpa only using this
    rw [Stream'.corec_eq, Stream'.tail_cons]
#align hindman.exists_FP_of_large Hindman.exists_FP_of_large
#align hindman.exists_FS_of_large Hindman.exists_FS_of_large
-/

#print Hindman.FP_partition_regular /-
/-- The strong form of **Hindman's theorem**: in any finite cover of an FP-set, one the parts
contains an FP-set. -/
@[to_additive FS_partition_regular
      "The strong form of **Hindman's theorem**: in any finite cover of\nan FS-set, one the parts contains an FS-set."]
theorem FP_partition_regular {M} [Semigroup M] (a : Stream' M) (s : Set (Set M)) (sfin : s.Finite)
    (scov : FP a ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ b : Stream' M, FP b ⊆ c :=
  let ⟨U, idem, aU⟩ := exists_idempotent_ultrafilter_le_FP a
  let ⟨c, cs, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset aU scov)
  ⟨c, cs, exists_FP_of_large U idem c hc⟩
#align hindman.FP_partition_regular Hindman.FP_partition_regular
#align hindman.FS_partition_regular Hindman.FS_partition_regular
-/

#print Hindman.exists_FP_of_finite_cover /-
/-- The weak form of **Hindman's theorem**: in any finite cover of a nonempty semigroup, one of the
parts contains an FP-set. -/
@[to_additive exists_FS_of_finite_cover
      "The weak form of **Hindman's theorem**: in any finite cover\nof a nonempty additive semigroup, one of the parts contains an FS-set."]
theorem exists_FP_of_finite_cover {M} [Semigroup M] [Nonempty M] (s : Set (Set M)) (sfin : s.Finite)
    (scov : ⊤ ⊆ ⋃₀ s) : ∃ c ∈ s, ∃ a : Stream' M, FP a ⊆ c :=
  let ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_mul_left (@Ultrafilter.continuous_mul_left M _)
  let ⟨c, c_s, hc⟩ := (Ultrafilter.finite_sUnion_mem_iff sfin).mp (mem_of_superset univ_mem scov)
  ⟨c, c_s, exists_FP_of_large U hU c hc⟩
#align hindman.exists_FP_of_finite_cover Hindman.exists_FP_of_finite_cover
#align hindman.exists_FS_of_finite_cover Hindman.exists_FS_of_finite_cover
-/

#print Hindman.FP_drop_subset_FP /-
@[to_additive FS_iter_tail_sub_FS]
theorem FP_drop_subset_FP {M} [Semigroup M] (a : Stream' M) (n : ℕ) : FP (a.drop n) ⊆ FP a :=
  by
  induction' n with n ih; · rfl
  rw [Nat.succ_eq_one_add, ← Stream'.drop_drop]
  exact trans (FP.tail _) ih
#align hindman.FP_drop_subset_FP Hindman.FP_drop_subset_FP
#align hindman.FS_iter_tail_sub_FS Hindman.FS_iter_tail_sub_FS
-/

#print Hindman.FP.singleton /-
@[to_additive]
theorem FP.singleton {M} [Semigroup M] (a : Stream' M) (i : ℕ) : a.get? i ∈ FP a := by
  induction' i with i ih generalizing a; · apply FP.head; · apply FP.tail; apply ih
#align hindman.FP.singleton Hindman.FP.singleton
#align hindman.FS.singleton Hindman.FS.singleton
-/

#print Hindman.FP.mul_two /-
@[to_additive]
theorem FP.mul_two {M} [Semigroup M] (a : Stream' M) (i j : ℕ) (ij : i < j) :
    a.get? i * a.get? j ∈ FP a := by
  refine' FP_drop_subset_FP _ i _
  rw [← Stream'.head_drop]
  apply FP.cons
  rcases le_iff_exists_add.mp (Nat.succ_le_of_lt ij) with ⟨d, hd⟩
  have := FP.singleton (a.drop i).tail d
  rw [Stream'.tail_eq_drop, Stream'.nth_drop, Stream'.nth_drop] at this 
  convert this
  rw [hd, add_comm, Nat.succ_add, Nat.add_succ]
#align hindman.FP.mul_two Hindman.FP.mul_two
#align hindman.FS.add_two Hindman.FS.add_two
-/

#print Hindman.FP.finset_prod /-
@[to_additive]
theorem FP.finset_prod {M} [CommMonoid M] (a : Stream' M) (s : Finset ℕ) (hs : s.Nonempty) :
    (s.Prod fun i => a.get? i) ∈ FP a :=
  by
  refine' FP_drop_subset_FP _ (s.min' hs) _
  induction' s using Finset.strongInduction with s ih
  rw [← Finset.mul_prod_erase _ _ (s.min'_mem hs), ← Stream'.head_drop]
  cases' (s.erase (s.min' hs)).eq_empty_or_nonempty with h h
  · rw [h, Finset.prod_empty, mul_one]; exact FP.head _
  · apply FP.cons; rw [Stream'.tail_eq_drop, Stream'.drop_drop, add_comm]
    refine' Set.mem_of_subset_of_mem _ (ih _ (Finset.erase_ssubset <| s.min'_mem hs) h)
    have : s.min' hs + 1 ≤ (s.erase (s.min' hs)).min' h :=
      Nat.succ_le_of_lt (Finset.min'_lt_of_mem_erase_min' _ _ <| Finset.min'_mem _ _)
    cases' le_iff_exists_add.mp this with d hd
    rw [hd, add_comm, ← Stream'.drop_drop]
    apply FP_drop_subset_FP
#align hindman.FP.finset_prod Hindman.FP.finset_prod
#align hindman.FS.finset_sum Hindman.FS.finset_sum
-/

end Hindman

