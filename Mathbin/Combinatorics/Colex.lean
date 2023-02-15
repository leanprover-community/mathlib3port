/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov

! This file was ported from Lean 3 source module combinatorics.colex
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Algebra.GeomSum

/-!
# Colex

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the colex ordering for finite sets, and give a couple of important
lemmas and properties relating to it.

The colex ordering likes to avoid large values - it can be thought of on
`finset ℕ` as the "binary" ordering. That is, order A based on
`∑_{i ∈ A} 2^i`.
It's defined here in a slightly more general way, requiring only `has_lt α` in
the definition of colex on `finset α`. In the context of the Kruskal-Katona
theorem, we are interested in particular on how colex behaves for sets of a
fixed size. If the size is 3, colex on ℕ starts
123, 124, 134, 234, 125, 135, 235, 145, 245, 345, ...

## Main statements
* `colex.hom_lt_iff`: strictly monotone functions preserve colex
* Colex order properties - linearity, decidability and so on.
* `forall_lt_of_colex_lt_of_forall_lt`: if A < B in colex, and everything
  in B is < t, then everything in A is < t. This confirms the idea that
  an enumeration under colex will exhaust all sets using elements < t before
  allowing t to be included.
* `sum_two_pow_le_iff_lt`: colex for α = ℕ is the same as binary
  (this also proves binary expansions are unique)

## See also

Related files are:
* `data.list.lex`: Lexicographic order on lists.
* `data.pi.lex`: Lexicographic order on `Πₗ i, α i`.
* `data.psigma.order`: Lexicographic order on `Σ' i, α i`.
* `data.sigma.order`: Lexicographic order on `Σ i, α i`.
* `data.prod.lex`: Lexicographic order on `α × β`.

## Tags
colex, colexicographic, binary

## References
* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

-/


variable {α : Type _}

open Finset

open BigOperators

#print Finset.Colex /-
/-- We define this type synonym to refer to the colexicographic ordering on finsets
rather than the natural subset ordering.
-/
def Finset.Colex (α) :=
  Finset α deriving Inhabited
#align finset.colex Finset.Colex
-/

#print Finset.toColex /-
/-- A convenience constructor to turn a `finset α` into a `finset.colex α`, useful in order to
use the colex ordering rather than the subset ordering.
-/
def Finset.toColex {α} (s : Finset α) : Finset.Colex α :=
  s
#align finset.to_colex Finset.toColex
-/

#print Colex.eq_iff /-
@[simp]
theorem Colex.eq_iff (A B : Finset α) : A.toColex = B.toColex ↔ A = B :=
  Iff.rfl
#align colex.eq_iff Colex.eq_iff
-/

/-- `A` is less than `B` in the colex ordering if the largest thing that's not in both sets is in B.
In other words, `max (A ∆ B) ∈ B` (if the maximum exists).
-/
instance [LT α] : LT (Finset.Colex α) :=
  ⟨fun A B : Finset α => ∃ k : α, (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B⟩

/-- We can define (≤) in the obvious way. -/
instance [LT α] : LE (Finset.Colex α) :=
  ⟨fun A B => A < B ∨ A = B⟩

#print Colex.lt_def /-
theorem Colex.lt_def [LT α] (A B : Finset α) :
    A.toColex < B.toColex ↔ ∃ k, (∀ {x}, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A ∧ k ∈ B :=
  Iff.rfl
#align colex.lt_def Colex.lt_def
-/

#print Colex.le_def /-
theorem Colex.le_def [LT α] (A B : Finset α) :
    A.toColex ≤ B.toColex ↔ A.toColex < B.toColex ∨ A = B :=
  Iff.rfl
#align colex.le_def Colex.le_def
-/

#print Nat.sum_two_pow_lt /-
/-- If everything in `A` is less than `k`, we can bound the sum of powers. -/
theorem Nat.sum_two_pow_lt {k : ℕ} {A : Finset ℕ} (h₁ : ∀ {x}, x ∈ A → x < k) :
    A.Sum (pow 2) < 2 ^ k :=
  by
  apply lt_of_le_of_lt (sum_le_sum_of_subset fun t => mem_range.2 ∘ h₁)
  have z := geom_sum_mul_add 1 k
  rw [mul_one, one_add_one_eq_two] at z
  rw [← z]
  apply Nat.lt_succ_self
#align nat.sum_two_pow_lt Nat.sum_two_pow_lt
-/

namespace Colex

#print Colex.hom_lt_iff /-
/-- Strictly monotone functions preserve the colex ordering. -/
theorem hom_lt_iff {β : Type _} [LinearOrder α] [DecidableEq β] [Preorder β] {f : α → β}
    (h₁ : StrictMono f) (A B : Finset α) :
    (A.image f).toColex < (B.image f).toColex ↔ A.toColex < B.toColex :=
  by
  simp only [Colex.lt_def, not_exists, mem_image, exists_prop, not_and]
  constructor
  · rintro ⟨k, z, q, k', _, rfl⟩
    exact
      ⟨k', fun x hx => by simpa [h₁.injective.eq_iff] using z (h₁ hx), fun t => q _ t rfl, ‹k' ∈ B›⟩
  rintro ⟨k, z, ka, _⟩
  refine' ⟨f k, fun x hx => _, _, k, ‹k ∈ B›, rfl⟩
  · constructor
    any_goals
      rintro ⟨x', hx', rfl⟩
      refine' ⟨x', _, rfl⟩
      first |rwa [← z _]|rwa [z _]
      rwa [StrictMono.lt_iff_lt h₁] at hx
  · simp only [h₁.injective, Function.Injective.eq_iff]
    exact fun x hx => ne_of_mem_of_not_mem hx ka
#align colex.hom_lt_iff Colex.hom_lt_iff
-/

/- warning: colex.hom_fin_lt_iff -> Colex.hom_fin_lt_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (A : Finset.{0} (Fin n)) (B : Finset.{0} (Fin n)), Iff (LT.lt.{0} (Finset.Colex.{0} Nat) (Finset.Colex.hasLt.{0} Nat Nat.hasLt) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (i : Fin n) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) A)) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (i : Fin n) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) B))) (LT.lt.{0} (Finset.Colex.{0} (Fin n)) (Finset.Colex.hasLt.{0} (Fin n) (Fin.hasLt n)) (Finset.toColex.{0} (Fin n) A) (Finset.toColex.{0} (Fin n) B))
but is expected to have type
  forall {n : Nat} (A : Finset.{0} (Fin n)) (B : Finset.{0} (Fin n)), Iff (LT.lt.{0} (Finset.Colex.{0} Nat) (instLTColex.{0} Nat instLTNat) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (i : Fin n) => Fin.val n i) A)) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (i : Fin n) => Fin.val n i) B))) (LT.lt.{0} (Finset.Colex.{0} (Fin n)) (instLTColex.{0} (Fin n) (instLTFin n)) (Finset.toColex.{0} (Fin n) A) (Finset.toColex.{0} (Fin n) B))
Case conversion may be inaccurate. Consider using '#align colex.hom_fin_lt_iff Colex.hom_fin_lt_iffₓ'. -/
/-- A special case of `colex.hom_lt_iff` which is sometimes useful. -/
@[simp]
theorem hom_fin_lt_iff {n : ℕ} (A B : Finset (Fin n)) :
    (A.image fun i : Fin n => (i : ℕ)).toColex < (B.image fun i : Fin n => (i : ℕ)).toColex ↔
      A.toColex < B.toColex :=
  Colex.hom_lt_iff (fun x y k => k) _ _
#align colex.hom_fin_lt_iff Colex.hom_fin_lt_iff

instance [LT α] : IsIrrefl (Finset.Colex α) (· < ·) :=
  ⟨fun A h => Exists.elim h fun _ ⟨_, a, b⟩ => a b⟩

#print Colex.lt_trans /-
@[trans]
theorem lt_trans [LinearOrder α] {a b c : Finset.Colex α} : a < b → b < c → a < c :=
  by
  rintro ⟨k₁, k₁z, notinA, inB⟩ ⟨k₂, k₂z, notinB, inC⟩
  cases lt_or_gt_of_ne (ne_of_mem_of_not_mem inB notinB)
  · refine' ⟨k₂, fun x hx => _, by rwa [k₁z h], inC⟩
    rw [← k₂z hx]
    apply k₁z (trans h hx)
  · refine' ⟨k₁, fun x hx => _, notinA, by rwa [← k₂z h]⟩
    rw [k₁z hx]
    apply k₂z (trans h hx)
#align colex.lt_trans Colex.lt_trans
-/

#print Colex.le_trans /-
@[trans]
theorem le_trans [LinearOrder α] (a b c : Finset.Colex α) : a ≤ b → b ≤ c → a ≤ c := fun AB BC =>
  AB.elim (fun k => BC.elim (fun t => Or.inl (lt_trans k t)) fun t => t ▸ AB) fun k => k.symm ▸ BC
#align colex.le_trans Colex.le_trans
-/

instance [LinearOrder α] : IsTrans (Finset.Colex α) (· < ·) :=
  ⟨fun _ _ _ => Colex.lt_trans⟩

#print Colex.lt_trichotomy /-
theorem lt_trichotomy [LinearOrder α] (A B : Finset.Colex α) : A < B ∨ A = B ∨ B < A :=
  by
  by_cases h₁ : A = B
  · tauto
  rcases exists_max_image (A \ B ∪ B \ A) id _ with ⟨k, hk, z⟩
  · simp only [mem_union, mem_sdiff] at hk
    cases hk
    · right
      right
      refine' ⟨k, fun t th => _, hk.2, hk.1⟩
      specialize z t
      by_contra h₂
      simp only [mem_union, mem_sdiff, id.def] at z
      rw [not_iff, iff_iff_and_or_not_and_not, Classical.not_not, and_comm'] at h₂
      apply not_le_of_lt th (z h₂)
    · left
      refine' ⟨k, fun t th => _, hk.2, hk.1⟩
      specialize z t
      by_contra h₃
      simp only [mem_union, mem_sdiff, id.def] at z
      rw [not_iff, iff_iff_and_or_not_and_not, Classical.not_not, and_comm', or_comm'] at h₃
      apply not_le_of_lt th (z h₃)
  rw [nonempty_iff_ne_empty]
  intro a
  simp only [union_eq_empty_iff, sdiff_eq_empty_iff_subset] at a
  apply h₁ (subset.antisymm a.1 a.2)
#align colex.lt_trichotomy Colex.lt_trichotomy
-/

instance [LinearOrder α] : IsTrichotomous (Finset.Colex α) (· < ·) :=
  ⟨lt_trichotomy⟩

#print Colex.decidableLt /-
instance decidableLt [LinearOrder α] : ∀ {A B : Finset.Colex α}, Decidable (A < B) :=
  show ∀ A B : Finset α, Decidable (A.toColex < B.toColex) from fun A B =>
    decidable_of_iff' (∃ k ∈ B, (∀ x ∈ A ∪ B, k < x → (x ∈ A ↔ x ∈ B)) ∧ k ∉ A)
      (by
        rw [Colex.lt_def]
        apply exists_congr
        simp only [mem_union, exists_prop, or_imp, and_comm' (_ ∈ B), and_assoc']
        intro k
        refine' and_congr_left' (forall_congr' _)
        tauto)
#align colex.decidable_lt Colex.decidableLt
-/

instance [LinearOrder α] : LinearOrder (Finset.Colex α) :=
  { Finset.Colex.hasLt,
    Finset.Colex.hasLe with
    le_refl := fun A => Or.inr rfl
    le_trans := le_trans
    le_antisymm := fun A B AB BA =>
      AB.elim (fun k => BA.elim (fun t => (asymm k t).elim) fun t => t.symm) id
    le_total := fun A B =>
      (lt_trichotomy A B).elim3 (Or.inl ∘ Or.inl) (Or.inl ∘ Or.inr) (Or.inr ∘ Or.inl)
    decidableLe := fun A B => by infer_instance
    decidableLt := fun A B => by infer_instance
    DecidableEq := fun A B => by infer_instance
    lt_iff_le_not_le := fun A B => by
      constructor
      · intro t
        refine' ⟨Or.inl t, _⟩
        rintro (i | rfl)
        · apply asymm_of _ t i
        · apply irrefl _ t
      rintro ⟨h₁ | rfl, h₂⟩
      · apply h₁
      apply h₂.elim (Or.inr rfl) }

/-- The instances set up let us infer that `colex.lt` is a strict total order. -/
example [LinearOrder α] : IsStrictTotalOrder (Finset.Colex α) (· < ·) :=
  inferInstance

/- warning: colex.hom_le_iff -> Colex.hom_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β}, (StrictMono.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) f) -> (forall (A : Finset.{u1} α) (B : Finset.{u1} α), Iff (LE.le.{u2} (Finset.Colex.{u2} β) (Finset.Colex.hasLe.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (Finset.toColex.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => Eq.decidable.{u2} β _inst_2 a b) f A)) (Finset.toColex.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => Eq.decidable.{u2} β _inst_2 a b) f B))) (LE.le.{u1} (Finset.Colex.{u1} α) (Finset.Colex.hasLe.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.toColex.{u1} α A) (Finset.toColex.{u1} α B)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : LinearOrder.{u2} β] {f : α -> β}, (StrictMono.{u1, u2} α β (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))) f) -> (forall (A : Finset.{u1} α) (B : Finset.{u1} α), Iff (LE.le.{u2} (Finset.Colex.{u2} β) (instLEColex.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))))))) (Finset.toColex.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => instDecidableEq.{u2} β _inst_2 a b) f A)) (Finset.toColex.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => instDecidableEq.{u2} β _inst_2 a b) f B))) (LE.le.{u1} (Finset.Colex.{u1} α) (instLEColex.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.toColex.{u1} α A) (Finset.toColex.{u1} α B)))
Case conversion may be inaccurate. Consider using '#align colex.hom_le_iff Colex.hom_le_iffₓ'. -/
/-- Strictly monotone functions preserve the colex ordering. -/
theorem hom_le_iff {β : Type _} [LinearOrder α] [LinearOrder β] {f : α → β} (h₁ : StrictMono f)
    (A B : Finset α) : (A.image f).toColex ≤ (B.image f).toColex ↔ A.toColex ≤ B.toColex := by
  rw [le_iff_le_iff_lt_iff_lt, hom_lt_iff h₁]
#align colex.hom_le_iff Colex.hom_le_iff

/- warning: colex.hom_fin_le_iff -> Colex.hom_fin_le_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (A : Finset.{0} (Fin n)) (B : Finset.{0} (Fin n)), Iff (LE.le.{0} (Finset.Colex.{0} Nat) (Finset.Colex.hasLe.{0} Nat Nat.hasLt) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (i : Fin n) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) A)) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) (fun (i : Fin n) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) B))) (LE.le.{0} (Finset.Colex.{0} (Fin n)) (Finset.Colex.hasLe.{0} (Fin n) (Fin.hasLt n)) (Finset.toColex.{0} (Fin n) A) (Finset.toColex.{0} (Fin n) B))
but is expected to have type
  forall {n : Nat} (A : Finset.{0} (Fin n)) (B : Finset.{0} (Fin n)), Iff (LE.le.{0} (Finset.Colex.{0} Nat) (instLEColex.{0} Nat instLTNat) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (i : Fin n) => Fin.val n i) A)) (Finset.toColex.{0} Nat (Finset.image.{0, 0} (Fin n) Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) (fun (i : Fin n) => Fin.val n i) B))) (LE.le.{0} (Finset.Colex.{0} (Fin n)) (instLEColex.{0} (Fin n) (instLTFin n)) (Finset.toColex.{0} (Fin n) A) (Finset.toColex.{0} (Fin n) B))
Case conversion may be inaccurate. Consider using '#align colex.hom_fin_le_iff Colex.hom_fin_le_iffₓ'. -/
/-- A special case of `colex_hom` which is sometimes useful. -/
@[simp]
theorem hom_fin_le_iff {n : ℕ} (A B : Finset (Fin n)) :
    (A.image fun i : Fin n => (i : ℕ)).toColex ≤ (B.image fun i : Fin n => (i : ℕ)).toColex ↔
      A.toColex ≤ B.toColex :=
  Colex.hom_le_iff (fun x y k => k) _ _
#align colex.hom_fin_le_iff Colex.hom_fin_le_iff

#print Colex.forall_lt_of_colex_lt_of_forall_lt /-
/-- If `A` is before `B` in colex, and everything in `B` is small, then everything in `A` is small.
-/
theorem forall_lt_of_colex_lt_of_forall_lt [LinearOrder α] {A B : Finset α} (t : α)
    (h₁ : A.toColex < B.toColex) (h₂ : ∀ x ∈ B, x < t) : ∀ x ∈ A, x < t :=
  by
  rw [Colex.lt_def] at h₁
  rcases h₁ with ⟨k, z, _, _⟩
  intro x hx
  apply lt_of_not_ge
  intro a
  refine' not_lt_of_ge a (h₂ x _)
  rwa [← z]
  apply lt_of_lt_of_le (h₂ k ‹_›) a
#align colex.forall_lt_of_colex_lt_of_forall_lt Colex.forall_lt_of_colex_lt_of_forall_lt
-/

#print Colex.lt_singleton_iff_mem_lt /-
/-- `s.to_colex < {r}.to_colex` iff all elements of `s` are less than `r`. -/
theorem lt_singleton_iff_mem_lt [LinearOrder α] {r : α} {s : Finset α} :
    s.toColex < ({r} : Finset α).toColex ↔ ∀ x ∈ s, x < r :=
  by
  simp only [lt_def, mem_singleton, ← and_assoc', exists_eq_right]
  constructor
  · intro t x hx
    rw [← not_le]
    intro h
    rcases lt_or_eq_of_le h with (h₁ | rfl)
    · exact ne_of_irrefl h₁ ((t.1 h₁).1 hx).symm
    · exact t.2 hx
  ·
    exact fun h =>
      ⟨fun z hz => ⟨fun i => (asymm hz (h _ i)).elim, fun i => (hz.ne' i).elim⟩, by simpa using h r⟩
#align colex.lt_singleton_iff_mem_lt Colex.lt_singleton_iff_mem_lt
-/

/- warning: colex.mem_le_of_singleton_le -> Colex.mem_le_of_singleton_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {r : α} {s : Finset.{u1} α}, Iff (LE.le.{u1} (Finset.Colex.{u1} α) (Finset.Colex.hasLe.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.toColex.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) r)) (Finset.toColex.{u1} α s)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) r x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {r : α} {s : Finset.{u1} α}, Iff (LE.le.{u1} (Finset.Colex.{u1} α) (instLEColex.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.toColex.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) r)) (Finset.toColex.{u1} α s)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) r x)))
Case conversion may be inaccurate. Consider using '#align colex.mem_le_of_singleton_le Colex.mem_le_of_singleton_leₓ'. -/
/-- If {r} is less than or equal to s in the colexicographical sense,
  then s contains an element greater than or equal to r. -/
theorem mem_le_of_singleton_le [LinearOrder α] {r : α} {s : Finset α} :
    ({r} : Finset α).toColex ≤ s.toColex ↔ ∃ x ∈ s, r ≤ x :=
  by
  rw [← not_lt]
  simp [lt_singleton_iff_mem_lt]
#align colex.mem_le_of_singleton_le Colex.mem_le_of_singleton_le

#print Colex.singleton_lt_iff_lt /-
/-- Colex is an extension of the base ordering on α. -/
theorem singleton_lt_iff_lt [LinearOrder α] {r s : α} :
    ({r} : Finset α).toColex < ({s} : Finset α).toColex ↔ r < s := by simp [lt_singleton_iff_mem_lt]
#align colex.singleton_lt_iff_lt Colex.singleton_lt_iff_lt
-/

#print Colex.singleton_le_iff_le /-
/-- Colex is an extension of the base ordering on α. -/
theorem singleton_le_iff_le [LinearOrder α] {r s : α} :
    ({r} : Finset α).toColex ≤ ({s} : Finset α).toColex ↔ r ≤ s := by
  rw [le_iff_le_iff_lt_iff_lt, singleton_lt_iff_lt]
#align colex.singleton_le_iff_le Colex.singleton_le_iff_le
-/

#print Colex.sdiff_lt_sdiff_iff_lt /-
/-- Colex doesn't care if you remove the other set -/
@[simp]
theorem sdiff_lt_sdiff_iff_lt [LT α] [DecidableEq α] (A B : Finset α) :
    (A \ B).toColex < (B \ A).toColex ↔ A.toColex < B.toColex :=
  by
  rw [Colex.lt_def, Colex.lt_def]
  apply exists_congr
  intro k
  simp only [mem_sdiff, not_and, Classical.not_not]
  constructor
  · rintro ⟨z, kAB, kB, kA⟩
    refine' ⟨_, kA, kB⟩
    · intro x hx
      specialize z hx
      tauto
  · rintro ⟨z, kA, kB⟩
    refine' ⟨_, fun _ => kB, kB, kA⟩
    intro x hx
    rw [z hx]
#align colex.sdiff_lt_sdiff_iff_lt Colex.sdiff_lt_sdiff_iff_lt
-/

/- warning: colex.sdiff_le_sdiff_iff_le -> Colex.sdiff_le_sdiff_iff_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (A : Finset.{u1} α) (B : Finset.{u1} α), Iff (LE.le.{u1} (Finset.Colex.{u1} α) (Finset.Colex.hasLe.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.toColex.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) A B)) (Finset.toColex.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => Eq.decidable.{u1} α _inst_1 a b)) B A))) (LE.le.{u1} (Finset.Colex.{u1} α) (Finset.Colex.hasLe.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))) (Finset.toColex.{u1} α A) (Finset.toColex.{u1} α B))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (A : Finset.{u1} α) (B : Finset.{u1} α), Iff (LE.le.{u1} (Finset.Colex.{u1} α) (instLEColex.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.toColex.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) A B)) (Finset.toColex.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => instDecidableEq.{u1} α _inst_1 a b)) B A))) (LE.le.{u1} (Finset.Colex.{u1} α) (instLEColex.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))) (Finset.toColex.{u1} α A) (Finset.toColex.{u1} α B))
Case conversion may be inaccurate. Consider using '#align colex.sdiff_le_sdiff_iff_le Colex.sdiff_le_sdiff_iff_leₓ'. -/
/-- Colex doesn't care if you remove the other set -/
@[simp]
theorem sdiff_le_sdiff_iff_le [LinearOrder α] (A B : Finset α) :
    (A \ B).toColex ≤ (B \ A).toColex ↔ A.toColex ≤ B.toColex := by
  rw [le_iff_le_iff_lt_iff_lt, sdiff_lt_sdiff_iff_lt]
#align colex.sdiff_le_sdiff_iff_le Colex.sdiff_le_sdiff_iff_le

#print Colex.empty_toColex_lt /-
theorem empty_toColex_lt [LinearOrder α] {A : Finset α} (hA : A.Nonempty) :
    (∅ : Finset α).toColex < A.toColex :=
  by
  rw [Colex.lt_def]
  refine' ⟨max' _ hA, _, by simp, max'_mem _ _⟩
  simp only [false_iff_iff, not_mem_empty]
  intro x hx t
  apply not_le_of_lt hx (le_max' _ _ t)
#align colex.empty_to_colex_lt Colex.empty_toColex_lt
-/

#print Colex.colex_lt_of_ssubset /-
/-- If `A ⊂ B`, then `A` is less than `B` in the colex order. Note the converse does not hold, as
`⊆` is not a linear order. -/
theorem colex_lt_of_ssubset [LinearOrder α] {A B : Finset α} (h : A ⊂ B) : A.toColex < B.toColex :=
  by
  rw [← sdiff_lt_sdiff_iff_lt, sdiff_eq_empty_iff_subset.2 h.1]
  exact empty_to_colex_lt (by simpa [Finset.Nonempty] using exists_of_ssubset h)
#align colex.colex_lt_of_ssubset Colex.colex_lt_of_ssubset
-/

#print Colex.empty_toColex_le /-
@[simp]
theorem empty_toColex_le [LinearOrder α] {A : Finset α} : (∅ : Finset α).toColex ≤ A.toColex :=
  by
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · simp
  · apply (empty_to_colex_lt hA).le
#align colex.empty_to_colex_le Colex.empty_toColex_le
-/

#print Colex.colex_le_of_subset /-
/-- If `A ⊆ B`, then `A ≤ B` in the colex order. Note the converse does not hold, as `⊆` is not a
linear order. -/
theorem colex_le_of_subset [LinearOrder α] {A B : Finset α} (h : A ⊆ B) : A.toColex ≤ B.toColex :=
  by
  rw [← sdiff_le_sdiff_iff_le, sdiff_eq_empty_iff_subset.2 h]
  apply empty_to_colex_le
#align colex.colex_le_of_subset Colex.colex_le_of_subset
-/

#print Colex.toColexRelHom /-
/-- The function from finsets to finsets with the colex order is a relation homomorphism. -/
@[simps]
def toColexRelHom [LinearOrder α] :
    ((· ⊆ ·) : Finset α → Finset α → Prop) →r ((· ≤ ·) : Finset.Colex α → Finset.Colex α → Prop)
    where
  toFun := Finset.toColex
  map_rel' A B := colex_le_of_subset
#align colex.to_colex_rel_hom Colex.toColexRelHom
-/

instance [LinearOrder α] : OrderBot (Finset.Colex α)
    where
  bot := (∅ : Finset α).toColex
  bot_le x := empty_toColex_le

instance [LinearOrder α] [Fintype α] : OrderTop (Finset.Colex α)
    where
  top := Finset.univ.toColex
  le_top x := colex_le_of_subset (subset_univ _)

instance [LinearOrder α] : Lattice (Finset.Colex α) :=
  { (by infer_instance : SemilatticeSup (Finset.Colex α)),
    (by infer_instance : SemilatticeInf (Finset.Colex α)) with }

instance [LinearOrder α] [Fintype α] : BoundedOrder (Finset.Colex α) :=
  { (by infer_instance : OrderTop (Finset.Colex α)),
    (by infer_instance : OrderBot (Finset.Colex α)) with }

#print Colex.sum_two_pow_lt_iff_lt /-
/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
theorem sum_two_pow_lt_iff_lt (A B : Finset ℕ) :
    ((∑ i in A, 2 ^ i) < ∑ i in B, 2 ^ i) ↔ A.toColex < B.toColex :=
  by
  have z : ∀ A B : Finset ℕ, A.toColex < B.toColex → (∑ i in A, 2 ^ i) < ∑ i in B, 2 ^ i :=
    by
    intro A B
    rw [← sdiff_lt_sdiff_iff_lt, Colex.lt_def]
    rintro ⟨k, z, kA, kB⟩
    rw [← sdiff_union_inter A B]
    conv_rhs => rw [← sdiff_union_inter B A]
    rw [sum_union (disjoint_sdiff_inter _ _), sum_union (disjoint_sdiff_inter _ _), inter_comm,
      add_lt_add_iff_right]
    apply lt_of_lt_of_le (@Nat.sum_two_pow_lt k (A \ B) _)
    · apply single_le_sum (fun _ _ => Nat.zero_le _) kB
    intro x hx
    apply lt_of_le_of_ne (le_of_not_lt fun kx => _)
    · apply ne_of_mem_of_not_mem hx kA
    have := (z kx).1 hx
    rw [mem_sdiff] at this hx
    exact hx.2 this.1
  refine'
    ⟨fun h => (lt_trichotomy A B).resolve_right fun h₁ => h₁.elim _ (not_lt_of_gt h ∘ z _ _), z A B⟩
  rintro rfl
  apply irrefl _ h
#align colex.sum_two_pow_lt_iff_lt Colex.sum_two_pow_lt_iff_lt
-/

#print Colex.sum_two_pow_le_iff_lt /-
/-- For subsets of ℕ, we can show that colex is equivalent to binary. -/
theorem sum_two_pow_le_iff_lt (A B : Finset ℕ) :
    ((∑ i in A, 2 ^ i) ≤ ∑ i in B, 2 ^ i) ↔ A.toColex ≤ B.toColex := by
  rw [le_iff_le_iff_lt_iff_lt, sum_two_pow_lt_iff_lt]
#align colex.sum_two_pow_le_iff_lt Colex.sum_two_pow_le_iff_lt
-/

end Colex

