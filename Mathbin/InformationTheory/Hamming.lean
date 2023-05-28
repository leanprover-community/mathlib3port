/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson

! This file was ported from Lean 3 source module information_theory.hamming
! leanprover-community/mathlib commit cb3ceec8485239a61ed51d944cb9a95b68c6bafc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic

/-!
# Hamming spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hamming_dist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hamming_norm x`: the Hamming norm of `x`, the number of non-zero entries.
* `hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `hamming.to_hamming`, `hamming.of_hamming`: functions for casting between `hamming β` and
`Π i, β i`.
* `hamming.normed_add_comm_group`: the Hamming norm forms a normed group on `hamming β`.
-/


section HammingDistNorm

open Finset Function

variable {α ι : Type _} {β : ι → Type _} [Fintype ι] [∀ i, DecidableEq (β i)]

variable {γ : ι → Type _} [∀ i, DecidableEq (γ i)]

#print hammingDist /-
/-- The Hamming distance function to the naturals. -/
def hammingDist (x y : ∀ i, β i) : ℕ :=
  (univ.filterₓ fun i => x i ≠ y i).card
#align hamming_dist hammingDist
-/

/- warning: hamming_dist_self -> hammingDist_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x x) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x x) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align hamming_dist_self hammingDist_selfₓ'. -/
/-- Corresponds to `dist_self`. -/
@[simp]
theorem hammingDist_self (x : ∀ i, β i) : hammingDist x x = 0 := by
  rw [hammingDist, card_eq_zero, filter_eq_empty_iff]; exact fun _ _ H => H rfl
#align hamming_dist_self hammingDist_self

/- warning: hamming_dist_nonneg -> hammingDist_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_nonneg hammingDist_nonnegₓ'. -/
/-- Corresponds to `dist_nonneg`. -/
theorem hammingDist_nonneg {x y : ∀ i, β i} : 0 ≤ hammingDist x y :=
  zero_le _
#align hamming_dist_nonneg hammingDist_nonneg

/- warning: hamming_dist_comm -> hammingDist_comm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) y x)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) y x)
Case conversion may be inaccurate. Consider using '#align hamming_dist_comm hammingDist_commₓ'. -/
/-- Corresponds to `dist_comm`. -/
theorem hammingDist_comm (x y : ∀ i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]
#align hamming_dist_comm hammingDist_comm

/- warning: hamming_dist_triangle -> hammingDist_triangle is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i) (z : forall (i : ι), β i), LE.le.{0} Nat Nat.hasLe (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x z) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) y z))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i) (z : forall (i : ι), β i), LE.le.{0} Nat instLENat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x z) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) y z))
Case conversion may be inaccurate. Consider using '#align hamming_dist_triangle hammingDist_triangleₓ'. -/
/-- Corresponds to `dist_triangle`. -/
theorem hammingDist_triangle (x y z : ∀ i, β i) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  classical
    simp_rw [hammingDist]
    refine' le_trans (card_mono _) (card_union_le _ _)
    rw [← filter_or]
    refine' monotone_filter_right _ _
    intro i h
    by_contra' H
    exact h (Eq.trans H.1 H.2)
#align hamming_dist_triangle hammingDist_triangle

/- warning: hamming_dist_triangle_left -> hammingDist_triangle_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i) (z : forall (i : ι), β i), LE.le.{0} Nat Nat.hasLe (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) z x) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) z y))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i) (z : forall (i : ι), β i), LE.le.{0} Nat instLENat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) z x) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) z y))
Case conversion may be inaccurate. Consider using '#align hamming_dist_triangle_left hammingDist_triangle_leftₓ'. -/
/-- Corresponds to `dist_triangle_left`. -/
theorem hammingDist_triangle_left (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist z x + hammingDist z y := by rw [hammingDist_comm z];
  exact hammingDist_triangle _ _ _
#align hamming_dist_triangle_left hammingDist_triangle_left

/- warning: hamming_dist_triangle_right -> hammingDist_triangle_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i) (z : forall (i : ι), β i), LE.le.{0} Nat Nat.hasLe (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x z) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) y z))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i) (z : forall (i : ι), β i), LE.le.{0} Nat instLENat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x z) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) y z))
Case conversion may be inaccurate. Consider using '#align hamming_dist_triangle_right hammingDist_triangle_rightₓ'. -/
/-- Corresponds to `dist_triangle_right`. -/
theorem hammingDist_triangle_right (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist x z + hammingDist y z := by rw [hammingDist_comm y];
  exact hammingDist_triangle _ _ _
#align hamming_dist_triangle_right hammingDist_triangle_right

/- warning: swap_hamming_dist -> swap_hammingDist is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)], Eq.{max (max (succ u1) (succ u2)) 1} ((forall (i : ι), β i) -> (forall (i : ι), β i) -> Nat) (Function.swap.{max (succ u1) (succ u2), max (succ u1) (succ u2), 1} (forall (i : ι), β i) (forall (i : ι), β i) (fun (x : forall (i : ι), β i) (y : forall (i : ι), β i) => Nat) (hammingDist.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b))) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)], Eq.{max (succ u2) (succ u1)} ((forall (i : ι), β i) -> (forall (i : ι), β i) -> Nat) (Function.swap.{max (succ u2) (succ u1), max (succ u2) (succ u1), 1} (forall (i : ι), β i) (forall (i : ι), β i) (fun (x : forall (i : ι), β i) (y : forall (i : ι), β i) => Nat) (hammingDist.{u2, u1} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b))) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b))
Case conversion may be inaccurate. Consider using '#align swap_hamming_dist swap_hammingDistₓ'. -/
/-- Corresponds to `swap_dist`. -/
theorem swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist := by funext x y;
  exact hammingDist_comm _ _
#align swap_hamming_dist swap_hammingDist

/- warning: eq_of_hamming_dist_eq_zero -> eq_of_hammingDist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, (Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, (Eq.{1} Nat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align eq_of_hamming_dist_eq_zero eq_of_hammingDist_eq_zeroₓ'. -/
/-- Corresponds to `eq_of_dist_eq_zero`. -/
theorem eq_of_hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 → x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]
#align eq_of_hamming_dist_eq_zero eq_of_hammingDist_eq_zero

/- warning: hamming_dist_eq_zero -> hammingDist_eq_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Eq.{1} Nat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_eq_zero hammingDist_eq_zeroₓ'. -/
/-- Corresponds to `dist_eq_zero`. -/
@[simp]
theorem hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hammingDist_eq_zero, fun H => by rw [H]; exact hammingDist_self _⟩
#align hamming_dist_eq_zero hammingDist_eq_zero

/- warning: hamming_zero_eq_dist -> hamming_zero_eq_dist is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Eq.{1} Nat (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Eq.{1} Nat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align hamming_zero_eq_dist hamming_zero_eq_distₓ'. -/
/-- Corresponds to `zero_eq_dist`. -/
@[simp]
theorem hamming_zero_eq_dist {x y : ∀ i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm, hammingDist_eq_zero]
#align hamming_zero_eq_dist hamming_zero_eq_dist

/- warning: hamming_dist_ne_zero -> hammingDist_ne_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Ne.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Ne.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Ne.{1} Nat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Ne.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_ne_zero hammingDist_ne_zeroₓ'. -/
/-- Corresponds to `dist_ne_zero`. -/
theorem hammingDist_ne_zero {x y : ∀ i, β i} : hammingDist x y ≠ 0 ↔ x ≠ y :=
  hammingDist_eq_zero.Not
#align hamming_dist_ne_zero hammingDist_ne_zero

/- warning: hamming_dist_pos -> hammingDist_pos is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)) (Ne.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)) (Ne.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_pos hammingDist_posₓ'. -/
/-- Corresponds to `dist_pos`. -/
@[simp]
theorem hammingDist_pos {x y : ∀ i, β i} : 0 < hammingDist x y ↔ x ≠ y := by
  rw [← hammingDist_ne_zero, iff_not_comm, not_lt, le_zero_iff]
#align hamming_dist_pos hammingDist_pos

/- warning: hamming_dist_lt_one -> hammingDist_lt_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (LT.lt.{0} Nat Nat.hasLt (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (LT.lt.{0} Nat instLTNat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_lt_one hammingDist_lt_oneₓ'. -/
@[simp]
theorem hammingDist_lt_one {x y : ∀ i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff, hammingDist_eq_zero]
#align hamming_dist_lt_one hammingDist_lt_one

/- warning: hamming_dist_le_card_fintype -> hammingDist_le_card_fintype is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, LE.le.{0} Nat Nat.hasLe (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (Fintype.card.{u1} ι _inst_1)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] {x : forall (i : ι), β i} {y : forall (i : ι), β i}, LE.le.{0} Nat instLENat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (Fintype.card.{u2} ι _inst_1)
Case conversion may be inaccurate. Consider using '#align hamming_dist_le_card_fintype hammingDist_le_card_fintypeₓ'. -/
theorem hammingDist_le_card_fintype {x y : ∀ i, β i} : hammingDist x y ≤ Fintype.card ι :=
  card_le_univ _
#align hamming_dist_le_card_fintype hammingDist_le_card_fintype

/- warning: hamming_dist_comp_le_hamming_dist -> hammingDist_comp_le_hammingDist is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {γ : ι -> Type.{u3}} [_inst_3 : forall (i : ι), DecidableEq.{succ u3} (γ i)] (f : forall (i : ι), (γ i) -> (β i)) {x : forall (i : ι), γ i} {y : forall (i : ι), γ i}, LE.le.{0} Nat Nat.hasLe (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => f i (x i)) (fun (i : ι) => f i (y i))) (hammingDist.{u1, u3} ι (fun (i : ι) => γ i) _inst_1 (fun (i : ι) (a : γ i) (b : γ i) => _inst_3 i a b) x y)
but is expected to have type
  forall {ι : Type.{u3}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u3} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {γ : ι -> Type.{u1}} [_inst_3 : forall (i : ι), DecidableEq.{succ u1} (γ i)] (f : forall (i : ι), (γ i) -> (β i)) {x : forall (i : ι), γ i} {y : forall (i : ι), γ i}, LE.le.{0} Nat instLENat (hammingDist.{u3, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => f i (x i)) (fun (i : ι) => f i (y i))) (hammingDist.{u3, u1} ι (fun (i : ι) => γ i) _inst_1 (fun (i : ι) (a : γ i) (b : γ i) => _inst_3 i a b) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_comp_le_hamming_dist hammingDist_comp_le_hammingDistₓ'. -/
theorem hammingDist_comp_le_hammingDist (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) ≤ hammingDist x y :=
  card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| congr_arg (f i) H2)
#align hamming_dist_comp_le_hamming_dist hammingDist_comp_le_hammingDist

#print hammingDist_comp /-
theorem hammingDist_comp (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} (hf : ∀ i, Injective (f i)) :
    (hammingDist (fun i => f i (x i)) fun i => f i (y i)) = hammingDist x y :=
  by
  refine' le_antisymm (hammingDist_comp_le_hammingDist _) _
  exact card_mono (monotone_filter_right _ fun i H1 H2 => H1 <| hf i H2)
#align hamming_dist_comp hammingDist_comp
-/

/- warning: hamming_dist_smul_le_hamming_dist -> hammingDist_smul_le_hammingDist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : ι -> Type.{u3}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u3} (β i)] [_inst_4 : forall (i : ι), SMul.{u1, u3} α (β i)] {k : α} {x : forall (i : ι), β i} {y : forall (i : ι), β i}, LE.le.{0} Nat Nat.hasLe (hammingDist.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)) k x) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)) k y)) (hammingDist.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), SMul.{u3, u2} α (β i)] {k : α} {x : forall (i : ι), β i} {y : forall (i : ι), β i}, LE.le.{0} Nat instLENat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))) k x) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))) k y)) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y)
Case conversion may be inaccurate. Consider using '#align hamming_dist_smul_le_hamming_dist hammingDist_smul_le_hammingDistₓ'. -/
theorem hammingDist_smul_le_hammingDist [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i} :
    hammingDist (k • x) (k • y) ≤ hammingDist x y :=
  hammingDist_comp_le_hammingDist fun i => (· • ·) k
#align hamming_dist_smul_le_hamming_dist hammingDist_smul_le_hammingDist

/- warning: hamming_dist_smul -> hammingDist_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : ι -> Type.{u3}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u3} (β i)] [_inst_4 : forall (i : ι), SMul.{u1, u3} α (β i)] {k : α} {x : forall (i : ι), β i} {y : forall (i : ι), β i}, (forall (i : ι), IsSMulRegular.{u1, u3} α (β i) (_inst_4 i) k) -> (Eq.{1} Nat (hammingDist.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)) k x) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)) k y)) (hammingDist.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), SMul.{u3, u2} α (β i)] {k : α} {x : forall (i : ι), β i} {y : forall (i : ι), β i}, (forall (i : ι), IsSMulRegular.{u3, u2} α (β i) (_inst_4 i) k) -> (Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))) k x) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))) k y)) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y))
Case conversion may be inaccurate. Consider using '#align hamming_dist_smul hammingDist_smulₓ'. -/
/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
theorem hammingDist_smul [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i}
    (hk : ∀ i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist x y :=
  hammingDist_comp (fun i => (· • ·) k) hk
#align hamming_dist_smul hammingDist_smul

section Zero

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

#print hammingNorm /-
/-- The Hamming weight function to the naturals. -/
def hammingNorm (x : ∀ i, β i) : ℕ :=
  (univ.filterₓ fun i => x i ≠ 0).card
#align hamming_norm hammingNorm
-/

/- warning: hamming_dist_zero_right -> hammingDist_zero_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] (x : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] (x : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))) (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)
Case conversion may be inaccurate. Consider using '#align hamming_dist_zero_right hammingDist_zero_rightₓ'. -/
/-- Corresponds to `dist_zero_right`. -/
@[simp]
theorem hammingDist_zero_right (x : ∀ i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl
#align hamming_dist_zero_right hammingDist_zero_right

/- warning: hamming_dist_zero_left -> hammingDist_zero_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)], Eq.{max (max (succ u1) (succ u2)) 1} ((forall (i : ι), β i) -> Nat) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)], Eq.{max (succ u2) (succ u1)} ((forall (i : ι), β i) -> Nat) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))) (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i))
Case conversion may be inaccurate. Consider using '#align hamming_dist_zero_left hammingDist_zero_leftₓ'. -/
/-- Corresponds to `dist_zero_left`. -/
@[simp]
theorem hammingDist_zero_left : hammingDist (0 : ∀ i, β i) = hammingNorm :=
  funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]
#align hamming_dist_zero_left hammingDist_zero_left

/- warning: hamming_norm_nonneg -> hammingNorm_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] {x : forall (i : ι), β i}, LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] {x : forall (i : ι), β i}, LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)
Case conversion may be inaccurate. Consider using '#align hamming_norm_nonneg hammingNorm_nonnegₓ'. -/
/-- Corresponds to `norm_nonneg`. -/
@[simp]
theorem hammingNorm_nonneg {x : ∀ i, β i} : 0 ≤ hammingNorm x :=
  zero_le _
#align hamming_norm_nonneg hammingNorm_nonneg

/- warning: hamming_norm_zero -> hammingNorm_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)], Eq.{1} Nat (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)], Eq.{1} Nat (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))
Case conversion may be inaccurate. Consider using '#align hamming_norm_zero hammingNorm_zeroₓ'. -/
/-- Corresponds to `norm_zero`. -/
@[simp]
theorem hammingNorm_zero : hammingNorm (0 : ∀ i, β i) = 0 :=
  hammingDist_self _
#align hamming_norm_zero hammingNorm_zero

/- warning: hamming_norm_eq_zero -> hammingNorm_eq_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] {x : forall (i : ι), β i}, Iff (Eq.{1} Nat (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] {x : forall (i : ι), β i}, Iff (Eq.{1} Nat (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))
Case conversion may be inaccurate. Consider using '#align hamming_norm_eq_zero hammingNorm_eq_zeroₓ'. -/
/-- Corresponds to `norm_eq_zero`. -/
@[simp]
theorem hammingNorm_eq_zero {x : ∀ i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hammingDist_eq_zero
#align hamming_norm_eq_zero hammingNorm_eq_zero

/- warning: hamming_norm_ne_zero_iff -> hammingNorm_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] {x : forall (i : ι), β i}, Iff (Ne.{1} Nat (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Ne.{max (succ u1) (succ u2)} (forall (i : ι), β i) x (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] {x : forall (i : ι), β i}, Iff (Ne.{1} Nat (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Ne.{max (succ u2) (succ u1)} (forall (i : ι), β i) x (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))
Case conversion may be inaccurate. Consider using '#align hamming_norm_ne_zero_iff hammingNorm_ne_zero_iffₓ'. -/
/-- Corresponds to `norm_ne_zero_iff`. -/
theorem hammingNorm_ne_zero_iff {x : ∀ i, β i} : hammingNorm x ≠ 0 ↔ x ≠ 0 :=
  hammingNorm_eq_zero.Not
#align hamming_norm_ne_zero_iff hammingNorm_ne_zero_iff

/- warning: hamming_norm_pos_iff -> hammingNorm_pos_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] {x : forall (i : ι), β i}, Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)) (Ne.{max (succ u1) (succ u2)} (forall (i : ι), β i) x (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] {x : forall (i : ι), β i}, Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)) (Ne.{max (succ u2) (succ u1)} (forall (i : ι), β i) x (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))
Case conversion may be inaccurate. Consider using '#align hamming_norm_pos_iff hammingNorm_pos_iffₓ'. -/
/-- Corresponds to `norm_pos_iff`. -/
@[simp]
theorem hammingNorm_pos_iff {x : ∀ i, β i} : 0 < hammingNorm x ↔ x ≠ 0 :=
  hammingDist_pos
#align hamming_norm_pos_iff hammingNorm_pos_iff

/- warning: hamming_norm_lt_one -> hammingNorm_lt_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] {x : forall (i : ι), β i}, Iff (LT.lt.{0} Nat Nat.hasLt (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x (OfNat.ofNat.{max u1 u2} (forall (i : ι), β i) 0 (OfNat.mk.{max u1 u2} (forall (i : ι), β i) 0 (Zero.zero.{max u1 u2} (forall (i : ι), β i) (Pi.instZero.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i))))))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] {x : forall (i : ι), β i}, Iff (LT.lt.{0} Nat instLTNat (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x (OfNat.ofNat.{max u2 u1} (forall (i : ι), β i) 0 (Zero.toOfNat0.{max u2 u1} (forall (i : ι), β i) (Pi.instZero.{u2, u1} ι (fun (i : ι) => β i) (fun (i : ι) => _inst_4 i)))))
Case conversion may be inaccurate. Consider using '#align hamming_norm_lt_one hammingNorm_lt_oneₓ'. -/
@[simp]
theorem hammingNorm_lt_one {x : ∀ i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hammingDist_lt_one
#align hamming_norm_lt_one hammingNorm_lt_one

/- warning: hamming_norm_le_card_fintype -> hammingNorm_le_card_fintype is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] {x : forall (i : ι), β i}, LE.le.{0} Nat Nat.hasLe (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (Fintype.card.{u1} ι _inst_1)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] [_inst_4 : forall (i : ι), Zero.{u1} (β i)] {x : forall (i : ι), β i}, LE.le.{0} Nat instLENat (hammingNorm.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x) (Fintype.card.{u2} ι _inst_1)
Case conversion may be inaccurate. Consider using '#align hamming_norm_le_card_fintype hammingNorm_le_card_fintypeₓ'. -/
theorem hammingNorm_le_card_fintype {x : ∀ i, β i} : hammingNorm x ≤ Fintype.card ι :=
  hammingDist_le_card_fintype
#align hamming_norm_le_card_fintype hammingNorm_le_card_fintype

/- warning: hamming_norm_comp_le_hamming_norm -> hammingNorm_comp_le_hammingNorm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] {γ : ι -> Type.{u3}} [_inst_3 : forall (i : ι), DecidableEq.{succ u3} (γ i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] [_inst_5 : forall (i : ι), Zero.{u3} (γ i)] (f : forall (i : ι), (γ i) -> (β i)) {x : forall (i : ι), γ i}, (forall (i : ι), Eq.{succ u2} (β i) (f i (OfNat.ofNat.{u3} (γ i) 0 (OfNat.mk.{u3} (γ i) 0 (Zero.zero.{u3} (γ i) (_inst_5 i))))) (OfNat.ofNat.{u2} (β i) 0 (OfNat.mk.{u2} (β i) 0 (Zero.zero.{u2} (β i) (_inst_4 i))))) -> (LE.le.{0} Nat Nat.hasLe (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => f i (x i))) (hammingNorm.{u1, u3} ι (fun (i : ι) => γ i) _inst_1 (fun (i : ι) (a : γ i) (b : γ i) => _inst_3 i a b) (fun (i : ι) => _inst_5 i) x))
but is expected to have type
  forall {ι : Type.{u1}} {β : ι -> Type.{u3}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u3} (β i)] {γ : ι -> Type.{u2}} [_inst_3 : forall (i : ι), DecidableEq.{succ u2} (γ i)] [_inst_4 : forall (i : ι), Zero.{u3} (β i)] [_inst_5 : forall (i : ι), Zero.{u2} (γ i)] (f : forall (i : ι), (γ i) -> (β i)) {x : forall (i : ι), γ i}, (forall (i : ι), Eq.{succ u3} (β i) (f i (OfNat.ofNat.{u2} (γ i) 0 (Zero.toOfNat0.{u2} (γ i) (_inst_5 i)))) (OfNat.ofNat.{u3} (β i) 0 (Zero.toOfNat0.{u3} (β i) (_inst_4 i)))) -> (LE.le.{0} Nat instLENat (hammingNorm.{u1, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (fun (i : ι) => f i (x i))) (hammingNorm.{u1, u2} ι (fun (i : ι) => γ i) _inst_1 (fun (i : ι) (a : γ i) (b : γ i) => _inst_3 i a b) (fun (i : ι) => _inst_5 i) x))
Case conversion may be inaccurate. Consider using '#align hamming_norm_comp_le_hamming_norm hammingNorm_comp_le_hammingNormₓ'. -/
theorem hammingNorm_comp_le_hammingNorm (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf : ∀ i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) ≤ hammingNorm x := by
  convert hammingDist_comp_le_hammingDist f; simp_rw [hf]; rfl
#align hamming_norm_comp_le_hamming_norm hammingNorm_comp_le_hammingNorm

#print hammingNorm_comp /-
theorem hammingNorm_comp (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf₁ : ∀ i, Injective (f i))
    (hf₂ : ∀ i, f i 0 = 0) : (hammingNorm fun i => f i (x i)) = hammingNorm x := by
  convert hammingDist_comp f hf₁; simp_rw [hf₂]; rfl
#align hamming_norm_comp hammingNorm_comp
-/

/- warning: hamming_norm_smul_le_hamming_norm -> hammingNorm_smul_le_hammingNorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : ι -> Type.{u3}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u3} (β i)] [_inst_4 : forall (i : ι), Zero.{u3} (β i)] [_inst_6 : Zero.{u1} α] [_inst_7 : forall (i : ι), SMulWithZero.{u1, u3} α (β i) _inst_6 (_inst_4 i)] {k : α} {x : forall (i : ι), β i}, LE.le.{0} Nat Nat.hasLe (hammingNorm.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => SMulZeroClass.toHasSmul.{u1, u3} α (β i) (_inst_4 i) (SMulWithZero.toSmulZeroClass.{u1, u3} α (β i) _inst_6 (_inst_4 i) (_inst_7 i)))) k x)) (hammingNorm.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] [_inst_6 : Zero.{u3} α] [_inst_7 : forall (i : ι), SMulWithZero.{u3, u2} α (β i) _inst_6 (_inst_4 i)] {k : α} {x : forall (i : ι), β i}, LE.le.{0} Nat instLENat (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => SMulZeroClass.toSMul.{u3, u2} α (β i) (_inst_4 i) (SMulWithZero.toSMulZeroClass.{u3, u2} α (β i) _inst_6 (_inst_4 i) (_inst_7 i))))) k x)) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x)
Case conversion may be inaccurate. Consider using '#align hamming_norm_smul_le_hamming_norm hammingNorm_smul_le_hammingNormₓ'. -/
theorem hammingNorm_smul_le_hammingNorm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    {x : ∀ i, β i} : hammingNorm (k • x) ≤ hammingNorm x :=
  hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]
#align hamming_norm_smul_le_hamming_norm hammingNorm_smul_le_hammingNorm

/- warning: hamming_norm_smul -> hammingNorm_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : ι -> Type.{u3}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u3} (β i)] [_inst_4 : forall (i : ι), Zero.{u3} (β i)] [_inst_6 : Zero.{u1} α] [_inst_7 : forall (i : ι), SMulWithZero.{u1, u3} α (β i) _inst_6 (_inst_4 i)] {k : α}, (forall (i : ι), IsSMulRegular.{u1, u3} α (β i) (SMulZeroClass.toHasSmul.{u1, u3} α (β i) (_inst_4 i) (SMulWithZero.toSmulZeroClass.{u1, u3} α (β i) _inst_6 (_inst_4 i) (_inst_7 i))) k) -> (forall (x : forall (i : ι), β i), Eq.{1} Nat (hammingNorm.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => SMulZeroClass.toHasSmul.{u1, u3} α (β i) (_inst_4 i) (SMulWithZero.toSmulZeroClass.{u1, u3} α (β i) _inst_6 (_inst_4 i) (_inst_7 i)))) k x)) (hammingNorm.{u2, u3} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), Zero.{u2} (β i)] [_inst_6 : Zero.{u3} α] [_inst_7 : forall (i : ι), SMulWithZero.{u3, u2} α (β i) _inst_6 (_inst_4 i)] {k : α}, (forall (i : ι), IsSMulRegular.{u3, u2} α (β i) (SMulZeroClass.toSMul.{u3, u2} α (β i) (_inst_4 i) (SMulWithZero.toSMulZeroClass.{u3, u2} α (β i) _inst_6 (_inst_4 i) (_inst_7 i))) k) -> (forall (x : forall (i : ι), β i), Eq.{1} Nat (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => SMulZeroClass.toSMul.{u3, u2} α (β i) (_inst_4 i) (SMulWithZero.toSMulZeroClass.{u3, u2} α (β i) _inst_6 (_inst_4 i) (_inst_7 i))))) k x)) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_4 i) x))
Case conversion may be inaccurate. Consider using '#align hamming_norm_smul hammingNorm_smulₓ'. -/
theorem hammingNorm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    (hk : ∀ i, IsSMulRegular (β i) k) (x : ∀ i, β i) : hammingNorm (k • x) = hammingNorm x :=
  hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]
#align hamming_norm_smul hammingNorm_smul

end Zero

/- warning: hamming_dist_eq_hamming_norm -> hammingDist_eq_hammingNorm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), AddGroup.{u2} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => AddZeroClass.toHasZero.{u2} (β i) (AddMonoid.toAddZeroClass.{u2} (β i) (SubNegMonoid.toAddMonoid.{u2} (β i) (AddGroup.toSubNegMonoid.{u2} (β i) (_inst_4 i))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (forall (i : ι), β i) (forall (i : ι), β i) (forall (i : ι), β i) (instHSub.{max u1 u2} (forall (i : ι), β i) (Pi.instSub.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => SubNegMonoid.toHasSub.{u2} (β i) (AddGroup.toSubNegMonoid.{u2} (β i) (_inst_4 i))))) x y))
but is expected to have type
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_4 : forall (i : ι), AddGroup.{u2} (β i)] (x : forall (i : ι), β i) (y : forall (i : ι), β i), Eq.{1} Nat (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) x y) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => NegZeroClass.toZero.{u2} (β i) (SubNegZeroMonoid.toNegZeroClass.{u2} (β i) (SubtractionMonoid.toSubNegZeroMonoid.{u2} (β i) (AddGroup.toSubtractionMonoid.{u2} (β i) (_inst_4 i))))) (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (forall (i : ι), β i) (forall (i : ι), β i) (forall (i : ι), β i) (instHSub.{max u1 u2} (forall (i : ι), β i) (Pi.instSub.{u1, u2} ι (fun (i : ι) => β i) (fun (i : ι) => SubNegMonoid.toSub.{u2} (β i) (AddGroup.toSubNegMonoid.{u2} (β i) (_inst_4 i))))) x y))
Case conversion may be inaccurate. Consider using '#align hamming_dist_eq_hamming_norm hammingDist_eq_hammingNormₓ'. -/
/-- Corresponds to `dist_eq_norm`. -/
theorem hammingDist_eq_hammingNorm [∀ i, AddGroup (β i)] (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (x - y) := by
  simp_rw [hammingNorm, hammingDist, Pi.sub_apply, sub_ne_zero]
#align hamming_dist_eq_hamming_norm hammingDist_eq_hammingNorm

end HammingDistNorm

/-! ### The `hamming` type synonym -/


#print Hamming /-
/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `pi.normed_add_comm_group` which uses the sup norm. -/
def Hamming {ι : Type _} (β : ι → Type _) : Type _ :=
  ∀ i, β i
#align hamming Hamming
-/

namespace Hamming

variable {α ι : Type _} {β : ι → Type _}

/-! Instances inherited from normal Pi types. -/


instance [∀ i, Inhabited (β i)] : Inhabited (Hamming β) :=
  ⟨fun i => default⟩

instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (Hamming β) :=
  Pi.fintype

instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
  Pi.nontrivial

instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (Hamming β) :=
  Fintype.decidablePiFintype

instance [∀ i, Zero (β i)] : Zero (Hamming β) :=
  Pi.instZero

instance [∀ i, Neg (β i)] : Neg (Hamming β) :=
  Pi.instNeg

instance [∀ i, Add (β i)] : Add (Hamming β) :=
  Pi.instAdd

instance [∀ i, Sub (β i)] : Sub (Hamming β) :=
  Pi.instSub

instance [∀ i, SMul α (β i)] : SMul α (Hamming β) :=
  Pi.instSMul

instance [Zero α] [∀ i, Zero (β i)] [∀ i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β) :=
  Pi.smulWithZero _

instance [∀ i, AddMonoid (β i)] : AddMonoid (Hamming β) :=
  Pi.addMonoid

instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β) :=
  Pi.addCommMonoid

instance [∀ i, AddCommGroup (β i)] : AddCommGroup (Hamming β) :=
  Pi.addCommGroup

instance (α) [Semiring α] (β : ι → Type _) [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
    Module α (Hamming β) :=
  Pi.module _ _ _

/-! API to/from the type synonym. -/


#print Hamming.toHamming /-
/-- `to_hamming` is the identity function to the `hamming` of a type.  -/
@[match_pattern]
def toHamming : (∀ i, β i) ≃ Hamming β :=
  Equiv.refl _
#align hamming.to_hamming Hamming.toHamming
-/

#print Hamming.ofHamming /-
/-- `of_hamming` is the identity function from the `hamming` of a type.  -/
@[match_pattern]
def ofHamming : Hamming β ≃ ∀ i, β i :=
  Equiv.refl _
#align hamming.of_hamming Hamming.ofHamming
-/

/- warning: hamming.to_hamming_symm_eq -> Hamming.toHamming_symm_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}}, Eq.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Equiv.symm.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι β) (Hamming.toHamming.{u1, u2} ι β)) (Hamming.ofHamming.{u1, u2} ι β)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (i : ι), β i) (Hamming.{u2, u1} ι β) (Hamming.toHamming.{u2, u1} ι β)) (Hamming.ofHamming.{u2, u1} ι β)
Case conversion may be inaccurate. Consider using '#align hamming.to_hamming_symm_eq Hamming.toHamming_symm_eqₓ'. -/
@[simp]
theorem toHamming_symm_eq : (@toHamming _ β).symm = ofHamming :=
  rfl
#align hamming.to_hamming_symm_eq Hamming.toHamming_symm_eq

/- warning: hamming.of_hamming_symm_eq -> Hamming.ofHamming_symm_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}}, Eq.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι β)) (Equiv.symm.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i) (Hamming.ofHamming.{u1, u2} ι β)) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (i : ι), β i) (Hamming.{u2, u1} ι β)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i) (Hamming.ofHamming.{u2, u1} ι β)) (Hamming.toHamming.{u2, u1} ι (fun (i : ι) => β i))
Case conversion may be inaccurate. Consider using '#align hamming.of_hamming_symm_eq Hamming.ofHamming_symm_eqₓ'. -/
@[simp]
theorem ofHamming_symm_eq : (@ofHamming _ β).symm = toHamming :=
  rfl
#align hamming.of_hamming_symm_eq Hamming.ofHamming_symm_eq

/- warning: hamming.to_hamming_of_hamming -> Hamming.toHamming_ofHamming is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} (x : Hamming.{u1, u2} ι β), Eq.{succ (max u1 u2)} (Hamming.{u1, u2} ι (fun (i : ι) => β i)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (fun (_x : Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) => (forall (i : ι), β i) -> (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i)) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x)) x
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} (x : Hamming.{u2, u1} ι β), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (a : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) a) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) x)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (_x : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u1} ι (fun (i : ι) => β i)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) x)) x
Case conversion may be inaccurate. Consider using '#align hamming.to_hamming_of_hamming Hamming.toHamming_ofHammingₓ'. -/
@[simp]
theorem toHamming_ofHamming (x : Hamming β) : toHamming (ofHamming x) = x :=
  rfl
#align hamming.to_hamming_of_hamming Hamming.toHamming_ofHamming

/- warning: hamming.of_hamming_to_hamming -> Hamming.ofHamming_toHamming is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} (x : forall (i : ι), β i), Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι (fun (i : ι) => β i)) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι (fun (i : ι) => β i)) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι (fun (i : ι) => β i)) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι (fun (i : ι) => β i)) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι (fun (i : ι) => β i)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (fun (_x : Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) => (forall (i : ι), β i) -> (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i)) x)) x
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} (x : forall (i : ι), β i), Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι (fun (i : ι) => β i)) => forall (i : ι), β i) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (a : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) a) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u1} ι (fun (i : ι) => β i)) x)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι (fun (i : ι) => β i)) (forall (i : ι), β i)) (Hamming.{u2, u1} ι (fun (i : ι) => β i)) (fun (_x : Hamming.{u2, u1} ι (fun (i : ι) => β i)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι (fun (i : ι) => β i)) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι (fun (i : ι) => β i)) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι (fun (i : ι) => β i)) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (_x : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u1} ι (fun (i : ι) => β i)) x)) x
Case conversion may be inaccurate. Consider using '#align hamming.of_hamming_to_hamming Hamming.ofHamming_toHammingₓ'. -/
@[simp]
theorem ofHamming_toHamming (x : ∀ i, β i) : ofHamming (toHamming x) = x :=
  rfl
#align hamming.of_hamming_to_hamming Hamming.ofHamming_toHamming

/- warning: hamming.to_hamming_inj -> Hamming.toHamming_inj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Eq.{succ (max u1 u2)} (Hamming.{u1, u2} ι (fun (i : ι) => β i)) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (fun (_x : Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) => (forall (i : ι), β i) -> (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i)) x) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ (max u1 u2))) (succ (max u1 u2)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ (max u1 u2))} (Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (fun (_x : Equiv.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) => (forall (i : ι), β i) -> (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), succ (max u1 u2)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i)) y)) (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} {x : forall (i : ι), β i} {y : forall (i : ι), β i}, Iff (Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (_x : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u1} ι (fun (i : ι) => β i)) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (_x : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u2, u1} ι (fun (i : ι) => β i)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (forall (i : ι), β i) (Hamming.{u2, u1} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u1} ι (fun (i : ι) => β i)) y)) (Eq.{max (succ u2) (succ u1)} (forall (i : ι), β i) x y)
Case conversion may be inaccurate. Consider using '#align hamming.to_hamming_inj Hamming.toHamming_injₓ'. -/
@[simp]
theorem toHamming_inj {x y : ∀ i, β i} : toHamming x = toHamming y ↔ x = y :=
  Iff.rfl
#align hamming.to_hamming_inj Hamming.toHamming_inj

/- warning: hamming.of_hamming_inj -> Hamming.ofHamming_inj is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} {x : Hamming.{u1, u2} ι β} {y : Hamming.{u1, u2} ι β}, Iff (Eq.{max (succ u1) (succ u2)} (forall (i : ι), β i) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) y)) (Eq.{succ (max u1 u2)} (Hamming.{u1, u2} ι β) x y)
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} {x : Hamming.{u2, u1} ι β} {y : Hamming.{u2, u1} ι β}, Iff (Eq.{max (succ u2) (succ u1)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) y)) (Eq.{max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) x y)
Case conversion may be inaccurate. Consider using '#align hamming.of_hamming_inj Hamming.ofHamming_injₓ'. -/
@[simp]
theorem ofHamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y :=
  Iff.rfl
#align hamming.of_hamming_inj Hamming.ofHamming_inj

#print Hamming.toHamming_zero /-
@[simp]
theorem toHamming_zero [∀ i, Zero (β i)] : toHamming (0 : ∀ i, β i) = 0 :=
  rfl
#align hamming.to_hamming_zero Hamming.toHamming_zero
-/

#print Hamming.ofHamming_zero /-
@[simp]
theorem ofHamming_zero [∀ i, Zero (β i)] : ofHamming (0 : Hamming β) = 0 :=
  rfl
#align hamming.of_hamming_zero Hamming.ofHamming_zero
-/

#print Hamming.toHamming_neg /-
@[simp]
theorem toHamming_neg [∀ i, Neg (β i)] {x : ∀ i, β i} : toHamming (-x) = -toHamming x :=
  rfl
#align hamming.to_hamming_neg Hamming.toHamming_neg
-/

#print Hamming.ofHamming_neg /-
@[simp]
theorem ofHamming_neg [∀ i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -ofHamming x :=
  rfl
#align hamming.of_hamming_neg Hamming.ofHamming_neg
-/

#print Hamming.toHamming_add /-
@[simp]
theorem toHamming_add [∀ i, Add (β i)] {x y : ∀ i, β i} :
    toHamming (x + y) = toHamming x + toHamming y :=
  rfl
#align hamming.to_hamming_add Hamming.toHamming_add
-/

#print Hamming.ofHamming_add /-
@[simp]
theorem ofHamming_add [∀ i, Add (β i)] {x y : Hamming β} :
    ofHamming (x + y) = ofHamming x + ofHamming y :=
  rfl
#align hamming.of_hamming_add Hamming.ofHamming_add
-/

#print Hamming.toHamming_sub /-
@[simp]
theorem toHamming_sub [∀ i, Sub (β i)] {x y : ∀ i, β i} :
    toHamming (x - y) = toHamming x - toHamming y :=
  rfl
#align hamming.to_hamming_sub Hamming.toHamming_sub
-/

#print Hamming.ofHamming_sub /-
@[simp]
theorem ofHamming_sub [∀ i, Sub (β i)] {x y : Hamming β} :
    ofHamming (x - y) = ofHamming x - ofHamming y :=
  rfl
#align hamming.of_hamming_sub Hamming.ofHamming_sub
-/

/- warning: hamming.to_hamming_smul -> Hamming.toHamming_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u1, u3} α (β i)] {r : α} {x : forall (i : ι), β i}, Eq.{succ (max u2 u3)} (Hamming.{u2, u3} ι (fun (i : ι) => β i)) (coeFn.{max 1 (max (max (succ u2) (succ u3)) (succ (max u2 u3))) (succ (max u2 u3)) (succ u2) (succ u3), max (max (succ u2) (succ u3)) (succ (max u2 u3))} (Equiv.{max (succ u2) (succ u3), succ (max u2 u3)} (forall (i : ι), β i) (Hamming.{u2, u3} ι (fun (i : ι) => β i))) (fun (_x : Equiv.{max (succ u2) (succ u3), succ (max u2 u3)} (forall (i : ι), β i) (Hamming.{u2, u3} ι (fun (i : ι) => β i))) => (forall (i : ι), β i) -> (Hamming.{u2, u3} ι (fun (i : ι) => β i))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), succ (max u2 u3)} (forall (i : ι), β i) (Hamming.{u2, u3} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u3} ι (fun (i : ι) => β i)) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i)) r x)) (SMul.smul.{u1, max u2 u3} α (Hamming.{u2, u3} ι (fun (i : ι) => β i)) (Hamming.hasSmul.{u1, u2, u3} α ι (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i)) r (coeFn.{max 1 (max (max (succ u2) (succ u3)) (succ (max u2 u3))) (succ (max u2 u3)) (succ u2) (succ u3), max (max (succ u2) (succ u3)) (succ (max u2 u3))} (Equiv.{max (succ u2) (succ u3), succ (max u2 u3)} (forall (i : ι), β i) (Hamming.{u2, u3} ι (fun (i : ι) => β i))) (fun (_x : Equiv.{max (succ u2) (succ u3), succ (max u2 u3)} (forall (i : ι), β i) (Hamming.{u2, u3} ι (fun (i : ι) => β i))) => (forall (i : ι), β i) -> (Hamming.{u2, u3} ι (fun (i : ι) => β i))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), succ (max u2 u3)} (forall (i : ι), β i) (Hamming.{u2, u3} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u2, u3} ι (fun (i : ι) => β i)) x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u3, u2} α (β i)] {r : α} {x : forall (i : ι), β i}, Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u1, u2} ι (fun (i : ι) => β i)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i))) r x)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (_x : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u1, u2} ι (fun (i : ι) => β i)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (forall (i : ι), β i) (forall (i : ι), β i) (instHSMul.{u3, max u1 u2} α (forall (i : ι), β i) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i))) r x)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u1, u2} ι (fun (i : ι) => β i)) x) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u1, u2} ι (fun (i : ι) => β i)) x) (instHSMul.{u3, max u1 u2} α ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u1, u2} ι (fun (i : ι) => β i)) x) (Hamming.instSMulHamming.{u3, u1, u2} α ι (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i))) r (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (forall (i : ι), β i) (fun (_x : forall (i : ι), β i) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : forall (i : ι), β i) => Hamming.{u1, u2} ι (fun (i : ι) => β i)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (forall (i : ι), β i) (Hamming.{u1, u2} ι (fun (i : ι) => β i))) (Hamming.toHamming.{u1, u2} ι (fun (i : ι) => β i)) x))
Case conversion may be inaccurate. Consider using '#align hamming.to_hamming_smul Hamming.toHamming_smulₓ'. -/
@[simp]
theorem toHamming_smul [∀ i, SMul α (β i)] {r : α} {x : ∀ i, β i} :
    toHamming (r • x) = r • toHamming x :=
  rfl
#align hamming.to_hamming_smul Hamming.toHamming_smul

/- warning: hamming.of_hamming_smul -> Hamming.ofHamming_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {β : ι -> Type.{u3}} [_inst_1 : forall (i : ι), SMul.{u1, u3} α (β i)] {r : α} {x : Hamming.{u2, u3} ι β}, Eq.{max (succ u2) (succ u3)} (forall (i : ι), β i) (coeFn.{max 1 (max (succ (max u2 u3)) (succ u2) (succ u3)) (max (succ u2) (succ u3)) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u2) (succ u3)} (Equiv.{succ (max u2 u3), max (succ u2) (succ u3)} (Hamming.{u2, u3} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u2 u3), max (succ u2) (succ u3)} (Hamming.{u2, u3} ι β) (forall (i : ι), β i)) => (Hamming.{u2, u3} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u2 u3), max (succ u2) (succ u3)} (Hamming.{u2, u3} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u3} ι β) (SMul.smul.{u1, max u2 u3} α (Hamming.{u2, u3} ι β) (Hamming.hasSmul.{u1, u2, u3} α ι β (fun (i : ι) => _inst_1 i)) r x)) (SMul.smul.{u1, max u2 u3} α (forall (i : ι), β i) (Pi.instSMul.{u2, u3, u1} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i)) r (coeFn.{max 1 (max (succ (max u2 u3)) (succ u2) (succ u3)) (max (succ u2) (succ u3)) (succ (max u2 u3)), max (succ (max u2 u3)) (succ u2) (succ u3)} (Equiv.{succ (max u2 u3), max (succ u2) (succ u3)} (Hamming.{u2, u3} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u2 u3), max (succ u2) (succ u3)} (Hamming.{u2, u3} ι β) (forall (i : ι), β i)) => (Hamming.{u2, u3} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u2 u3), max (succ u2) (succ u3)} (Hamming.{u2, u3} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u3} ι β) x))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : forall (i : ι), SMul.{u3, u2} α (β i)] {r : α} {x : Hamming.{u1, u2} ι β}, Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (Hamming.{u1, u2} ι β) (Hamming.{u1, u2} ι β) (instHSMul.{u3, max u1 u2} α (Hamming.{u1, u2} ι β) (Hamming.instSMulHamming.{u3, u1, u2} α ι β (fun (i : ι) => _inst_1 i))) r x)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.{u1, u2} ι β) (fun (_x : Hamming.{u1, u2} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α (Hamming.{u1, u2} ι β) (Hamming.{u1, u2} ι β) (instHSMul.{u3, max u1 u2} α (Hamming.{u1, u2} ι β) (Hamming.instSMulHamming.{u3, u1, u2} α ι β (fun (i : ι) => _inst_1 i))) r x)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} α ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) x) ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) x) (instHSMul.{u3, max u1 u2} α ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) x) (Pi.instSMul.{u1, u2, u3} ι α (fun (i : ι) => β i) (fun (i : ι) => _inst_1 i))) r (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.{u1, u2} ι β) (fun (_x : Hamming.{u1, u2} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x))
Case conversion may be inaccurate. Consider using '#align hamming.of_hamming_smul Hamming.ofHamming_smulₓ'. -/
@[simp]
theorem ofHamming_smul [∀ i, SMul α (β i)] {r : α} {x : Hamming β} :
    ofHamming (r • x) = r • ofHamming x :=
  rfl
#align hamming.of_hamming_smul Hamming.ofHamming_smul

section

/-! Instances equipping `hamming` with `hamming_norm` and `hamming_dist`. -/


variable [Fintype ι] [∀ i, DecidableEq (β i)]

instance : Dist (Hamming β) :=
  ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

/- warning: hamming.dist_eq_hamming_dist -> Hamming.dist_eq_hammingDist is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : Hamming.{u1, u2} ι β) (y : Hamming.{u1, u2} ι β), Eq.{1} Real (Dist.dist.{max u1 u2} (Hamming.{u1, u2} ι β) (Hamming.hasDist.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b)) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) y)))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : Hamming.{u2, u1} ι β) (y : Hamming.{u2, u1} ι β), Eq.{1} Real (Dist.dist.{max u2 u1} (Hamming.{u2, u1} ι β) (Hamming.instDistHamming.{u2, u1} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b)) x y) (Nat.cast.{0} Real Real.natCast (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) y)))
Case conversion may be inaccurate. Consider using '#align hamming.dist_eq_hamming_dist Hamming.dist_eq_hammingDistₓ'. -/
@[simp, push_cast]
theorem dist_eq_hammingDist (x y : Hamming β) :
    dist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
#align hamming.dist_eq_hamming_dist Hamming.dist_eq_hammingDist

instance : PseudoMetricSpace (Hamming β) :=
  {
    Hamming.hasDist with
    dist_self := by push_cast ; exact_mod_cast hammingDist_self
    dist_comm := by push_cast ; exact_mod_cast hammingDist_comm
    dist_triangle := by push_cast ; exact_mod_cast hammingDist_triangle
    toUniformSpace := ⊥
    uniformity_dist :=
      uniformity_dist_of_mem_uniformity _ _ fun s =>
        by
        push_cast
        constructor
        · refine' fun hs => ⟨1, zero_lt_one, fun _ _ hab => _⟩
          rw_mod_cast [hammingDist_lt_one]  at hab
          rw [of_hamming_inj, ← mem_idRel] at hab
          exact hs hab
        · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ hab
          rw [mem_idRel] at hab
          rw [hab]
          refine' hs (lt_of_eq_of_lt _ hε)
          exact_mod_cast hammingDist_self _
    toBornology := ⟨⊥, bot_le⟩
    cobounded_sets := by
      ext
      push_cast
      refine' iff_of_true (filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => _⟩
      exact_mod_cast hammingDist_le_card_fintype }

/- warning: hamming.nndist_eq_hamming_dist -> Hamming.nndist_eq_hammingDist is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] (x : Hamming.{u1, u2} ι β) (y : Hamming.{u1, u2} ι β), Eq.{1} NNReal (NNDist.nndist.{max u1 u2} (Hamming.{u1, u2} ι β) (PseudoMetricSpace.toNNDist.{max u1 u2} (Hamming.{u1, u2} ι β) (Hamming.pseudoMetricSpace.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b))) x y) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (hammingDist.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) y)))
but is expected to have type
  forall {ι : Type.{u2}} {β : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u1} (β i)] (x : Hamming.{u2, u1} ι β) (y : Hamming.{u2, u1} ι β), Eq.{1} NNReal (NNDist.nndist.{max u2 u1} (Hamming.{u2, u1} ι β) (PseudoMetricSpace.toNNDist.{max u2 u1} (Hamming.{u2, u1} ι β) (Hamming.instPseudoMetricSpaceHamming.{u2, u1} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b))) x y) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (hammingDist.{u2, u1} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) x) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.{u2, u1} ι β) (fun (_x : Hamming.{u2, u1} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u2, u1} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Hamming.{u2, u1} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u2, u1} ι β) y)))
Case conversion may be inaccurate. Consider using '#align hamming.nndist_eq_hamming_dist Hamming.nndist_eq_hammingDistₓ'. -/
@[simp, push_cast]
theorem nndist_eq_hammingDist (x y : Hamming β) :
    nndist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
#align hamming.nndist_eq_hamming_dist Hamming.nndist_eq_hammingDist

instance : MetricSpace (Hamming β) :=
  { Hamming.pseudoMetricSpace with
    eq_of_dist_eq_zero := by push_cast ; exact_mod_cast @eq_of_hammingDist_eq_zero _ _ _ _ }

instance [∀ i, Zero (β i)] : Norm (Hamming β) :=
  ⟨fun x => hammingNorm (ofHamming x)⟩

/- warning: hamming.norm_eq_hamming_norm -> Hamming.norm_eq_hammingNorm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_3 : forall (i : ι), Zero.{u2} (β i)] (x : Hamming.{u1, u2} ι β), Eq.{1} Real (Norm.norm.{max u1 u2} (Hamming.{u1, u2} ι β) (Hamming.hasNorm.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_3 i)) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_3 i) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x)))
but is expected to have type
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_3 : forall (i : ι), Zero.{u2} (β i)] (x : Hamming.{u1, u2} ι β), Eq.{1} Real (Norm.norm.{max u1 u2} (Hamming.{u1, u2} ι β) (Hamming.instNormHamming.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_3 i)) x) (Nat.cast.{0} Real Real.natCast (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_3 i) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.{u1, u2} ι β) (fun (_x : Hamming.{u1, u2} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x)))
Case conversion may be inaccurate. Consider using '#align hamming.norm_eq_hamming_norm Hamming.norm_eq_hammingNormₓ'. -/
@[simp, push_cast]
theorem norm_eq_hammingNorm [∀ i, Zero (β i)] (x : Hamming β) : ‖x‖ = hammingNorm (ofHamming x) :=
  rfl
#align hamming.norm_eq_hamming_norm Hamming.norm_eq_hammingNorm

instance [∀ i, AddCommGroup (β i)] : SeminormedAddCommGroup (Hamming β) :=
  { Pi.addCommGroup with dist_eq := by push_cast ; exact_mod_cast hammingDist_eq_hammingNorm }

/- warning: hamming.nnnorm_eq_hamming_norm -> Hamming.nnnorm_eq_hammingNorm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_3 : forall (i : ι), AddCommGroup.{u2} (β i)] (x : Hamming.{u1, u2} ι β), Eq.{1} NNReal (NNNorm.nnnorm.{max u1 u2} (Hamming.{u1, u2} ι β) (SeminormedAddGroup.toNNNorm.{max u1 u2} (Hamming.{u1, u2} ι β) (SeminormedAddCommGroup.toSeminormedAddGroup.{max u1 u2} (Hamming.{u1, u2} ι β) (Hamming.seminormedAddCommGroup.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_3 i)))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => AddZeroClass.toHasZero.{u2} (β i) (AddMonoid.toAddZeroClass.{u2} (β i) (SubNegMonoid.toAddMonoid.{u2} (β i) (AddGroup.toSubNegMonoid.{u2} (β i) (AddCommGroup.toAddGroup.{u2} (β i) (_inst_3 i)))))) (coeFn.{max 1 (max (succ (max u1 u2)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ (max u1 u2)), max (succ (max u1 u2)) (succ u1) (succ u2)} (Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (fun (_x : Equiv.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) => (Hamming.{u1, u2} ι β) -> (forall (i : ι), β i)) (Equiv.hasCoeToFun.{succ (max u1 u2), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x)))
but is expected to have type
  forall {ι : Type.{u1}} {β : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_2 : forall (i : ι), DecidableEq.{succ u2} (β i)] [_inst_3 : forall (i : ι), AddCommGroup.{u2} (β i)] (x : Hamming.{u1, u2} ι β), Eq.{1} NNReal (NNNorm.nnnorm.{max u1 u2} (Hamming.{u1, u2} ι β) (SeminormedAddGroup.toNNNorm.{max u1 u2} (Hamming.{u1, u2} ι β) (SeminormedAddCommGroup.toSeminormedAddGroup.{max u1 u2} (Hamming.{u1, u2} ι β) (NormedAddCommGroup.toSeminormedAddCommGroup.{max u1 u2} (Hamming.{u1, u2} ι β) (Hamming.instNormedAddCommGroupHamming.{u1, u2} ι β _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => _inst_3 i))))) x) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (hammingNorm.{u1, u2} ι (fun (i : ι) => β i) _inst_1 (fun (i : ι) (a : β i) (b : β i) => _inst_2 i a b) (fun (i : ι) => NegZeroClass.toZero.{u2} (β i) (SubNegZeroMonoid.toNegZeroClass.{u2} (β i) (SubtractionMonoid.toSubNegZeroMonoid.{u2} (β i) (SubtractionCommMonoid.toSubtractionMonoid.{u2} (β i) (AddCommGroup.toDivisionAddCommMonoid.{u2} (β i) (_inst_3 i)))))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.{u1, u2} ι β) (fun (_x : Hamming.{u1, u2} ι β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Hamming.{u1, u2} ι β) => forall (i : ι), β i) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Hamming.{u1, u2} ι β) (forall (i : ι), β i)) (Hamming.ofHamming.{u1, u2} ι β) x)))
Case conversion may be inaccurate. Consider using '#align hamming.nnnorm_eq_hamming_norm Hamming.nnnorm_eq_hammingNormₓ'. -/
@[simp, push_cast]
theorem nnnorm_eq_hammingNorm [∀ i, AddCommGroup (β i)] (x : Hamming β) :
    ‖x‖₊ = hammingNorm (ofHamming x) :=
  rfl
#align hamming.nnnorm_eq_hamming_norm Hamming.nnnorm_eq_hammingNorm

instance [∀ i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) :=
  { Hamming.seminormedAddCommGroup with }

end

end Hamming

