/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.inc_matrix
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.Matrix.Basic

/-!
# Incidence matrix of a simple graph

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `simple_graph.inc_matrix`: `G.inc_matrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `simple_graph.inc_matrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.inc_matrix R` and its transpose are the degrees of the vertices.
* `simple_graph.inc_matrix_mul_transpose`: Gives a complete description of the product of
  `G.inc_matrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `simple_graph.inc_matrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.inc_matrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `simple_graph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.
-/


open Finset Matrix SimpleGraph Sym2

open BigOperators Matrix

namespace SimpleGraph

variable (R : Type _) {α : Type _} (G : SimpleGraph α)

#print SimpleGraph.incMatrix /-
/-- `G.inc_matrix R` is the `α × sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` otherwise. -/
noncomputable def incMatrix [Zero R] [One R] : Matrix α (Sym2 α) R := fun a =>
  (G.incidenceSet a).indicator 1
#align simple_graph.inc_matrix SimpleGraph.incMatrix
-/

variable {R}

/- warning: simple_graph.inc_matrix_apply -> SimpleGraph.incMatrix_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Zero.{u1} R] [_inst_2 : One.{u1} R] {a : α} {e : Sym2.{u2} α}, Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G _inst_1 _inst_2 a e) (Set.indicator.{u2, u1} (Sym2.{u2} α) R _inst_1 (SimpleGraph.incidenceSet.{u2} α G a) (OfNat.ofNat.{max u2 u1} ((Sym2.{u2} α) -> R) 1 (OfNat.mk.{max u2 u1} ((Sym2.{u2} α) -> R) 1 (One.one.{max u2 u1} ((Sym2.{u2} α) -> R) (Pi.instOne.{u2, u1} (Sym2.{u2} α) (fun (ᾰ : Sym2.{u2} α) => R) (fun (i : Sym2.{u2} α) => _inst_2))))) e)
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : Zero.{u2} R] [_inst_2 : One.{u2} R] {a : α} {e : Sym2.{u1} α}, Eq.{succ u2} R (SimpleGraph.incMatrix.{u2, u1} R α G _inst_1 _inst_2 a e) (Set.indicator.{u1, u2} (Sym2.{u1} α) R _inst_1 (SimpleGraph.incidenceSet.{u1} α G a) (OfNat.ofNat.{max u1 u2} ((Sym2.{u1} α) -> R) 1 (One.toOfNat1.{max u2 u1} ((Sym2.{u1} α) -> R) (Pi.instOne.{u1, u2} (Sym2.{u1} α) (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : Sym2.{u1} α) => R) (fun (i : Sym2.{u1} α) => _inst_2)))) e)
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_apply SimpleGraph.incMatrix_applyₓ'. -/
theorem incMatrix_apply [Zero R] [One R] {a : α} {e : Sym2 α} :
    G.incMatrix R a e = (G.incidenceSet a).indicator 1 e :=
  rfl
#align simple_graph.inc_matrix_apply SimpleGraph.incMatrix_apply

/- warning: simple_graph.inc_matrix_apply' -> SimpleGraph.incMatrix_apply' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Zero.{u1} R] [_inst_2 : One.{u1} R] [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {a : α} {e : Sym2.{u2} α}, Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G _inst_1 _inst_2 a e) (ite.{succ u1} R (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a)) (SimpleGraph.decidableMemIncidenceSet.{u2} α G (fun (a : α) (b : α) => _inst_3 a b) (fun (a : α) (b : α) => _inst_4 a b) a e) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R _inst_2))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R _inst_1))))
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : Zero.{u2} R] [_inst_2 : One.{u2} R] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {a : α} {e : Sym2.{u1} α}, Eq.{succ u2} R (SimpleGraph.incMatrix.{u2, u1} R α G _inst_1 _inst_2 a e) (ite.{succ u2} R (Membership.mem.{u1, u1} (Sym2.{u1} α) (Set.{u1} (Sym2.{u1} α)) (Set.instMembershipSet.{u1} (Sym2.{u1} α)) e (SimpleGraph.incidenceSet.{u1} α G a)) (SimpleGraph.decidableMemIncidenceSet.{u1} α G (fun (a : α) (b : α) => _inst_3 a b) (fun (a : α) (b : α) => _inst_4 a b) a e) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_2)) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R _inst_1)))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_apply' SimpleGraph.incMatrix_apply'ₓ'. -/
/-- Entries of the incidence matrix can be computed given additional decidable instances. -/
theorem incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
    {e : Sym2 α} : G.incMatrix R a e = if e ∈ G.incidenceSet a then 1 else 0 := by convert rfl
#align simple_graph.inc_matrix_apply' SimpleGraph.incMatrix_apply'

section MulZeroOneClass

variable [MulZeroOneClass R] {a b : α} {e : Sym2 α}

/- warning: simple_graph.inc_matrix_apply_mul_inc_matrix_apply -> SimpleGraph.incMatrix_apply_mul_incMatrix_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {b : α} {e : Sym2.{u2} α}, Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (MulZeroClass.toHasMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) b e)) (Set.indicator.{u2, u1} (Sym2.{u2} α) R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (Inter.inter.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasInter.{u2} (Sym2.{u2} α)) (SimpleGraph.incidenceSet.{u2} α G a) (SimpleGraph.incidenceSet.{u2} α G b)) (OfNat.ofNat.{max u2 u1} ((Sym2.{u2} α) -> R) 1 (OfNat.mk.{max u2 u1} ((Sym2.{u2} α) -> R) 1 (One.one.{max u2 u1} ((Sym2.{u2} α) -> R) (Pi.instOne.{u2, u1} (Sym2.{u2} α) (fun (ᾰ : Sym2.{u2} α) => R) (fun (i : Sym2.{u2} α) => MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)))))) e)
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : MulZeroOneClass.{u2} R] {a : α} {b : α} {e : Sym2.{u1} α}, Eq.{succ u2} R (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (MulZeroClass.toMul.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R _inst_1))) (SimpleGraph.incMatrix.{u2, u1} R α G (MulZeroOneClass.toZero.{u2} R _inst_1) (MulOneClass.toOne.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R _inst_1)) a e) (SimpleGraph.incMatrix.{u2, u1} R α G (MulZeroOneClass.toZero.{u2} R _inst_1) (MulOneClass.toOne.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R _inst_1)) b e)) (Set.indicator.{u1, u2} (Sym2.{u1} α) R (MulZeroOneClass.toZero.{u2} R _inst_1) (Inter.inter.{u1} (Set.{u1} (Sym2.{u1} α)) (Set.instInterSet.{u1} (Sym2.{u1} α)) (SimpleGraph.incidenceSet.{u1} α G a) (SimpleGraph.incidenceSet.{u1} α G b)) (OfNat.ofNat.{max u1 u2} ((Sym2.{u1} α) -> R) 1 (One.toOfNat1.{max u2 u1} ((Sym2.{u1} α) -> R) (Pi.instOne.{u1, u2} (Sym2.{u1} α) (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : Sym2.{u1} α) => R) (fun (i : Sym2.{u1} α) => MulOneClass.toOne.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R _inst_1))))) e)
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_apply_mul_inc_matrix_apply SimpleGraph.incMatrix_apply_mul_incMatrix_applyₓ'. -/
theorem incMatrix_apply_mul_incMatrix_apply :
    G.incMatrix R a e * G.incMatrix R b e = (G.incidenceSet a ∩ G.incidenceSet b).indicator 1 e :=
  by
  classical simp only [inc_matrix, Set.indicator_apply, ← ite_and_mul_zero, Pi.one_apply, mul_one,
      Set.mem_inter_iff]
#align simple_graph.inc_matrix_apply_mul_inc_matrix_apply SimpleGraph.incMatrix_apply_mul_incMatrix_apply

/- warning: simple_graph.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj -> SimpleGraph.incMatrix_apply_mul_incMatrix_apply_of_not_adj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {b : α} {e : Sym2.{u2} α}, (Ne.{succ u2} α a b) -> (Not (SimpleGraph.Adj.{u2} α G a b)) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (MulZeroClass.toHasMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) b e)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {b : α} {e : Sym2.{u2} α}, (Ne.{succ u2} α a b) -> (Not (SimpleGraph.Adj.{u2} α G a b)) -> (Eq.{succ u1} R (HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (MulZeroClass.toMul.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R _inst_1) (MulOneClass.toOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R _inst_1) (MulOneClass.toOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) b e)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj SimpleGraph.incMatrix_apply_mul_incMatrix_apply_of_not_adjₓ'. -/
theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a ≠ b) (h : ¬G.Adj a b) :
    G.incMatrix R a e * G.incMatrix R b e = 0 :=
  by
  rw [inc_matrix_apply_mul_inc_matrix_apply, Set.indicator_of_not_mem]
  rw [G.incidence_set_inter_incidence_set_of_not_adj h hab]
  exact Set.not_mem_empty e
#align simple_graph.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj SimpleGraph.incMatrix_apply_mul_incMatrix_apply_of_not_adj

/- warning: simple_graph.inc_matrix_of_not_mem_incidence_set -> SimpleGraph.incMatrix_of_not_mem_incidenceSet is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {e : Sym2.{u2} α}, (Not (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a))) -> (Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {e : Sym2.{u2} α}, (Not (Membership.mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.instMembershipSet.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a))) -> (Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R _inst_1) (MulOneClass.toOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_of_not_mem_incidence_set SimpleGraph.incMatrix_of_not_mem_incidenceSetₓ'. -/
theorem incMatrix_of_not_mem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0 := by
  rw [inc_matrix_apply, Set.indicator_of_not_mem h]
#align simple_graph.inc_matrix_of_not_mem_incidence_set SimpleGraph.incMatrix_of_not_mem_incidenceSet

/- warning: simple_graph.inc_matrix_of_mem_incidence_set -> SimpleGraph.incMatrix_of_mem_incidenceSet is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {e : Sym2.{u2} α}, (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a)) -> (Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {e : Sym2.{u2} α}, (Membership.mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.instMembershipSet.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a)) -> (Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R _inst_1) (MulOneClass.toOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (MulOneClass.toOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_of_mem_incidence_set SimpleGraph.incMatrix_of_mem_incidenceSetₓ'. -/
theorem incMatrix_of_mem_incidenceSet (h : e ∈ G.incidenceSet a) : G.incMatrix R a e = 1 := by
  rw [inc_matrix_apply, Set.indicator_of_mem h, Pi.one_apply]
#align simple_graph.inc_matrix_of_mem_incidence_set SimpleGraph.incMatrix_of_mem_incidenceSet

variable [Nontrivial R]

/- warning: simple_graph.inc_matrix_apply_eq_zero_iff -> SimpleGraph.incMatrix_apply_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {e : Sym2.{u2} α} [_inst_2 : Nontrivial.{u1} R], Iff (Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)))))) (Not (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a)))
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : MulZeroOneClass.{u2} R] {a : α} {e : Sym2.{u1} α} [_inst_2 : Nontrivial.{u2} R], Iff (Eq.{succ u2} R (SimpleGraph.incMatrix.{u2, u1} R α G (MulZeroOneClass.toZero.{u2} R _inst_1) (MulOneClass.toOne.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R _inst_1)) a e) (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MulZeroOneClass.toZero.{u2} R _inst_1)))) (Not (Membership.mem.{u1, u1} (Sym2.{u1} α) (Set.{u1} (Sym2.{u1} α)) (Set.instMembershipSet.{u1} (Sym2.{u1} α)) e (SimpleGraph.incidenceSet.{u1} α G a)))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_apply_eq_zero_iff SimpleGraph.incMatrix_apply_eq_zero_iffₓ'. -/
theorem incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a :=
  by
  simp only [inc_matrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]
  exact Iff.rfl
#align simple_graph.inc_matrix_apply_eq_zero_iff SimpleGraph.incMatrix_apply_eq_zero_iff

/- warning: simple_graph.inc_matrix_apply_eq_one_iff -> SimpleGraph.incMatrix_apply_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : MulZeroOneClass.{u1} R] {a : α} {e : Sym2.{u2} α} [_inst_2 : Nontrivial.{u1} R], Iff (Eq.{succ u1} R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R _inst_1)) (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)) a e) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R _inst_1)))))) (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (SimpleGraph.incidenceSet.{u2} α G a))
but is expected to have type
  forall {R : Type.{u2}} {α : Type.{u1}} (G : SimpleGraph.{u1} α) [_inst_1 : MulZeroOneClass.{u2} R] {a : α} {e : Sym2.{u1} α} [_inst_2 : Nontrivial.{u2} R], Iff (Eq.{succ u2} R (SimpleGraph.incMatrix.{u2, u1} R α G (MulZeroOneClass.toZero.{u2} R _inst_1) (MulOneClass.toOne.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R _inst_1)) a e) (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (MulOneClass.toOne.{u2} R (MulZeroOneClass.toMulOneClass.{u2} R _inst_1))))) (Membership.mem.{u1, u1} (Sym2.{u1} α) (Set.{u1} (Sym2.{u1} α)) (Set.instMembershipSet.{u1} (Sym2.{u1} α)) e (SimpleGraph.incidenceSet.{u1} α G a))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_apply_eq_one_iff SimpleGraph.incMatrix_apply_eq_one_iffₓ'. -/
theorem incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e ∈ G.incidenceSet a :=
  by
  convert one_ne_zero.ite_eq_left_iff
  infer_instance
#align simple_graph.inc_matrix_apply_eq_one_iff SimpleGraph.incMatrix_apply_eq_one_iff

end MulZeroOneClass

section NonAssocSemiring

variable [Fintype α] [NonAssocSemiring R] {a b : α} {e : Sym2 α}

/- warning: simple_graph.sum_inc_matrix_apply -> SimpleGraph.sum_incMatrix_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {a : α} [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ u1} R (Finset.sum.{u1, u2} R (Sym2.{u2} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Finset.univ.{u2} (Sym2.{u2} α) (Quotient.fintype.{u2} (Prod.{u2, u2} α α) (Prod.fintype.{u2, u2} α α _inst_1 _inst_1) (Sym2.Rel.setoid.{u2} α) (fun (a : Prod.{u2, u2} α α) (b : Prod.{u2, u2} α α) => Sym2.Rel.decidableRel.{u2} α (fun (a : α) (b : α) => _inst_3 a b) a b))) (fun (e : Sym2.{u2} α) => SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))) a e)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2)))))) (SimpleGraph.degree.{u2} α G a (SimpleGraph.neighborSetFintype.{u2} α G _inst_1 (fun (a : α) (b : α) => _inst_4 a b) a)))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {a : α} [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ u1} R (Finset.sum.{u1, u2} R (Sym2.{u2} α) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Finset.univ.{u2} (Sym2.{u2} α) (Quotient.fintype.{u2} (Prod.{u2, u2} α α) (instFintypeProd.{u2, u2} α α _inst_1 _inst_1) (Sym2.Rel.setoid.{u2} α) (fun (a : Prod.{u2, u2} α α) (b : Prod.{u2, u2} α α) => Sym2.instRelDecidable'.{u2} α (fun (a : α) (b : α) => _inst_3 a b) a b))) (fun (e : Sym2.{u2} α) => SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2) a e)) (Nat.cast.{u1} R (NonAssocSemiring.toNatCast.{u1} R _inst_2) (SimpleGraph.degree.{u2} α G a (SimpleGraph.neighborSetFintype.{u2} α G _inst_1 (fun (a : α) (b : α) => _inst_4 a b) a)))
Case conversion may be inaccurate. Consider using '#align simple_graph.sum_inc_matrix_apply SimpleGraph.sum_incMatrix_applyₓ'. -/
theorem sum_incMatrix_apply [DecidableEq α] [DecidableRel G.Adj] :
    (∑ e, G.incMatrix R a e) = G.degree a := by
  simp [inc_matrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset]
#align simple_graph.sum_inc_matrix_apply SimpleGraph.sum_incMatrix_apply

/- warning: simple_graph.inc_matrix_mul_transpose_diag -> SimpleGraph.incMatrix_mul_transpose_diag is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {a : α} [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ u1} R (Matrix.mul.{u1, u2, u2, u2} α (Sym2.{u2} α) α R (Quotient.fintype.{u2} (Prod.{u2, u2} α α) (Prod.fintype.{u2, u2} α α _inst_1 _inst_1) (Sym2.Rel.setoid.{u2} α) (fun (a : Prod.{u2, u2} α α) (b : Prod.{u2, u2} α α) => Sym2.Rel.decidableRel.{u2} α (fun (a : α) (b : α) => _inst_3 a b) a b)) (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2)))) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))))) a a) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2)))))) (SimpleGraph.degree.{u2} α G a (SimpleGraph.neighborSetFintype.{u2} α G _inst_1 (fun (a : α) (b : α) => _inst_4 a b) a)))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {a : α} [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ u1} R (Matrix.mul.{u1, u2, u2, u2} α (Sym2.{u2} α) α R (Quotient.fintype.{u2} (Prod.{u2, u2} α α) (instFintypeProd.{u2, u2} α α _inst_1 _inst_1) (Sym2.Rel.setoid.{u2} α) (fun (a : Prod.{u2, u2} α α) (b : Prod.{u2, u2} α α) => Sym2.instRelDecidable'.{u2} α (fun (a : α) (b : α) => _inst_3 a b) a b)) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2)) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2))) a a) (Nat.cast.{u1} R (NonAssocSemiring.toNatCast.{u1} R _inst_2) (SimpleGraph.degree.{u2} α G a (SimpleGraph.neighborSetFintype.{u2} α G _inst_1 (fun (a : α) (b : α) => _inst_4 a b) a)))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_mul_transpose_diag SimpleGraph.incMatrix_mul_transpose_diagₓ'. -/
theorem incMatrix_mul_transpose_diag [DecidableEq α] [DecidableRel G.Adj] :
    (G.incMatrix R ⬝ (G.incMatrix R)ᵀ) a a = G.degree a :=
  by
  rw [← sum_inc_matrix_apply]
  simp [Matrix.mul_apply, inc_matrix_apply', ← ite_and_mul_zero]
#align simple_graph.inc_matrix_mul_transpose_diag SimpleGraph.incMatrix_mul_transpose_diag

/- warning: simple_graph.sum_inc_matrix_apply_of_mem_edge_set -> SimpleGraph.sum_incMatrix_apply_of_mem_edgeSet is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {e : Sym2.{u2} α}, (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (coeFn.{succ u2, succ u2} (OrderEmbedding.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (SimpleGraph.hasLe.{u2} α) (Set.hasLe.{u2} (Sym2.{u2} α))) (fun (_x : RelEmbedding.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (LE.le.{u2} (SimpleGraph.{u2} α) (SimpleGraph.hasLe.{u2} α)) (LE.le.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasLe.{u2} (Sym2.{u2} α)))) => (SimpleGraph.{u2} α) -> (Set.{u2} (Sym2.{u2} α))) (RelEmbedding.hasCoeToFun.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (LE.le.{u2} (SimpleGraph.{u2} α) (SimpleGraph.hasLe.{u2} α)) (LE.le.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasLe.{u2} (Sym2.{u2} α)))) (SimpleGraph.edgeSetEmbedding.{u2} α) G)) -> (Eq.{succ u1} R (Finset.sum.{u1, u2} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Finset.univ.{u2} α _inst_1) (fun (a : α) => SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))) a e)) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {e : Sym2.{u2} α}, (Membership.mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.instMembershipSet.{u2} (Sym2.{u2} α)) e (SimpleGraph.edgeSet.{u2} α G)) -> (Eq.{succ u1} R (Finset.sum.{u1, u2} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Finset.univ.{u2} α _inst_1) (fun (a : α) => SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2) a e)) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocSemiring.toNatCast.{u1} R _inst_2) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align simple_graph.sum_inc_matrix_apply_of_mem_edge_set SimpleGraph.sum_incMatrix_apply_of_mem_edgeSetₓ'. -/
theorem sum_incMatrix_apply_of_mem_edgeSet :
    e ∈ G.edgeSetEmbedding → (∑ a, G.incMatrix R a e) = 2 := by
  classical
    refine' e.ind _
    intro a b h
    rw [mem_edge_set] at h
    rw [← Nat.cast_two, ← card_doubleton h.ne]
    simp only [inc_matrix_apply', sum_boole, mk_mem_incidence_set_iff, h, true_and_iff]
    congr 2
    ext e
    simp only [mem_filter, mem_univ, true_and_iff, mem_insert, mem_singleton]
#align simple_graph.sum_inc_matrix_apply_of_mem_edge_set SimpleGraph.sum_incMatrix_apply_of_mem_edgeSet

/- warning: simple_graph.sum_inc_matrix_apply_of_not_mem_edge_set -> SimpleGraph.sum_incMatrix_apply_of_not_mem_edgeSet is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {e : Sym2.{u2} α}, (Not (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (coeFn.{succ u2, succ u2} (OrderEmbedding.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (SimpleGraph.hasLe.{u2} α) (Set.hasLe.{u2} (Sym2.{u2} α))) (fun (_x : RelEmbedding.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (LE.le.{u2} (SimpleGraph.{u2} α) (SimpleGraph.hasLe.{u2} α)) (LE.le.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasLe.{u2} (Sym2.{u2} α)))) => (SimpleGraph.{u2} α) -> (Set.{u2} (Sym2.{u2} α))) (RelEmbedding.hasCoeToFun.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (LE.le.{u2} (SimpleGraph.{u2} α) (SimpleGraph.hasLe.{u2} α)) (LE.le.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasLe.{u2} (Sym2.{u2} α)))) (SimpleGraph.edgeSetEmbedding.{u2} α) G))) -> (Eq.{succ u1} R (Finset.sum.{u1, u2} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Finset.univ.{u2} α _inst_1) (fun (a : α) => SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))) a e)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {e : Sym2.{u2} α}, (Not (Membership.mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.instMembershipSet.{u2} (Sym2.{u2} α)) e (SimpleGraph.edgeSet.{u2} α G))) -> (Eq.{succ u1} R (Finset.sum.{u1, u2} R α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Finset.univ.{u2} α _inst_1) (fun (a : α) => SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2) a e)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.sum_inc_matrix_apply_of_not_mem_edge_set SimpleGraph.sum_incMatrix_apply_of_not_mem_edgeSetₓ'. -/
theorem sum_incMatrix_apply_of_not_mem_edgeSet (h : e ∉ G.edgeSetEmbedding) :
    (∑ a, G.incMatrix R a e) = 0 :=
  sum_eq_zero fun a _ => G.incMatrix_of_not_mem_incidenceSet fun he => h he.1
#align simple_graph.sum_inc_matrix_apply_of_not_mem_edge_set SimpleGraph.sum_incMatrix_apply_of_not_mem_edgeSet

/- warning: simple_graph.inc_matrix_transpose_mul_diag -> SimpleGraph.incMatrix_transpose_mul_diag is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {e : Sym2.{u2} α} [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ u1} R (Matrix.mul.{u1, u2, u2, u2} (Sym2.{u2} α) α (Sym2.{u2} α) R _inst_1 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2)))) e e) (ite.{succ u1} R (Membership.Mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.hasMem.{u2} (Sym2.{u2} α)) e (coeFn.{succ u2, succ u2} (OrderEmbedding.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (SimpleGraph.hasLe.{u2} α) (Set.hasLe.{u2} (Sym2.{u2} α))) (fun (_x : RelEmbedding.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (LE.le.{u2} (SimpleGraph.{u2} α) (SimpleGraph.hasLe.{u2} α)) (LE.le.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasLe.{u2} (Sym2.{u2} α)))) => (SimpleGraph.{u2} α) -> (Set.{u2} (Sym2.{u2} α))) (RelEmbedding.hasCoeToFun.{u2, u2} (SimpleGraph.{u2} α) (Set.{u2} (Sym2.{u2} α)) (LE.le.{u2} (SimpleGraph.{u2} α) (SimpleGraph.hasLe.{u2} α)) (LE.le.{u2} (Set.{u2} (Sym2.{u2} α)) (Set.hasLe.{u2} (Sym2.{u2} α)))) (SimpleGraph.edgeSetEmbedding.{u2} α) G)) (SimpleGraph.decidableMemEdgeSet.{u2} α G (fun (a : α) (b : α) => _inst_3 a b) e) (OfNat.ofNat.{u1} R 2 (OfNat.mk.{u1} R 2 (bit0.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2))) (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R _inst_2))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} α] [_inst_2 : NonAssocSemiring.{u1} R] {e : Sym2.{u2} α} [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ u1} R (Matrix.mul.{u1, u2, u2, u2} (Sym2.{u2} α) α (Sym2.{u2} α) R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R _inst_2)) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)) (NonAssocSemiring.toOne.{u1} R _inst_2)) e e) (ite.{succ u1} R (Membership.mem.{u2, u2} (Sym2.{u2} α) (Set.{u2} (Sym2.{u2} α)) (Set.instMembershipSet.{u2} (Sym2.{u2} α)) e (SimpleGraph.edgeSet.{u2} α G)) (SimpleGraph.decidableMemEdgeSet.{u2} α G (fun (a : α) (b : α) => _inst_3 a b) e) (OfNat.ofNat.{u1} R 2 (instOfNat.{u1} R 2 (NonAssocSemiring.toNatCast.{u1} R _inst_2) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MulZeroOneClass.toZero.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R _inst_2)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_transpose_mul_diag SimpleGraph.incMatrix_transpose_mul_diagₓ'. -/
theorem incMatrix_transpose_mul_diag [DecidableRel G.Adj] :
    ((G.incMatrix R)ᵀ ⬝ G.incMatrix R) e e = if e ∈ G.edgeSetEmbedding then 2 else 0 := by
  classical
    simp only [Matrix.mul_apply, inc_matrix_apply', transpose_apply, ← ite_and_mul_zero, one_mul,
      sum_boole, and_self_iff]
    split_ifs with h
    · revert h
      refine' e.ind _
      intro v w h
      rw [← Nat.cast_two, ← card_doubleton (G.ne_of_adj h)]
      simp [mk_mem_incidence_set_iff, G.mem_edge_set.mp h]
      congr 2
      ext u
      simp
    · revert h
      refine' e.ind _
      intro v w h
      simp [mk_mem_incidence_set_iff, G.mem_edge_set.not.mp h]
#align simple_graph.inc_matrix_transpose_mul_diag SimpleGraph.incMatrix_transpose_mul_diag

end NonAssocSemiring

section Semiring

variable [Fintype (Sym2 α)] [Semiring R] {a b : α} {e : Sym2 α}

/- warning: simple_graph.inc_matrix_mul_transpose_apply_of_adj -> SimpleGraph.incMatrix_mul_transpose_apply_of_adj is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} (Sym2.{u2} α)] [_inst_2 : Semiring.{u1} R] {a : α} {b : α}, (SimpleGraph.Adj.{u2} α G a b) -> (Eq.{succ u1} R (Matrix.mul.{u1, u2, u2, u2} α (Sym2.{u2} α) α R _inst_1 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))))) a b) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} (Sym2.{u2} α)] [_inst_2 : Semiring.{u1} R] {a : α} {b : α}, (SimpleGraph.Adj.{u2} α G a b) -> (Eq.{succ u1} R (Matrix.mul.{u1, u2, u2, u2} α (Sym2.{u2} α) α R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (SimpleGraph.incMatrix.{u1, u2} R α G (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (Semiring.toOne.{u1} R _inst_2)) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (Semiring.toOne.{u1} R _inst_2))) a b) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_2))))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_mul_transpose_apply_of_adj SimpleGraph.incMatrix_mul_transpose_apply_of_adjₓ'. -/
theorem incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) :
    (G.incMatrix R ⬝ (G.incMatrix R)ᵀ) a b = (1 : R) := by
  classical
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, inc_matrix_apply_mul_inc_matrix_apply,
      Set.indicator_apply, Pi.one_apply, sum_boole]
    convert Nat.cast_one
    convert card_singleton ⟦(a, b)⟧
    rw [← coe_eq_singleton, coe_filter_univ]
    exact G.incidence_set_inter_incidence_set_of_adj h
#align simple_graph.inc_matrix_mul_transpose_apply_of_adj SimpleGraph.incMatrix_mul_transpose_apply_of_adj

/- warning: simple_graph.inc_matrix_mul_transpose -> SimpleGraph.incMatrix_mul_transpose is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} (Sym2.{u2} α)] [_inst_2 : Semiring.{u1} R] [_inst_3 : Fintype.{u2} α] [_inst_4 : DecidableEq.{succ u2} α] [_inst_5 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{succ (max u2 u1)} (Matrix.{u2, u2, u1} α α R) (Matrix.mul.{u1, u2, u2, u2} α (Sym2.{u2} α) α R _inst_1 (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))) (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))))) (fun (a : α) (b : α) => ite.{succ u1} R (Eq.{succ u2} α a b) (_inst_4 a b) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))))) (SimpleGraph.degree.{u2} α G a (SimpleGraph.neighborSetFintype.{u2} α G _inst_3 (fun (a : α) (b : α) => _inst_5 a b) a))) (ite.{succ u1} R (SimpleGraph.Adj.{u2} α G a b) (_inst_5 a b) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2)))))))))
but is expected to have type
  forall {R : Type.{u1}} {α : Type.{u2}} (G : SimpleGraph.{u2} α) [_inst_1 : Fintype.{u2} (Sym2.{u2} α)] [_inst_2 : Semiring.{u1} R] [_inst_3 : Fintype.{u2} α] [_inst_4 : DecidableEq.{succ u2} α] [_inst_5 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Eq.{max (succ u1) (succ u2)} (Matrix.{u2, u2, u1} α α R) (Matrix.mul.{u1, u2, u2, u2} α (Sym2.{u2} α) α R _inst_1 (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))) (SimpleGraph.incMatrix.{u1, u2} R α G (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (Semiring.toOne.{u1} R _inst_2)) (Matrix.transpose.{u1, u2, u2} α (Sym2.{u2} α) R (SimpleGraph.incMatrix.{u1, u2} R α G (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2)) (Semiring.toOne.{u1} R _inst_2)))) (fun (a : α) (b : α) => ite.{succ u1} R (Eq.{succ u2} α a b) (_inst_4 a b) (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R _inst_2) (SimpleGraph.degree.{u2} α G a (SimpleGraph.neighborSetFintype.{u2} α G _inst_3 (fun (a : α) (b : α) => _inst_5 a b) a))) (ite.{succ u1} R (SimpleGraph.Adj.{u2} α G a b) (_inst_5 a b) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_2))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_2))))))
Case conversion may be inaccurate. Consider using '#align simple_graph.inc_matrix_mul_transpose SimpleGraph.incMatrix_mul_transposeₓ'. -/
theorem incMatrix_mul_transpose [Fintype α] [DecidableEq α] [DecidableRel G.Adj] :
    G.incMatrix R ⬝ (G.incMatrix R)ᵀ = fun a b =>
      if a = b then G.degree a else if G.Adj a b then 1 else 0 :=
  by
  ext (a b)
  split_ifs with h h'
  · subst b
    convert G.inc_matrix_mul_transpose_diag
  · exact G.inc_matrix_mul_transpose_apply_of_adj h'
  ·
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj h h', sum_const_zero]
#align simple_graph.inc_matrix_mul_transpose SimpleGraph.incMatrix_mul_transpose

end Semiring

end SimpleGraph

