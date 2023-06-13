/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.ring.ideal
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.RingTheory.Ideal.Quotient

/-!
# Ideals and quotients of topological rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `ideal.closure` to be the topological closure of an ideal in a topological
ring. We also define a `topological_space` structure on the quotient of a topological ring by an
ideal and prove that the quotient is a topological ring.
-/


section Ring

variable {R : Type _} [TopologicalSpace R] [Ring R] [TopologicalRing R]

#print Ideal.closure /-
/-- The closure of an ideal in a topological ring as an ideal. -/
protected def Ideal.closure (I : Ideal R) : Ideal R :=
  {
    AddSubmonoid.topologicalClosure
      I.toAddSubmonoid with
    carrier := closure I
    smul_mem' := fun c x hx => map_mem_closure (mulLeft_continuous _) hx fun a => I.mul_mem_left c }
#align ideal.closure Ideal.closure
-/

#print Ideal.coe_closure /-
@[simp]
theorem Ideal.coe_closure (I : Ideal R) : (I.closure : Set R) = closure I :=
  rfl
#align ideal.coe_closure Ideal.coe_closure
-/

#print Ideal.closure_eq_of_isClosed /-
@[simp]
theorem Ideal.closure_eq_of_isClosed (I : Ideal R) [hI : IsClosed (I : Set R)] : I.closure = I :=
  SetLike.ext' hI.closure_eq
#align ideal.closure_eq_of_is_closed Ideal.closure_eq_of_isClosed
-/

end Ring

section CommRing

variable {R : Type _} [TopologicalSpace R] [CommRing R] (N : Ideal R)

open Ideal.Quotient

#print topologicalRingQuotientTopology /-
instance topologicalRingQuotientTopology : TopologicalSpace (R ⧸ N) :=
  Quotient.topologicalSpace
#align topological_ring_quotient_topology topologicalRingQuotientTopology
-/

-- note for the reader: in the following, `mk` is `ideal.quotient.mk`, the canonical map `R → R/I`.
variable [TopologicalRing R]

#print QuotientRing.isOpenMap_coe /-
theorem QuotientRing.isOpenMap_coe : IsOpenMap (mk N) :=
  by
  intro s s_op
  change IsOpen (mk N ⁻¹' (mk N '' s))
  rw [quotient_ring_saturate]
  exact isOpen_iUnion fun ⟨n, _⟩ => isOpenMap_add_left n s s_op
#align quotient_ring.is_open_map_coe QuotientRing.isOpenMap_coe
-/

#print QuotientRing.quotientMap_coe_coe /-
theorem QuotientRing.quotientMap_coe_coe : QuotientMap fun p : R × R => (mk N p.1, mk N p.2) :=
  IsOpenMap.to_quotientMap ((QuotientRing.isOpenMap_coe N).Prod (QuotientRing.isOpenMap_coe N))
    ((continuous_quot_mk.comp continuous_fst).prod_mk (continuous_quot_mk.comp continuous_snd))
    (by rintro ⟨⟨x⟩, ⟨y⟩⟩ <;> exact ⟨(x, y), rfl⟩)
#align quotient_ring.quotient_map_coe_coe QuotientRing.quotientMap_coe_coe
-/

#print topologicalRing_quotient /-
instance topologicalRing_quotient : TopologicalRing (R ⧸ N) :=
  TopologicalSemiring.toTopologicalRing
    { continuous_add :=
        have cont : Continuous (mk N ∘ fun p : R × R => p.fst + p.snd) :=
          continuous_quot_mk.comp continuous_add
        (QuotientMap.continuous_iff (QuotientRing.quotientMap_coe_coe N)).mpr cont
      continuous_mul :=
        have cont : Continuous (mk N ∘ fun p : R × R => p.fst * p.snd) :=
          continuous_quot_mk.comp continuous_mul
        (QuotientMap.continuous_iff (QuotientRing.quotientMap_coe_coe N)).mpr cont }
#align topological_ring_quotient topologicalRing_quotient
-/

end CommRing

