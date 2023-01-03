/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module order.atoms.finite
! leanprover-community/mathlib commit 6cb77a8eaff0ddd100e87b1591c6d3ad319514ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite
import Mathbin.Order.Atoms

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

This module contains some results on atoms and simple lattices in the finite context.

## Main results
  * `finite.to_is_atomic`, `finite.to_is_coatomic`: Finite partial orders with bottom resp. top
    are atomic resp. coatomic.

-/


variable {α β : Type _}

namespace IsSimpleOrder

section DecidableEq

/- It is important that `is_simple_order` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply. -/
instance (priority := 200) {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    Fintype α :=
  Fintype.ofEquiv Bool equivBool.symm

end DecidableEq

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} :=
  by
  change Finset.map _ (Finset.univ : Finset Bool) = _
  rw [Fintype.univ_bool]
  simp only [Finset.map_insert, Function.Embedding.coeFn_mk, Finset.map_singleton]
  rfl
#align fintype.is_simple_order.univ Fintype.IsSimpleOrder.univ

theorem card : Fintype.card α = 2 :=
  (Fintype.of_equiv_card _).trans Fintype.card_bool
#align fintype.is_simple_order.card Fintype.IsSimpleOrder.card

end IsSimpleOrder

end Fintype

namespace Bool

instance : IsSimpleOrder Bool :=
  ⟨fun a =>
    by
    rw [← Finset.mem_singleton, or_comm, ← Finset.mem_insert, top_eq_true, bot_eq_false, ←
      Fintype.univ_bool]
    apply Finset.mem_univ⟩

end Bool

section Fintype

open Finset

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_is_coatomic [PartialOrder α] [OrderTop α] [Finite α] :
    IsCoatomic α :=
  by
  refine' IsCoatomic.mk fun b => or_iff_not_imp_left.2 fun ht => _
  obtain ⟨c, hc, hmax⟩ :=
    Set.Finite.exists_maximal_wrt id { x : α | b ≤ x ∧ x ≠ ⊤ } (Set.to_finite _) ⟨b, le_rfl, ht⟩
  refine' ⟨c, ⟨hc.2, fun y hcy => _⟩, hc.1⟩
  by_contra hyt
  obtain rfl : c = y := hmax y ⟨hc.1.trans hcy.le, hyt⟩ hcy.le
  exact (lt_self_iff_false _).mp hcy
#align finite.to_is_coatomic Finite.to_is_coatomic

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_is_atomic [PartialOrder α] [OrderBot α] [Finite α] :
    IsAtomic α :=
  is_coatomic_dual_iff_is_atomic.mp Finite.to_is_coatomic
#align finite.to_is_atomic Finite.to_is_atomic

end Fintype

