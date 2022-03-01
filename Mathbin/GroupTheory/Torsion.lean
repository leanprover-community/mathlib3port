/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathbin.GroupTheory.Exponent
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.GroupTheory.QuotientGroup

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `monoid.is_torsion` is a predicate asserting a monoid `G` is a torsion monoid, i.e. that all
  elements are of finite order. Torsion groups are also known as periodic groups.
* `add_monoid.is_torsion` the additive version of `monoid.is_torsion`.

## Future work

* Define `tor G` for the torsion subgroup of a group
* torsion-free groups
-/


universe u

variable {G : Type u}

open_locale Classical

namespace Monoidₓ

variable (G) [Monoidₓ G]

/-- A predicate on a monoid saying that all elements are of finite order.-/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def IsTorsion :=
  ∀ g : G, IsOfFinOrder g

end Monoidₓ

open Monoidₓ

variable [Groupₓ G] {N : Subgroup G}

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
theorem IsTorsion.subgroup (tG : IsTorsion G) (H : Subgroup G) : IsTorsion H := fun h =>
  (is_of_fin_order_iff_coe _ h).mpr <| tG h

/-- Quotient groups of torsion groups are torsion groups. -/
@[to_additive "Quotient groups of additive torsion groups are additive torsion groups."]
theorem IsTorsion.quotient_group [nN : N.Normal] (tG : IsTorsion G) : IsTorsion (G ⧸ N) := fun h =>
  (QuotientGroup.induction_on' h) fun g => (tG g).Quotient N g

/-- If a group exponent exists, the group is torsion. -/
@[to_additive ExponentExists.is_add_torsion]
theorem ExponentExists.is_torsion (h : ExponentExists G) : IsTorsion G := by
  obtain ⟨n, npos, hn⟩ := h
  intro g
  exact (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, npos, hn g⟩

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive IsAddTorsion.exponent_exists]
theorem IsTorsion.exponent_exists (tG : IsTorsion G) (bounded : (Set.Range fun g : G => orderOf g).Finite) :
    ExponentExists G :=
  exponent_exists_iff_ne_zero.mpr <|
    (exponent_ne_zero_iff_range_order_of_finite fun g => order_of_pos' (tG g)).mpr bounded

/-- Finite groups are torsion groups.-/
@[to_additive is_add_torsion_of_fintype]
theorem is_torsion_of_fintype [Fintype G] : IsTorsion G :=
  ExponentExists.is_torsion <| exponent_exists_iff_ne_zero.mpr exponent_ne_zero_of_fintype

