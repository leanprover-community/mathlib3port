/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Nilpotent
import Mathbin.Algebra.Lie.Centralizer

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `lie_subalgebra.is_cartan_subalgebra`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/


universe u v w w₁ w₂

variable {R : Type u} {L : Type v}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

namespace LieSubalgebra

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class IsCartanSubalgebra : Prop where
  nilpotent : LieAlgebra.IsNilpotent R H
  self_normalizing : H.normalizer = H

instance [H.IsCartanSubalgebra] : LieAlgebra.IsNilpotent R H :=
  is_cartan_subalgebra.nilpotent

@[simp]
theorem centralizer_eq_self_of_is_cartan_subalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H.toLieSubmodule.Centralizer = H.toLieSubmodule := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff, coe_centralizer_eq_normalizer, is_cartan_subalgebra.self_normalizing,
    coe_to_lie_submodule]

end LieSubalgebra

@[simp]
theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRingₓ R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [← LieSubalgebra.mem_normalizer_iff, ← LieSubalgebra.mem_top, ← iff_trueₓ] using fun y hy => I.lie_mem hy

open LieIdeal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance LieAlgebra.top_is_cartan_subalgebra_of_nilpotent [LieAlgebra.IsNilpotent R L] :
    LieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where
  nilpotent := inferInstance
  self_normalizing := by
    rw [← top_coe_lie_subalgebra, normalizer_eq_top, top_coe_lie_subalgebra]

