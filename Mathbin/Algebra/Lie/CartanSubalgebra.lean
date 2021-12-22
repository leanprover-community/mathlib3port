import Mathbin.Algebra.Lie.Nilpotent

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `lie_subalgebra.normalizer`
  * `lie_subalgebra.le_normalizer_of_ideal`
  * `lie_subalgebra.is_cartan_subalgebra`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/


universe u v w w₁ w₂

variable {R : Type u} {L : Type v}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

namespace LieSubalgebra

/--  The normalizer of a Lie subalgebra `H` is the set of elements of the Lie algebra whose bracket
with any element of `H` lies in `H`. It is the Lie algebra equivalent of the group-theoretic
normalizer (see `subgroup.normalizer`) and is an idealizer in the sense of abstract algebra. -/
def normalizer : LieSubalgebra R L :=
  { Carrier := { x : L | ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H },
    zero_mem' := fun y hy => by
      rw [zero_lie y]
      exact H.zero_mem,
    add_mem' := fun z₁ z₂ h₁ h₂ y hy => by
      rw [add_lie]
      exact H.add_mem (h₁ y hy) (h₂ y hy),
    smul_mem' := fun t y hy z hz => by
      rw [smul_lie]
      exact H.smul_mem t (hy z hz),
    lie_mem' := fun z₁ z₂ h₁ h₂ y hy => by
      rw [lie_lie]
      exact H.sub_mem (h₁ _ (h₂ y hy)) (h₂ _ (h₁ y hy)) }

theorem mem_normalizer_iff (x : L) : x ∈ H.normalizer ↔ ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H :=
  Iff.rfl

theorem le_normalizer : H ≤ H.normalizer := fun x hx => show ∀ y : L, y ∈ H → ⁅x,y⁆ ∈ H from fun y => H.lie_mem hx

/--  A Lie subalgebra is an ideal of its normalizer. -/
theorem ideal_in_normalizer : ∀ x y : L, x ∈ H.normalizer → y ∈ H → ⁅x,y⁆ ∈ H := fun x y h => h y

/--  The normalizer of a Lie subalgebra `H` is the maximal Lie subalgebra in which `H` is a Lie
ideal. -/
theorem le_normalizer_of_ideal {N : LieSubalgebra R L} (h : ∀ x y : L, x ∈ N → y ∈ H → ⁅x,y⁆ ∈ H) : N ≤ H.normalizer :=
  fun x hx y => h x y hx

/--  A Cartan subalgebra is a nilpotent, self-normalizing subalgebra. -/
class is_cartan_subalgebra : Prop where
  nilpotent : LieAlgebra.IsNilpotent R H
  self_normalizing : H.normalizer = H

end LieSubalgebra

@[simp]
theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRingₓ R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_trueₓ] using fun y hy => I.lie_mem hy

open LieIdeal

/--  A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance LieAlgebra.top_is_cartan_subalgebra_of_nilpotent [LieAlgebra.IsNilpotent R L] :
    LieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where
  nilpotent := inferInstance
  self_normalizing := by
    rw [← top_coe_lie_subalgebra, normalizer_eq_top, top_coe_lie_subalgebra]

