/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Abelian
import Mathbin.Algebra.Lie.Solvable
import Mathbin.LinearAlgebra.Dual

/-!
# Characters of Lie algebras

A character of a Lie algebra `L` over a commutative ring `R` is a morphism of Lie algebras `L → R`,
where `R` is regarded as a Lie algebra over itself via the ring commutator. For an Abelian Lie
algebra (e.g., a Cartan subalgebra of a semisimple Lie algebra) a character is just a linear form.

## Main definitions

  * `lie_algebra.lie_character`
  * `lie_algebra.lie_character_equiv_linear_dual`

## Tags

lie algebra, lie character
-/


universe u v w w₁

namespace LieAlgebra

variable (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L] [LieAlgebra R L]

/-- A character of a Lie algebra is a morphism to the scalars. -/
abbrev LieCharacter :=
  L →ₗ⁅R⁆ R

variable {R L}

@[simp]
theorem lie_character_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x,y⁆ = 0 := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_comm, sub_self]

theorem lie_character_apply_of_mem_derived (χ : LieCharacter R L) {x : L} (h : x ∈ derivedSeries R L 1) : χ x = 0 := by
  rw [derived_series_def, derived_series_of_ideal_succ, derived_series_of_ideal_zero, ← LieSubmodule.mem_coe_submodule,
    LieSubmodule.lie_ideal_oper_eq_linear_span] at h
  apply Submodule.span_induction h
  · rintro y ⟨⟨z, hz⟩, ⟨⟨w, hw⟩, rfl⟩⟩
    apply lie_character_apply_lie
    
  · exact χ.map_zero
    
  · intro y z hy hz
    rw [LieHom.map_add, hy, hz, add_zeroₓ]
    
  · intro t y hy
    rw [LieHom.map_smul, hy, smul_zero]
    

/-- For an Abelian Lie algebra, characters are just linear forms. -/
@[simps]
def lieCharacterEquivLinearDual [IsLieAbelian L] : LieCharacter R L ≃ Module.Dual R L where
  toFun := fun χ => (χ : L →ₗ[R] R)
  invFun := fun ψ =>
    { ψ with
      map_lie' := fun x y => by
        rw [LieModule.IsTrivial.trivial, LieRing.of_associative_ring_bracket, mul_comm, sub_self,
          LinearMap.to_fun_eq_coe, LinearMap.map_zero] }
  left_inv := fun χ => by
    ext
    rfl
  right_inv := fun ψ => by
    ext
    rfl

end LieAlgebra

