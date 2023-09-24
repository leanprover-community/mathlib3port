/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
import Algebra.Lie.OfAssociative
import RingTheory.Derivation.Basic

#align_import ring_theory.derivation.lie from "leanprover-community/mathlib"@"5c1efce12ba86d4901463f61019832f6a4b1a0d0"

/-!
# Results

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

- `derivation.lie_algebra`: The `R`-derivations from `A` to `A` form an lie algebra over `R`.

-/


namespace Derivation

variable {R : Type _} [CommRing R]

variable {A : Type _} [CommRing A] [Algebra R A]

variable (D : Derivation R A A) {D1 D2 : Derivation R A A} (a : A)

section LieStructures

/-! # Lie structures -/


/-- The commutator of derivations is again a derivation. -/
instance : Bracket (Derivation R A A) (Derivation R A A) :=
  ⟨fun D1 D2 =>
    mk' ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ fun a b =>
      by
      simp only [Ring.lie_def, map_add, Algebra.id.smul_eq_mul, LinearMap.mul_apply, leibniz,
        coe_fn_coe, LinearMap.sub_apply]
      ring⟩

#print Derivation.commutator_coe_linear_map /-
@[simp]
theorem commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R A), (D2 : Module.End R A)⁆ :=
  rfl
#align derivation.commutator_coe_linear_map Derivation.commutator_coe_linear_map
-/

#print Derivation.commutator_apply /-
theorem commutator_apply : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl
#align derivation.commutator_apply Derivation.commutator_apply
-/

instance : LieRing (Derivation R A A)
    where
  add_lie d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_add d e f := by ext a; simp only [commutator_apply, add_apply, map_add]; ring
  lie_self d := by ext a; simp only [commutator_apply, add_apply, map_add]; ring_nf
  leibniz_lie d e f := by ext a; simp only [commutator_apply, add_apply, sub_apply, map_sub]; ring

instance : LieAlgebra R (Derivation R A A) :=
  { Derivation.module with
    lie_smul := fun r d e => by ext a;
      simp only [commutator_apply, map_smul, smul_sub, smul_apply] }

end LieStructures

end Derivation

