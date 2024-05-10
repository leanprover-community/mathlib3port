/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import GroupTheory.GroupAction.Hom
import Algebra.Ring.Subring.Pointwise

#align_import algebra.group_ring_action.invariant from "leanprover-community/mathlib"@"1dac236edca9b4b6f5f00b1ad831e35f89472837"

/-! # Subrings invariant under an action 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


section Ring

variable (M R : Type _) [Monoid M] [Ring R] [MulSemiringAction M R]

variable (S : Subring R)

open MulAction

variable {R}

#print IsInvariantSubring /-
/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S
#align is_invariant_subring IsInvariantSubring
-/

#print IsInvariantSubring.toMulSemiringAction /-
instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] : MulSemiringAction M S
    where
  smul m x := ⟨m • x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul s := Subtype.eq <| one_smul M s
  hMul_smul m₁ m₂ s := Subtype.eq <| hMul_smul m₁ m₂ s
  smul_add m s₁ s₂ := Subtype.eq <| smul_add m s₁ s₂
  smul_zero m := Subtype.eq <| smul_zero m
  smul_one m := Subtype.eq <| smul_one m
  smul_hMul m s₁ s₂ := Subtype.eq <| smul_mul' m s₁ s₂
#align is_invariant_subring.to_mul_semiring_action IsInvariantSubring.toMulSemiringAction
-/

end Ring

section

variable (M : Type _) [Monoid M]

variable {R' : Type _} [Ring R'] [MulSemiringAction M R']

variable (U : Subring R') [IsInvariantSubring M U]

#print IsInvariantSubring.subtypeHom /-
/-- The canonical inclusion from an invariant subring. -/
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.Subtype with map_smul' := fun m s => rfl }
#align is_invariant_subring.subtype_hom IsInvariantSubring.subtypeHom
-/

#print IsInvariantSubring.coe_subtypeHom /-
@[simp]
theorem IsInvariantSubring.coe_subtypeHom : (IsInvariantSubring.subtypeHom M U : U → R') = coe :=
  rfl
#align is_invariant_subring.coe_subtype_hom IsInvariantSubring.coe_subtypeHom
-/

#print IsInvariantSubring.coe_subtypeHom' /-
@[simp]
theorem IsInvariantSubring.coe_subtypeHom' :
    (IsInvariantSubring.subtypeHom M U : U →+* R') = U.Subtype :=
  rfl
#align is_invariant_subring.coe_subtype_hom' IsInvariantSubring.coe_subtypeHom'
-/

end

