/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Algebra.GroupRingAction
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Instances on punit

This file collects facts about algebraic structures on the one-element type, e.g. that it is a
commutative ring.
-/


universe u

namespace PUnit

variable {R S : Type _} (x y : PUnit.{u + 1}) (s : Set PUnit.{u + 1})

@[to_additive]
instance : CommGroupₓ PUnit := by
  refine_struct
      { mul := fun _ _ => star, one := star, inv := fun _ => star, div := fun _ _ => star, npow := fun _ _ => star,
        zpow := fun _ _ => star.. } <;>
    intros <;> exact Subsingleton.elimₓ _ _

@[simp, to_additive]
theorem one_eq : (1 : PUnit) = star :=
  rfl

@[simp, to_additive]
theorem mul_eq : x * y = star :=
  rfl

-- `sub_eq` simplifies `punit.sub_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive]
theorem div_eq : x / y = star :=
  rfl

-- `neg_eq` simplifies `punit.neg_eq`, but the latter is eligible for `dsimp`
@[simp, nolint simp_nf, to_additive]
theorem inv_eq : x⁻¹ = star :=
  rfl

instance : CommRingₓ PUnit := by
  refine' { PUnit.commGroup, PUnit.addCommGroup with natCast := fun _ => PUnit.unit.. } <;>
    intros <;> exact Subsingleton.elimₓ _ _

instance : CancelCommMonoidWithZero PUnit := by
  refine' { PUnit.commRing with .. } <;> intros <;> exact Subsingleton.elimₓ _ _

instance : NormalizedGcdMonoid PUnit := by
  refine'
      { gcd := fun _ _ => star, lcm := fun _ _ => star, normUnit := fun x => 1,
        gcd_dvd_left := fun _ _ => ⟨star, Subsingleton.elimₓ _ _⟩,
        gcd_dvd_right := fun _ _ => ⟨star, Subsingleton.elimₓ _ _⟩,
        dvd_gcd := fun _ _ _ _ _ => ⟨star, Subsingleton.elimₓ _ _⟩,
        gcd_mul_lcm := fun _ _ => ⟨1, Subsingleton.elimₓ _ _⟩.. } <;>
    intros <;> exact Subsingleton.elimₓ _ _

@[simp]
theorem gcd_eq : gcd x y = star :=
  rfl

@[simp]
theorem lcm_eq : lcm x y = star :=
  rfl

@[simp]
theorem norm_unit_eq : normUnit x = 1 :=
  rfl

instance : CanonicallyOrderedAddMonoid PUnit := by
  refine'
      { PUnit.commRing, PUnit.completeBooleanAlgebra with
        exists_add_of_le := fun _ _ _ => ⟨star, Subsingleton.elimₓ _ _⟩.. } <;>
    intros <;> trivial

instance : LinearOrderedCancelAddCommMonoid PUnit :=
  { PUnit.canonicallyOrderedAddMonoid, PUnit.linearOrder with add_left_cancel := fun _ _ _ _ => Subsingleton.elimₓ _ _,
    le_of_add_le_add_left := fun _ _ _ _ => trivialₓ }

instance : HasSmul R PUnit where smul := fun _ _ => unit

@[simp]
theorem smul_eq (r : R) : r • y = star :=
  rfl

instance : IsCentralScalar R PUnit :=
  ⟨fun _ _ => rfl⟩

instance : SmulCommClass R S PUnit :=
  ⟨fun _ _ _ => Subsingleton.elimₓ _ _⟩

instance [HasSmul R S] : IsScalarTower R S PUnit :=
  ⟨fun _ _ _ => Subsingleton.elimₓ _ _⟩

instance [Zero R] : SmulWithZero R PUnit := by
  refine' { PUnit.hasSmul with .. } <;> intros <;> exact Subsingleton.elimₓ _ _

instance [Monoidₓ R] : MulAction R PUnit := by
  refine' { PUnit.hasSmul with .. } <;> intros <;> exact Subsingleton.elimₓ _ _

instance [Monoidₓ R] : DistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elimₓ _ _

instance [Monoidₓ R] : MulDistribMulAction R PUnit := by
  refine' { PUnit.mulAction with .. } <;> intros <;> exact Subsingleton.elimₓ _ _

instance [Semiringₓ R] : MulSemiringAction R PUnit :=
  { PUnit.distribMulAction, PUnit.mulDistribMulAction with }

instance [MonoidWithZeroₓ R] : MulActionWithZero R PUnit :=
  { PUnit.mulAction, PUnit.smulWithZero with }

instance [Semiringₓ R] : Module R PUnit := by
  refine' { PUnit.distribMulAction with .. } <;> intros <;> exact Subsingleton.elimₓ _ _

end PUnit

