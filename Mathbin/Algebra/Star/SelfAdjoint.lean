/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

This file defines `self_adjoint R` (resp. `skew_adjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `is_star_normal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `star_module R₂ R`, then `self_adjoint R` has a natural
  `module (self_adjoint R₂) (self_adjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)`
  and not `module (self_adjoint ℂ) (self_adjoint R)`. We solve this issue by adding the typeclass
  `[has_trivial_star R₃]`, of which `ℝ` is an instance (registered in `data/real/basic`), and then
  add a `[module R₃ (self_adjoint R)]` instance whenever we have
  `[module R₃ R] [has_trivial_star R₃]`. (Another approach would have been to define
  `[star_invariant_scalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/


variable {R A : Type _}

/-- An element is self-adjoint if it is equal to its star. -/
def IsSelfAdjoint [HasStar R] (x : R) : Prop :=
  star x = x

/-- An element of a star monoid is normal if it commutes with its adjoint. -/
class IsStarNormal [Mul R] [HasStar R] (x : R) : Prop where
  star_comm_self : Commute (star x) x

export IsStarNormal (star_comm_self)

theorem star_comm_self' [Mul R] [HasStar R] (x : R) [IsStarNormal x] : star x * x = x * star x :=
  IsStarNormal.star_comm_self

namespace IsSelfAdjoint

theorem star_eq [HasStar R] {x : R} (hx : IsSelfAdjoint x) : star x = x :=
  hx

theorem _root_.is_self_adjoint_iff [HasStar R] {x : R} : IsSelfAdjoint x ↔ star x = x :=
  Iff.rfl

@[simp]
theorem star_mul_self [Semigroupₓ R] [StarSemigroup R] (x : R) : IsSelfAdjoint (star x * x) := by
  simp only [IsSelfAdjoint, star_mul, star_star]

@[simp]
theorem mul_star_self [Semigroupₓ R] [StarSemigroup R] (x : R) : IsSelfAdjoint (x * star x) := by
  simpa only [star_star] using star_mul_self (star x)

/-- Functions in a `star_hom_class` preserve self-adjoint elements. -/
theorem star_hom_apply {F R S : Type _} [HasStar R] [HasStar S] [StarHomClass F R S] {x : R} (hx : IsSelfAdjoint x)
    (f : F) : IsSelfAdjoint (f x) :=
  show star (f x) = f x from map_star f x ▸ congr_arg f hx

section AddGroupₓ

variable [AddGroupₓ R] [StarAddMonoid R]

variable (R)

theorem _root_.is_self_adjoint_zero : IsSelfAdjoint (0 : R) :=
  star_zero R

variable {R}

theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by
  simp only [is_self_adjoint_iff, star_add, hx.star_eq, hy.star_eq]

theorem neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x) := by
  simp only [is_self_adjoint_iff, star_neg, hx.star_eq]

theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by
  simp only [is_self_adjoint_iff, star_sub, hx.star_eq, hy.star_eq]

theorem bit0 {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (bit0 x) := by
  simp only [is_self_adjoint_iff, star_bit0, hx.star_eq]

end AddGroupₓ

section NonUnitalSemiringₓ

variable [NonUnitalSemiringₓ R] [StarRing R]

theorem conjugate {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (z * x * star z) := by
  simp only [is_self_adjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

theorem conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z * x * z) := by
  simp only [is_self_adjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

theorem is_star_normal {x : R} (hx : IsSelfAdjoint x) : IsStarNormal x :=
  ⟨by
    simp only [hx.star_eq]⟩

end NonUnitalSemiringₓ

section Ringₓ

variable [Ringₓ R] [StarRing R]

variable (R)

theorem _root_.is_self_adjoint_one : IsSelfAdjoint (1 : R) :=
  star_one R

variable {R}

theorem bit1 {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (bit1 x) := by
  simp only [is_self_adjoint_iff, star_bit1, hx.star_eq]

theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
  simp only [is_self_adjoint_iff, star_pow, hx.star_eq]

end Ringₓ

section NonUnitalCommRing

variable [NonUnitalCommRing R] [StarRing R]

theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
  simp only [is_self_adjoint_iff, star_mul', hx.star_eq, hy.star_eq]

end NonUnitalCommRing

section Field

variable [Field R] [StarRing R]

theorem inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [is_self_adjoint_iff, star_inv', hx.star_eq]

theorem div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x / y) := by
  simp only [is_self_adjoint_iff, star_div', hx.star_eq, hy.star_eq]

theorem zpow {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by
  simp only [is_self_adjoint_iff, star_zpow₀, hx.star_eq]

end Field

section HasSmul

variable [HasStar R] [HasTrivialStar R] [AddGroupₓ A] [StarAddMonoid A]

theorem smul [HasSmul R A] [StarModule R A] (r : R) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r • x) := by
  simp only [is_self_adjoint_iff, star_smul, star_trivial, hx.star_eq]

end HasSmul

end IsSelfAdjoint

variable (R)

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def selfAdjoint [AddGroupₓ R] [StarAddMonoid R] : AddSubgroup R where
  Carrier := { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' := fun _ _ hx => hx.add
  neg_mem' := fun _ hx => hx.neg

/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
def skewAdjoint [AddCommGroupₓ R] [StarAddMonoid R] : AddSubgroup R where
  Carrier := { x | star x = -x }
  zero_mem' :=
    show star (0 : R) = -0 by
      simp only [star_zero, neg_zero]
  add_mem' := fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by
      rw [star_add x y, hx, hy, neg_add]
  neg_mem' := fun x (hx : star x = -x) =>
    show star (-x) = - -x by
      simp only [hx, star_neg]

variable {R}

namespace selfAdjoint

section AddGroupₓ

variable [AddGroupₓ R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ selfAdjoint R ↔ star x = x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
theorem star_coe_eq {x : selfAdjoint R} : star (x : R) = x :=
  x.Prop

instance : Inhabited (selfAdjoint R) :=
  ⟨0⟩

end AddGroupₓ

section Ringₓ

variable [Ringₓ R] [StarRing R]

instance : One (selfAdjoint R) :=
  ⟨⟨1, is_self_adjoint_one R⟩⟩

@[simp, norm_cast]
theorem coe_one : ↑(1 : selfAdjoint R) = (1 : R) :=
  rfl

instance [Nontrivial R] : Nontrivial (selfAdjoint R) :=
  ⟨⟨0, 1, Subtype.ne_of_val_ne zero_ne_one⟩⟩

instance : HasNatCast (selfAdjoint R) :=
  ⟨fun n =>
    ⟨n,
      Nat.recOn n
        (by
          simp [zero_mem])
        fun k hk => (@Nat.cast_succₓ R _ k).symm ▸ add_mem hk (is_self_adjoint_one R)⟩⟩

instance : HasIntCast (selfAdjoint R) :=
  ⟨fun n =>
    ⟨n, by
      cases n <;> simp [show ↑n ∈ selfAdjoint R from (n : selfAdjoint R).2]
      refine' add_mem (is_self_adjoint_one R).neg (n : selfAdjoint R).2.neg⟩⟩

instance : Pow (selfAdjoint R) ℕ :=
  ⟨fun x n => ⟨(x : R) ^ n, x.Prop.pow n⟩⟩

@[simp, norm_cast]
theorem coe_pow (x : selfAdjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  rfl

end Ringₓ

section NonUnitalCommRing

variable [NonUnitalCommRing R] [StarRing R]

instance : Mul (selfAdjoint R) :=
  ⟨fun x y => ⟨(x : R) * y, x.Prop.mul y.Prop⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y :=
  rfl

end NonUnitalCommRing

section CommRingₓ

variable [CommRingₓ R] [StarRing R]

instance : CommRingₓ (selfAdjoint R) :=
  Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero coe_one (selfAdjoint R).coe_add coe_mul
    (selfAdjoint R).coeNeg (selfAdjoint R).coe_sub (selfAdjoint R).coe_nsmul (selfAdjoint R).coe_zsmul coe_pow
    (fun _ => rfl) fun _ => rfl

end CommRingₓ

section Field

variable [Field R] [StarRing R]

instance : Inv (selfAdjoint R) where inv := fun x => ⟨x.val⁻¹, x.Prop.inv⟩

@[simp, norm_cast]
theorem coe_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
  rfl

instance : Div (selfAdjoint R) where div := fun x y => ⟨x / y, x.Prop.div y.Prop⟩

@[simp, norm_cast]
theorem coe_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) :=
  rfl

instance : Pow (selfAdjoint R) ℤ where pow := fun x z => ⟨x ^ z, x.Prop.zpow z⟩

@[simp, norm_cast]
theorem coe_zpow (x : selfAdjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z :=
  rfl

theorem rat_cast_mem : ∀ x : ℚ, IsSelfAdjoint (x : R)
  | ⟨a, b, h1, h2⟩ => by
    rw [IsSelfAdjoint, Rat.cast_mk', star_mul', star_inv', star_nat_cast, star_int_cast]

instance : HasRatCast (selfAdjoint R) :=
  ⟨fun n => ⟨n, rat_cast_mem n⟩⟩

@[simp, norm_cast]
theorem coe_rat_cast (x : ℚ) : ↑(x : selfAdjoint R) = (x : R) :=
  rfl

instance hasQsmul : HasSmul ℚ (selfAdjoint R) :=
  ⟨fun a x =>
    ⟨a • x, by
      rw [Rat.smul_def] <;> exact (rat_cast_mem a).mul x.prop⟩⟩

@[simp, norm_cast]
theorem coe_rat_smul (x : selfAdjoint R) (a : ℚ) : ↑(a • x) = a • (x : R) :=
  rfl

instance : Field (selfAdjoint R) :=
  Function.Injective.field _ Subtype.coe_injective (selfAdjoint R).coe_zero coe_one (selfAdjoint R).coe_add coe_mul
    (selfAdjoint R).coeNeg (selfAdjoint R).coe_sub coe_inv coe_div (selfAdjoint R).coe_nsmul (selfAdjoint R).coe_zsmul
    coe_rat_smul coe_pow coe_zpow (fun _ => rfl) (fun _ => rfl) coe_rat_cast

end Field

section HasSmul

variable [HasStar R] [HasTrivialStar R] [AddGroupₓ A] [StarAddMonoid A]

instance [HasSmul R A] [StarModule R A] : HasSmul R (selfAdjoint A) :=
  ⟨fun r x => ⟨r • x, x.Prop.smul r⟩⟩

@[simp, norm_cast]
theorem coe_smul [HasSmul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) :=
  rfl

instance [Monoidₓ R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A) :=
  Function.Injective.mulAction coe Subtype.coe_injective coe_smul

instance [Monoidₓ R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A) :=
  Function.Injective.distribMulAction (selfAdjoint A).Subtype Subtype.coe_injective coe_smul

end HasSmul

section Module

variable [HasStar R] [HasTrivialStar R] [AddCommGroupₓ A] [StarAddMonoid A]

instance [Semiringₓ R] [Module R A] [StarModule R A] : Module R (selfAdjoint A) :=
  Function.Injective.module R (selfAdjoint A).Subtype Subtype.coe_injective coe_smul

end Module

end selfAdjoint

namespace skewAdjoint

section AddGroupₓ

variable [AddCommGroupₓ R] [StarAddMonoid R]

theorem mem_iff {x : R} : x ∈ skewAdjoint R ↔ star x = -x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
theorem star_coe_eq {x : skewAdjoint R} : star (x : R) = -x :=
  x.Prop

instance : Inhabited (skewAdjoint R) :=
  ⟨0⟩

theorem bit0_mem {x : R} (hx : x ∈ skewAdjoint R) : bit0 x ∈ skewAdjoint R := by
  rw [mem_iff, star_bit0, mem_iff.mp hx, bit0, bit0, neg_add]

end AddGroupₓ

section Ringₓ

variable [Ringₓ R] [StarRing R]

theorem conjugate {x : R} (hx : x ∈ skewAdjoint R) (z : R) : z * x * star z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

theorem conjugate' {x : R} (hx : x ∈ skewAdjoint R) (z : R) : star z * x * z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]

theorem is_star_normal_of_mem {x : R} (hx : x ∈ skewAdjoint R) : IsStarNormal x :=
  ⟨by
    simp only [mem_iff] at hx
    simp only [hx, Commute.neg_left]⟩

instance (x : skewAdjoint R) : IsStarNormal (x : R) :=
  is_star_normal_of_mem (SetLike.coe_mem _)

end Ringₓ

section HasSmul

variable [HasStar R] [HasTrivialStar R] [AddCommGroupₓ A] [StarAddMonoid A]

theorem smul_mem [Monoidₓ R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A} (h : x ∈ skewAdjoint A) :
    r • x ∈ skewAdjoint A := by
  rw [mem_iff, star_smul, star_trivial, mem_iff.mp h, smul_neg r]

instance [Monoidₓ R] [DistribMulAction R A] [StarModule R A] : HasSmul R (skewAdjoint A) :=
  ⟨fun r x => ⟨r • x, smul_mem r x.Prop⟩⟩

@[simp, norm_cast]
theorem coe_smul [Monoidₓ R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) :=
  rfl

instance [Monoidₓ R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A) :=
  Function.Injective.distribMulAction (skewAdjoint A).Subtype Subtype.coe_injective coe_smul

instance [Semiringₓ R] [Module R A] [StarModule R A] : Module R (skewAdjoint A) :=
  Function.Injective.module R (skewAdjoint A).Subtype Subtype.coe_injective coe_smul

end HasSmul

end skewAdjoint

instance is_star_normal_zero [Semiringₓ R] [StarRing R] : IsStarNormal (0 : R) :=
  ⟨by
    simp only [star_comm_self, star_zero]⟩

instance is_star_normal_one [Monoidₓ R] [StarSemigroup R] : IsStarNormal (1 : R) :=
  ⟨by
    simp only [star_comm_self, star_one]⟩

instance is_star_normal_star_self [Monoidₓ R] [StarSemigroup R] {x : R} [IsStarNormal x] : IsStarNormal (star x) :=
  ⟨show star (star x) * star x = star x * star (star x) by
      rw [star_star, star_comm_self']⟩

-- see Note [lower instance priority]
instance (priority := 100) HasTrivialStar.is_star_normal [Monoidₓ R] [StarSemigroup R] [HasTrivialStar R] {x : R} :
    IsStarNormal x :=
  ⟨by
    rw [star_trivial]⟩

-- see Note [lower instance priority]
instance (priority := 100) CommMonoidₓ.is_star_normal [CommMonoidₓ R] [StarSemigroup R] {x : R} : IsStarNormal x :=
  ⟨mul_comm _ _⟩

