import Mathbin.Algebra.Star.Basic
import Mathbin.GroupTheory.Subgroup.Basic

/-!
# Self-adjoint elements of a star additive group

This file defines `self_adjoint R`, where `R` is a star additive monoid, as the additive subgroup
containing the elements that satisfy `star x = x`. This includes, for instance, Hermitian
operators on Hilbert spaces.

## TODO

* If `R` is a `star_module R₂ R`, put a module structure on `self_adjoint R`. This would naturally
  be a `module (self_adjoint R₂) (self_adjoint R)`, but doing this literally would be undesirable
  since in the main case of interest (`R₂ = ℂ`) we want `module ℝ (self_adjoint R)` and not
  `module (self_adjoint ℂ) (self_adjoint R)`. One way of doing this would be to add the typeclass
  `[has_trivial_star R]`, of which `ℝ` would be an instance, and then add a
  `[module R (self_adjoint E)]` instance whenever we have `[module R E] [has_trivial_star E]`.
  Another one would be to define a `[star_invariant_scalars R E]` to express the fact that
  `star (x • v) = x • star v`.

* Define `λ z x, z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `conj_act` for groups), and then state the fact that `self_adjoint R` is
  invariant under it.

-/


variable (R : Type _)

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
def selfAdjoint [AddGroupₓ R] [StarAddMonoid R] : AddSubgroup R where
  Carrier := { x | star x = x }
  zero_mem' := star_zero R
  add_mem' := fun x y hx : star x = x hy : star y = y =>
    show star (x + y) = x + y by
      simp only [star_add x y, hx, hy]
  neg_mem' := fun x hx : star x = x =>
    show star (-x) = -x by
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
  x.prop

end AddGroupₓ

instance [AddCommGroupₓ R] [StarAddMonoid R] : AddCommGroupₓ (selfAdjoint R) :=
  { AddSubgroup.toAddGroup (selfAdjoint R) with add_comm := add_commₓ }

section Ringₓ

variable [Ringₓ R] [StarRing R]

instance : HasOne (selfAdjoint R) :=
  ⟨⟨1, by
      rw [mem_iff, star_one]⟩⟩

@[simp, norm_cast]
theorem coe_one : (coeₓ : selfAdjoint R → R) (1 : selfAdjoint R) = (1 : R) :=
  rfl

theorem one_mem : (1 : R) ∈ selfAdjoint R := by
  simp only [mem_iff, star_one]

theorem bit0_mem {x : R} (hx : x ∈ selfAdjoint R) : bit0 x ∈ selfAdjoint R := by
  simp only [mem_iff, star_bit0, mem_iff.mp hx]

theorem bit1_mem {x : R} (hx : x ∈ selfAdjoint R) : bit1 x ∈ selfAdjoint R := by
  simp only [mem_iff, star_bit1, mem_iff.mp hx]

theorem conjugate {x : R} (hx : x ∈ selfAdjoint R) (z : R) : z * x * star z ∈ selfAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assocₓ]

theorem conjugate' {x : R} (hx : x ∈ selfAdjoint R) (z : R) : star z * x * z ∈ selfAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, mul_assocₓ]

end Ringₓ

section CommRingₓ

variable [CommRingₓ R] [StarRing R]

instance : Mul (selfAdjoint R) :=
  ⟨fun x y =>
    ⟨(x : R) * y, by
      simp only [mem_iff, star_mul', star_coe_eq]⟩⟩

@[simp, norm_cast]
theorem coe_mul (x y : selfAdjoint R) : (coeₓ : selfAdjoint R → R) (x * y) = (x : R) * y :=
  rfl

instance : CommRingₓ (selfAdjoint R) :=
  { selfAdjoint.addCommGroup, selfAdjoint.hasOne, selfAdjoint.hasMul with
    mul_assoc := fun x y z => by
      ext
      exact mul_assocₓ _ _ _,
    one_mul := fun x => by
      ext
      simp only [coe_mul, one_mulₓ, coe_one],
    mul_one := fun x => by
      ext
      simp only [mul_oneₓ, coe_mul, coe_one],
    mul_comm := fun x y => by
      ext
      exact mul_commₓ _ _,
    left_distrib := fun x y z => by
      ext
      exact left_distrib _ _ _,
    right_distrib := fun x y z => by
      ext
      exact right_distrib _ _ _ }

end CommRingₓ

section Field

variable [Field R] [StarRing R]

instance : Field (selfAdjoint R) :=
  { selfAdjoint.commRing with
    inv := fun x =>
      ⟨x.val⁻¹, by
        simp only [mem_iff, star_inv', star_coe_eq, Subtype.val_eq_coe]⟩,
    exists_pair_ne := ⟨0, 1, Subtype.ne_of_val_ne zero_ne_one⟩,
    mul_inv_cancel := fun x hx => by
      ext
      exact mul_inv_cancel fun H => hx $ Subtype.eq H,
    inv_zero := by
      ext
      exact inv_zero }

@[simp, norm_cast]
theorem coe_inv (x : selfAdjoint R) : (coeₓ : selfAdjoint R → R) (x⁻¹) = (x : R)⁻¹ :=
  rfl

end Field

end selfAdjoint

