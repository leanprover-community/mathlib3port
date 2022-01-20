import Mathbin.Data.Finsupp.Basic

/-!
# The pointwise product on `finsupp`.

For the convolution product on `finsupp` when the domain has a binary operation,
see the type synonyms `add_monoid_algebra`
(which is in turn used to define `polynomial` and `mv_polynomial`)
and `monoid_algebra`.
-/


noncomputable section

open Finset

universe u₁ u₂ u₃ u₄ u₅

variable {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace Finsupp

/-! ### Declarations about the pointwise product on `finsupp`s -/


section

variable [MulZeroClass β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance : Mul (α →₀ β) :=
  ⟨zip_with (· * ·) (mul_zero 0)⟩

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl

theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} : (g₁ * g₂).Support ⊆ g₁.support ∩ g₂.support := by
  intro a h
  simp only [mul_apply, mem_support_iff] at h
  simp only [mem_support_iff, mem_inter, Ne.def]
  rw [← not_or_distrib]
  intro w
  apply h
  cases w <;>
    · rw [w]
      simp
      

instance : MulZeroClass (α →₀ β) where
  zero := 0
  mul := · * ·
  mul_zero := fun f => by
    ext
    simp only [mul_apply, zero_apply, mul_zero]
  zero_mul := fun f => by
    ext
    simp only [mul_apply, zero_apply, zero_mul]

end

instance [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  { (inferInstance : MulZeroClass (α →₀ β)) with mul := · * ·,
    mul_assoc := fun f g h => by
      ext
      simp only [mul_apply, mul_assocₓ] }

instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →₀ β) :=
  { (inferInstance : MulZeroClass (α →₀ β)), (inferInstance : AddCommMonoidₓ (α →₀ β)) with
    left_distrib := fun f g h => by
      ext
      simp (config := { proj := false })only [mul_apply, add_apply, left_distrib],
    right_distrib := fun f g h => by
      ext
      simp (config := { proj := false })only [mul_apply, add_apply, right_distrib] }

instance [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  { (inferInstance : Semigroupₓ (α →₀ β)), (inferInstance : NonUnitalNonAssocSemiring (α →₀ β)) with }

instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  { (inferInstance : MulZeroClass (α →₀ β)), (inferInstance : AddCommGroupₓ (α →₀ β)) with
    left_distrib := fun f g h => by
      ext
      simp (config := { proj := false })only [mul_apply, add_apply, left_distrib],
    right_distrib := fun f g h => by
      ext
      simp (config := { proj := false })only [mul_apply, add_apply, right_distrib] }

/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwise_module [Semiringₓ β] : Module (α → β) (α →₀ β) where
  smul := fun f g =>
    Finsupp.ofSupportFinite (fun a => f a • g a)
      (by
        apply Set.Finite.subset g.finite_support
        simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne.def, Finsupp.fun_support_eq, Finset.mem_coe]
        intro x hx h
        apply hx
        rw [h, smul_zero])
  one_smul := fun b => by
    ext a
    simp only [one_smul, Pi.one_apply, Finsupp.of_support_finite_coe]
  mul_smul := fun x y b => by
    simp [Finsupp.of_support_finite_coe, mul_smul]
  smul_add := fun r x y =>
    Finsupp.ext fun a => by
      simpa only [smul_add, Pi.add_apply, coe_add]
  smul_zero := fun b =>
    Finsupp.ext
      (by
        simp [Finsupp.of_support_finite_coe, smul_zero])
  zero_smul := fun a =>
    Finsupp.ext fun b => by
      simp [Finsupp.of_support_finite_coe]
  add_smul := fun r s x =>
    Finsupp.ext fun b => by
      simp [Finsupp.of_support_finite_coe, add_smul]

@[simp]
theorem coe_pointwise_module [Semiringₓ β] (f : α → β) (g : α →₀ β) : ⇑(f • g) = f • g :=
  rfl

end Finsupp

