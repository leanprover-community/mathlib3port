/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
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

variable [MulZeroClassₓ β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance : Mul (α →₀ β) :=
  ⟨zipWith (· * ·) (mul_zero 0)⟩

theorem coe_mul (g₁ g₂ : α →₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl

theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} : (g₁ * g₂).Support ⊆ g₁.Support ∩ g₂.Support := by
  intro a h
  simp only [mul_apply, mem_support_iff] at h
  simp only [mem_support_iff, mem_inter, Ne.def]
  rw [← not_or_distrib]
  intro w
  apply h
  cases w <;>
    · rw [w]
      simp
      

instance : MulZeroClassₓ (α →₀ β) :=
  Finsupp.coe_fn_injective.MulZeroClass _ coe_zero coe_mul

end

instance [SemigroupWithZeroₓ β] : SemigroupWithZeroₓ (α →₀ β) :=
  Finsupp.coe_fn_injective.SemigroupWithZero _ coe_zero coe_mul

-- note we cannot use `function.injective.non_unital_non_assoc_semiring` here as it creates
-- a conflicting `nsmul` field
instance [NonUnitalNonAssocSemiringₓ β] : NonUnitalNonAssocSemiringₓ (α →₀ β) :=
  { (Function.Injective.distrib _ Finsupp.coe_fn_injective coe_add coe_mul : Distribₓ (α →₀ β)),
    (Finsupp.mulZeroClass : MulZeroClassₓ (α →₀ β)), (Finsupp.addCommMonoid : AddCommMonoidₓ (α →₀ β)) with }

instance [NonUnitalSemiringₓ β] : NonUnitalSemiringₓ (α →₀ β) :=
  { (inferInstance : Semigroupₓ (α →₀ β)), (inferInstance : NonUnitalNonAssocSemiringₓ (α →₀ β)) with }

instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  { (inferInstance : NonUnitalNonAssocSemiringₓ (α →₀ β)), (inferInstance : AddCommGroupₓ (α →₀ β)) with }

instance [NonUnitalRing β] : NonUnitalRing (α →₀ β) :=
  { (inferInstance : NonUnitalSemiringₓ (α →₀ β)), (inferInstance : AddCommGroupₓ (α →₀ β)) with }

-- TODO can this be generalized in the direction of `pi.has_scalar'`
-- (i.e. dependent functions and finsupps)
-- TODO in theory this could be generalised, we only really need `smul_zero` for the definition
instance pointwiseScalar [Semiringₓ β] : HasScalar (α → β) (α →₀ β) where
  smul := fun f g =>
    Finsupp.ofSupportFinite (fun a => f a • g a)
      (by
        apply Set.Finite.subset g.finite_support
        simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne.def, Finsupp.fun_support_eq, Finset.mem_coe]
        intro x hx h
        apply hx
        rw [h, smul_zero])

@[simp]
theorem coe_pointwise_smul [Semiringₓ β] (f : α → β) (g : α →₀ β) : ⇑(f • g) = f • g :=
  rfl

/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwiseModule [Semiringₓ β] : Module (α → β) (α →₀ β) :=
  Function.Injective.module _ coeFnAddHom coe_fn_injective coe_pointwise_smul

end Finsupp

