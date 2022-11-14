/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Finsupp.Defs

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
  ⟨zipWith (· * ·) (mul_zero 0)⟩

protected theorem coe_mul (g₁ g₂ : α →₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl
#align finsupp.coe_mul Finsupp.coe_mul

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl
#align finsupp.mul_apply Finsupp.mul_apply

theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} : (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support := by
  intro a h
  simp only [mul_apply, mem_support_iff] at h
  simp only [mem_support_iff, mem_inter, Ne.def]
  rw [← not_or]
  intro w
  apply h
  cases w <;>
    · rw [w]
      simp
      
#align finsupp.support_mul Finsupp.support_mul

instance : MulZeroClass (α →₀ β) :=
  Finsupp.coe_fn_injective.MulZeroClass _ Finsupp.coe_zero Finsupp.coe_mul

end

instance [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  Finsupp.coe_fn_injective.SemigroupWithZero _ Finsupp.coe_zero Finsupp.coe_mul

instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →₀ β) :=
  Finsupp.coe_fn_injective.NonUnitalNonAssocSemiring _ Finsupp.coe_zero Finsupp.coe_add Finsupp.coe_mul fun _ _ => rfl

instance [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  Finsupp.coe_fn_injective.NonUnitalSemiring _ Finsupp.coe_zero Finsupp.coe_add Finsupp.coe_mul fun _ _ => rfl

instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →₀ β) :=
  Finsupp.coe_fn_injective.NonUnitalCommSemiring _ Finsupp.coe_zero Finsupp.coe_add Finsupp.coe_mul fun _ _ => rfl

instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  Finsupp.coe_fn_injective.NonUnitalNonAssocRing _ Finsupp.coe_zero Finsupp.coe_add Finsupp.coe_mul Finsupp.coe_neg
    Finsupp.coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalRing β] : NonUnitalRing (α →₀ β) :=
  Finsupp.coe_fn_injective.NonUnitalRing _ Finsupp.coe_zero Finsupp.coe_add Finsupp.coe_mul Finsupp.coe_neg
    Finsupp.coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalCommRing β] : NonUnitalCommRing (α →₀ β) :=
  Finsupp.coe_fn_injective.NonUnitalCommRing _ Finsupp.coe_zero Finsupp.coe_add Finsupp.coe_mul Finsupp.coe_neg
    Finsupp.coe_sub (fun _ _ => rfl) fun _ _ => rfl

-- TODO can this be generalized in the direction of `pi.has_smul'`
-- (i.e. dependent functions and finsupps)
-- TODO in theory this could be generalised, we only really need `smul_zero` for the definition
instance pointwiseScalar [Semiring β] :
    HasSmul (α → β) (α →₀ β) where smul f g :=
    Finsupp.ofSupportFinite (fun a => f a • g a)
      (by
        apply Set.Finite.subset g.finite_support
        simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne.def, Finsupp.fun_support_eq, Finset.mem_coe]
        intro x hx h
        apply hx
        rw [h, smul_zero])
#align finsupp.pointwise_scalar Finsupp.pointwiseScalar

@[simp]
theorem coe_pointwise_smul [Semiring β] (f : α → β) (g : α →₀ β) : ⇑(f • g) = f • g :=
  rfl
#align finsupp.coe_pointwise_smul Finsupp.coe_pointwise_smul

/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwiseModule [Semiring β] : Module (α → β) (α →₀ β) :=
  Function.Injective.module _ coeFnAddHom coe_fn_injective coe_pointwise_smul
#align finsupp.pointwise_module Finsupp.pointwiseModule

end Finsupp

