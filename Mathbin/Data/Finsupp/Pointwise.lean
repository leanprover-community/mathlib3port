import Mathbin.Data.Finsupp.Basic

/-!
# The pointwise product on `finsupp`.

For the convolution product on `finsupp` when the domain has a binary operation,
see the type synonyms `add_monoid_algebra`
(which is in turn used to define `polynomial` and `mv_polynomial`)
and `monoid_algebra`.
-/


noncomputable theory

open_locale Classical

open Finset

universe u₁ u₂ u₃ u₄ u₅

variable{α : Type u₁}{β : Type u₂}{γ : Type u₃}{δ : Type u₄}{ι : Type u₅}

namespace Finsupp

/-! ### Declarations about the pointwise product on `finsupp`s -/


section 

variable[MulZeroClass β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance  : Mul (α →₀ β) :=
  ⟨zip_with (·*·) (mul_zero 0)⟩

@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁*g₂) a = g₁ a*g₂ a :=
  rfl

theorem support_mul {g₁ g₂ : α →₀ β} : (g₁*g₂).Support ⊆ g₁.support ∩ g₂.support :=
  by 
    intro a h 
    simp only [mul_apply, mem_support_iff] at h 
    simp only [mem_support_iff, mem_inter, Ne.def]
    rw [←not_or_distrib]
    intro w 
    apply h 
    cases w <;>
      ·
        rw [w]
        simp 

instance  : MulZeroClass (α →₀ β) :=
  { zero := 0, mul := ·*·,
    mul_zero :=
      fun f =>
        by 
          ext 
          simp only [mul_apply, zero_apply, mul_zero],
    zero_mul :=
      fun f =>
        by 
          ext 
          simp only [mul_apply, zero_apply, zero_mul] }

end 

instance  [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  { (inferInstance : MulZeroClass (α →₀ β)) with mul := ·*·,
    mul_assoc :=
      fun f g h =>
        by 
          ext 
          simp only [mul_apply, mul_assocₓ] }

-- error in Data.Finsupp.Pointwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance [non_unital_non_assoc_semiring β] : non_unital_non_assoc_semiring «expr →₀ »(α, β) :=
{ left_distrib := λ f g h, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr mul_apply, ",", expr add_apply, ",", expr left_distrib, "]"] [] [] { proj := ff } },
  right_distrib := λ f g h, by { ext [] [] [],
    simp [] [] ["only"] ["[", expr mul_apply, ",", expr add_apply, ",", expr right_distrib, "]"] [] [] { proj := ff } },
  ..(infer_instance : mul_zero_class «expr →₀ »(α, β)),
  ..(infer_instance : add_comm_monoid «expr →₀ »(α, β)) }

instance  [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  { (inferInstance : Semigroupₓ (α →₀ β)), (inferInstance : NonUnitalNonAssocSemiring (α →₀ β)) with  }

end Finsupp

