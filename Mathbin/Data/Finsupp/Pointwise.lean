/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module data.finsupp.pointwise
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Defs
import Mathbin.Algebra.Ring.Pi

/-!
# The pointwise product on `finsupp`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

/- warning: finsupp.coe_mul -> Finsupp.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] (g₁ : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (g₂ : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (instHMul.{max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.hasMul.{u1, u2} α β _inst_1)) g₁ g₂)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β _inst_1))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) g₁) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] (g₁ : Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (g₂ : Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) _x) (Finsupp.funLike.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (instHMul.{max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.instMulFinsuppToZero.{u1, u2} α β _inst_1)) g₁ g₂)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) ᾰ) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) ᾰ) (instHMul.{max u1 u2} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) ᾰ) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) ᾰ) (fun (i : α) => MulZeroClass.toMul.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) i) _inst_1))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) _x) (Finsupp.funLike.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) g₁) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) _x) (Finsupp.funLike.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) g₂))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_mul Finsupp.coe_mulₓ'. -/
theorem coe_mul (g₁ g₂ : α →₀ β) : ⇑(g₁ * g₂) = g₁ * g₂ :=
  rfl
#align finsupp.coe_mul Finsupp.coe_mul

/- warning: finsupp.mul_apply -> Finsupp.mul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] {g₁ : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)} {g₂ : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)} {a : α}, Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (instHMul.{max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.hasMul.{u1, u2} α β _inst_1)) g₁ g₂) a) (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β (MulZeroClass.toHasMul.{u2} β _inst_1)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) g₁ a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) g₂ a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] {g₁ : Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)} {g₂ : Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)} {a : α}, Eq.{succ u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) _x) (Finsupp.funLike.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (instHMul.{max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.instMulFinsuppToZero.{u1, u2} α β _inst_1)) g₁ g₂) a) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) (instHMul.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) (MulZeroClass.toMul.{u2} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) _inst_1)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) _x) (Finsupp.funLike.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) g₁ a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) _x) (Finsupp.funLike.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) g₂ a))
Case conversion may be inaccurate. Consider using '#align finsupp.mul_apply Finsupp.mul_applyₓ'. -/
@[simp]
theorem mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
  rfl
#align finsupp.mul_apply Finsupp.mul_apply

/- warning: finsupp.support_mul -> Finsupp.support_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {g₁ : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)} {g₂ : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finsupp.support.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (instHMul.{max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1)) (Finsupp.hasMul.{u1, u2} α β _inst_1)) g₁ g₂)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finsupp.support.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1) g₁) (Finsupp.support.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β _inst_1) g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MulZeroClass.{u2} β] [_inst_2 : DecidableEq.{succ u1} α] {g₁ : Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)} {g₂ : Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (Finsupp.support.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (instHMul.{max u1 u2} (Finsupp.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1)) (Finsupp.instMulFinsuppToZero.{u1, u2} α β _inst_1)) g₁ g₂)) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finsupp.support.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1) g₁) (Finsupp.support.{u1, u2} α β (MulZeroClass.toZero.{u2} β _inst_1) g₂))
Case conversion may be inaccurate. Consider using '#align finsupp.support_mul Finsupp.support_mulₓ'. -/
theorem support_mul [DecidableEq α] {g₁ g₂ : α →₀ β} :
    (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support :=
  by
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
  Finsupp.coeFn_injective.MulZeroClass _ coe_zero coe_mul

end

instance [SemigroupWithZero β] : SemigroupWithZero (α →₀ β) :=
  Finsupp.coeFn_injective.SemigroupWithZero _ coe_zero coe_mul

instance [NonUnitalNonAssocSemiring β] : NonUnitalNonAssocSemiring (α →₀ β) :=
  Finsupp.coeFn_injective.NonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalSemiring β] : NonUnitalSemiring (α →₀ β) :=
  Finsupp.coeFn_injective.NonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalCommSemiring β] : NonUnitalCommSemiring (α →₀ β) :=
  Finsupp.coeFn_injective.NonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing (α →₀ β) :=
  Finsupp.coeFn_injective.NonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalRing β] : NonUnitalRing (α →₀ β) :=
  Finsupp.coeFn_injective.NonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

instance [NonUnitalCommRing β] : NonUnitalCommRing (α →₀ β) :=
  Finsupp.coeFn_injective.NonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

/- warning: finsupp.pointwise_scalar -> Finsupp.pointwiseScalar is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u2} β], SMul.{max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u2} β], SMul.{max u1 u2, max u2 u1} (α -> β) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.pointwise_scalar Finsupp.pointwiseScalarₓ'. -/
-- TODO can this be generalized in the direction of `pi.has_smul'`
-- (i.e. dependent functions and finsupps)
-- TODO in theory this could be generalised, we only really need `smul_zero` for the definition
instance pointwiseScalar [Semiring β] : SMul (α → β) (α →₀ β)
    where smul f g :=
    Finsupp.ofSupportFinite (fun a => f a • g a)
      (by
        apply Set.Finite.subset g.finite_support
        simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne.def,
          Finsupp.fun_support_eq, Finset.mem_coe]
        intro x hx h
        apply hx
        rw [h, smul_zero])
#align finsupp.pointwise_scalar Finsupp.pointwiseScalar

/- warning: finsupp.coe_pointwise_smul -> Finsupp.coe_pointwise_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u2} β] (f : α -> β) (g : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))), Eq.{succ (max u1 u2)} (α -> β) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) (SMul.smul.{max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) (Finsupp.pointwiseScalar.{u1, u2} α β _inst_1) f g)) (SMul.smul.{max u1 u2, max u1 u2} (α -> β) (α -> β) (Pi.smul'.{u1, u2, u2} α (fun (ᾰ : α) => β) (fun (ᾰ : α) => β) (fun (i : α) => Mul.toSMul.{u2} β (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1)))))) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) (fun (_x : Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) => α -> β) (Finsupp.hasCoeToFun.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u2} β] (f : α -> β) (g : Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))), Eq.{max (succ u1) (succ u2)} (α -> β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) α (fun (_x : α) => β) (Finsupp.funLike.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (HSMul.hSMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (instHSMul.{max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (Finsupp.pointwiseScalar.{u1, u2} α β _inst_1)) f g)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => β) a) (Finsupp.funLike.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (HSMul.hSMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (instHSMul.{max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (Finsupp.pointwiseScalar.{u1, u2} α β _inst_1)) f g))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_pointwise_smul Finsupp.coe_pointwise_smulₓ'. -/
@[simp]
theorem coe_pointwise_smul [Semiring β] (f : α → β) (g : α →₀ β) : ⇑(f • g) = f • g :=
  rfl
#align finsupp.coe_pointwise_smul Finsupp.coe_pointwise_smul

/- warning: finsupp.pointwise_module -> Finsupp.pointwiseModule is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u2} β], Module.{max u1 u2, max u1 u2} (α -> β) (Finsupp.{u1, u2} α β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))) (Pi.semiring.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_1)) (Finsupp.addCommMonoid.{u1, u2} α β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Semiring.{u2} β], Module.{max u1 u2, max u2 u1} (α -> β) (Finsupp.{u1, u2} α β (MonoidWithZero.toZero.{u2} β (Semiring.toMonoidWithZero.{u2} β _inst_1))) (Pi.semiring.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_1)) (Finsupp.addCommMonoid.{u1, u2} α β (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.pointwise_module Finsupp.pointwiseModuleₓ'. -/
/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwiseModule [Semiring β] : Module (α → β) (α →₀ β) :=
  Function.Injective.module _ coeFnAddHom coeFn_injective coe_pointwise_smul
#align finsupp.pointwise_module Finsupp.pointwiseModule

end Finsupp

