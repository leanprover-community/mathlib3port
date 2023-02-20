/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser

! This file was ported from Lean 3 source module data.pi.algebra
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.ToAdditive
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Unique
import Mathbin.Tactic.Congr
import Mathbin.Tactic.Simpa
import Mathbin.Tactic.SplitIfs
import Mathbin.Data.Sum.Basic
import Mathbin.Data.Prod.Basic

/-!
# Instances and theorems on pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/


open Function

universe u v₁ v₂ v₃

variable {I : Type u}

-- The indexing type
variable {α β γ : Type _}

-- The families of types already equipped with instances
variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/


#print Pi.instOne /-
@[to_additive]
instance instOne [∀ i, One <| f i] : One (∀ i : I, f i) :=
  ⟨fun _ => 1⟩
#align pi.has_one Pi.instOne
#align pi.has_zero Pi.instZero
-/

#print Pi.one_apply /-
@[simp, to_additive]
theorem one_apply [∀ i, One <| f i] : (1 : ∀ i, f i) i = 1 :=
  rfl
#align pi.one_apply Pi.one_apply
#align pi.zero_apply Pi.zero_apply
-/

#print Pi.one_def /-
@[to_additive]
theorem one_def [∀ i, One <| f i] : (1 : ∀ i, f i) = fun i => 1 :=
  rfl
#align pi.one_def Pi.one_def
#align pi.zero_def Pi.zero_def
-/

#print Pi.const_one /-
@[simp, to_additive]
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl
#align pi.const_one Pi.const_one
#align pi.const_zero Pi.const_zero
-/

/- warning: pi.one_comp -> Pi.one_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : One.{u3} γ] (x : α -> β), Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ (OfNat.ofNat.{max u2 u3} (β -> γ) 1 (OfNat.mk.{max u2 u3} (β -> γ) 1 (One.one.{max u2 u3} (β -> γ) (Pi.instOne.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))))) x) (OfNat.ofNat.{max u1 u3} (α -> γ) 1 (OfNat.mk.{max u1 u3} (α -> γ) 1 (One.one.{max u1 u3} (α -> γ) (Pi.instOne.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : One.{u3} γ] (x : α -> β), Eq.{max (succ u2) (succ u3)} (α -> γ) (Function.comp.{succ u2, succ u1, succ u3} α β γ (OfNat.ofNat.{max u1 u3} (β -> γ) 1 (One.toOfNat1.{max u1 u3} (β -> γ) (Pi.instOne.{u1, u3} β (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.301 : β) => γ) (fun (i : β) => _inst_1)))) x) (OfNat.ofNat.{max u2 u3} (α -> γ) 1 (One.toOfNat1.{max u2 u3} (α -> γ) (Pi.instOne.{u2, u3} α (fun (a._@.Init.Prelude._hyg.25 : α) => γ) (fun (i : α) => _inst_1))))
Case conversion may be inaccurate. Consider using '#align pi.one_comp Pi.one_compₓ'. -/
@[simp, to_additive]
theorem one_comp [One γ] (x : α → β) : (1 : β → γ) ∘ x = 1 :=
  rfl
#align pi.one_comp Pi.one_comp
#align pi.zero_comp Pi.zero_comp

/- warning: pi.comp_one -> Pi.comp_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : One.{u2} β] (x : β -> γ), Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ x (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_1)))))) (Function.const.{succ u3, succ u1} γ α (x (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_1 : One.{u3} β] (x : β -> γ), Eq.{max (succ u2) (succ u1)} (α -> γ) (Function.comp.{succ u2, succ u3, succ u1} α β γ x (OfNat.ofNat.{max u2 u3} (α -> β) 1 (One.toOfNat1.{max u2 u3} (α -> β) (Pi.instOne.{u2, u3} α (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.349 : α) => β) (fun (i : α) => _inst_1))))) (Function.const.{succ u1, succ u2} γ α (x (OfNat.ofNat.{u3} β 1 (One.toOfNat1.{u3} β _inst_1))))
Case conversion may be inaccurate. Consider using '#align pi.comp_one Pi.comp_oneₓ'. -/
@[simp, to_additive]
theorem comp_one [One β] (x : β → γ) : x ∘ 1 = const α (x 1) :=
  rfl
#align pi.comp_one Pi.comp_one
#align pi.comp_zero Pi.comp_zero

#print Pi.instMul /-
@[to_additive]
instance instMul [∀ i, Mul <| f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i * g i⟩
#align pi.has_mul Pi.instMul
#align pi.has_add Pi.instAdd
-/

#print Pi.mul_apply /-
@[simp, to_additive]
theorem mul_apply [∀ i, Mul <| f i] : (x * y) i = x i * y i :=
  rfl
#align pi.mul_apply Pi.mul_apply
#align pi.add_apply Pi.add_apply
-/

#print Pi.mul_def /-
@[to_additive]
theorem mul_def [∀ i, Mul <| f i] : x * y = fun i => x i * y i :=
  rfl
#align pi.mul_def Pi.mul_def
#align pi.add_def Pi.add_def
-/

#print Pi.const_mul /-
@[simp, to_additive]
theorem const_mul [Mul β] (a b : β) : const α a * const α b = const α (a * b) :=
  rfl
#align pi.const_mul Pi.const_mul
#align pi.const_add Pi.const_add
-/

/- warning: pi.mul_comp -> Pi.mul_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Mul.{u3} γ] (x : β -> γ) (y : β -> γ) (z : α -> β), Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (β -> γ) (β -> γ) (β -> γ) (instHMul.{max u2 u3} (β -> γ) (Pi.instMul.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) x y) z) (HMul.hMul.{max u1 u3, max u1 u3, max u1 u3} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u1 u3} (α -> γ) (Pi.instMul.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) (Function.comp.{succ u1, succ u2, succ u3} α β γ x z) (Function.comp.{succ u1, succ u2, succ u3} α β γ y z))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : Mul.{u3} γ] (x : β -> γ) (y : β -> γ) (z : α -> β), Eq.{max (succ u2) (succ u3)} (α -> γ) (Function.comp.{succ u2, succ u1, succ u3} α β γ (HMul.hMul.{max u1 u3, max u1 u3, max u1 u3} (β -> γ) (β -> γ) (β -> γ) (instHMul.{max u1 u3} (β -> γ) (Pi.instMul.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) x y) z) (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u2 u3} (α -> γ) (Pi.instMul.{u2, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) (Function.comp.{succ u2, succ u1, succ u3} α β γ x z) (Function.comp.{succ u2, succ u1, succ u3} α β γ y z))
Case conversion may be inaccurate. Consider using '#align pi.mul_comp Pi.mul_compₓ'. -/
@[to_additive]
theorem mul_comp [Mul γ] (x y : β → γ) (z : α → β) : (x * y) ∘ z = x ∘ z * y ∘ z :=
  rfl
#align pi.mul_comp Pi.mul_comp
#align pi.add_comp Pi.add_comp

#print Pi.instSMul /-
@[to_additive Pi.instVAdd]
instance instSMul [∀ i, SMul α <| f i] : SMul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩
#align pi.has_smul Pi.instSMul
#align pi.has_vadd Pi.instVAdd
-/

/- warning: pi.smul_apply -> Pi.smul_apply is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u3}} {f : I -> Type.{u2}} [_inst_1 : forall (i : I), SMul.{u3, u2} α (f i)] (s : α) (x : forall (i : I), f i) (i : I), Eq.{succ u2} (f i) (SMul.smul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i)) s x i) (SMul.smul.{u3, u2} α (f i) (_inst_1 i) s (x i))
but is expected to have type
  forall {I : Type.{u2}} {α : Type.{u1}} {f : I -> Type.{u3}} [_inst_1 : forall (i : I), SMul.{u1, u3} α (f i)] (s : α) (x : forall (i : I), f i) (i : I), Eq.{succ u3} (f i) (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (i : I), f i) (forall (i : I), f i) (instHSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) s x i) (HSMul.hSMul.{u1, u3, u3} α (f i) (f i) (instHSMul.{u1, u3} α (f i) (_inst_1 i)) s (x i))
Case conversion may be inaccurate. Consider using '#align pi.smul_apply Pi.smul_applyₓ'. -/
@[simp, to_additive]
theorem smul_apply [∀ i, SMul α <| f i] (s : α) (x : ∀ i, f i) (i : I) : (s • x) i = s • x i :=
  rfl
#align pi.smul_apply Pi.smul_apply
#align pi.vadd_apply Pi.vadd_apply

/- warning: pi.smul_def -> Pi.smul_def is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u3}} {f : I -> Type.{u2}} [_inst_1 : forall (i : I), SMul.{u3, u2} α (f i)] (s : α) (x : forall (i : I), f i), Eq.{succ (max u1 u2)} (forall (i : I), f i) (SMul.smul.{u3, max u1 u2} α (forall (i : I), f i) (Pi.instSMul.{u1, u2, u3} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i)) s x) (fun (i : I) => SMul.smul.{u3, u2} α (f i) (_inst_1 i) s (x i))
but is expected to have type
  forall {I : Type.{u2}} {α : Type.{u1}} {f : I -> Type.{u3}} [_inst_1 : forall (i : I), SMul.{u1, u3} α (f i)] (s : α) (x : forall (i : I), f i), Eq.{max (succ u2) (succ u3)} (forall (i : I), f i) (HSMul.hSMul.{u1, max u2 u3, max u2 u3} α (forall (i : I), f i) (forall (i : I), f i) (instHSMul.{u1, max u2 u3} α (forall (i : I), f i) (Pi.instSMul.{u2, u3, u1} I α (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) s x) (fun (i : I) => HSMul.hSMul.{u1, u3, u3} α (f i) (f i) (instHSMul.{u1, u3} α (f i) (_inst_1 i)) s (x i))
Case conversion may be inaccurate. Consider using '#align pi.smul_def Pi.smul_defₓ'. -/
@[to_additive]
theorem smul_def [∀ i, SMul α <| f i] (s : α) (x : ∀ i, f i) : s • x = fun i => s • x i :=
  rfl
#align pi.smul_def Pi.smul_def
#align pi.vadd_def Pi.vadd_def

/- warning: pi.smul_const -> Pi.smul_const is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : SMul.{u2, u3} α β] (a : α) (b : β), Eq.{succ (max u1 u3)} (I -> β) (SMul.smul.{u2, max u1 u3} α (I -> β) (Pi.instSMul.{u1, u3, u2} I α (fun (ᾰ : I) => β) (fun (i : I) => _inst_1)) a (Function.const.{succ u3, succ u1} β I b)) (Function.const.{succ u3, succ u1} β I (SMul.smul.{u2, u3} α β _inst_1 a b))
but is expected to have type
  forall {I : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (b : β), Eq.{max (succ u3) (succ u2)} (I -> β) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} α (I -> β) (I -> β) (instHSMul.{u1, max u3 u2} α (I -> β) (Pi.instSMul.{u3, u2, u1} I α (fun (a._@.Init.Prelude._hyg.54 : I) => β) (fun (i : I) => _inst_1))) a (Function.const.{succ u2, succ u3} β I b)) (Function.const.{succ u2, succ u3} β I (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β _inst_1) a b))
Case conversion may be inaccurate. Consider using '#align pi.smul_const Pi.smul_constₓ'. -/
@[simp, to_additive]
theorem smul_const [SMul α β] (a : α) (b : β) : a • const I b = const I (a • b) :=
  rfl
#align pi.smul_const Pi.smul_const
#align pi.vadd_const Pi.vadd_const

/- warning: pi.smul_comp -> Pi.smul_comp is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : SMul.{u2, u4} α γ] (a : α) (x : β -> γ) (y : I -> β), Eq.{max (succ u1) (succ u4)} (I -> γ) (Function.comp.{succ u1, succ u3, succ u4} I β γ (SMul.smul.{u2, max u3 u4} α (β -> γ) (Pi.instSMul.{u3, u4, u2} β α (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1)) a x) y) (SMul.smul.{u2, max u1 u4} α (I -> γ) (Pi.instSMul.{u1, u4, u2} I α (fun (ᾰ : I) => γ) (fun (i : I) => _inst_1)) a (Function.comp.{succ u1, succ u3, succ u4} I β γ x y))
but is expected to have type
  forall {I : Type.{u4}} {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : SMul.{u2, u3} α γ] (a : α) (x : β -> γ) (y : I -> β), Eq.{max (succ u4) (succ u3)} (I -> γ) (Function.comp.{succ u4, succ u1, succ u3} I β γ (HSMul.hSMul.{u2, max u1 u3, max u1 u3} α (β -> γ) (β -> γ) (instHSMul.{u2, max u1 u3} α (β -> γ) (Pi.instSMul.{u1, u3, u2} β α (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.1026 : β) => γ) (fun (i : β) => _inst_1))) a x) y) (HSMul.hSMul.{u2, max u4 u3, max u4 u3} α (I -> γ) (I -> γ) (instHSMul.{u2, max u4 u3} α (I -> γ) (Pi.instSMul.{u4, u3, u2} I α (fun (a._@.Init.Prelude._hyg.25 : I) => γ) (fun (i : I) => _inst_1))) a (Function.comp.{succ u4, succ u1, succ u3} I β γ x y))
Case conversion may be inaccurate. Consider using '#align pi.smul_comp Pi.smul_compₓ'. -/
@[to_additive]
theorem smul_comp [SMul α γ] (a : α) (x : β → γ) (y : I → β) : (a • x) ∘ y = a • x ∘ y :=
  rfl
#align pi.smul_comp Pi.smul_comp
#align pi.vadd_comp Pi.vadd_comp

@[to_additive Pi.instSMul]
instance hasPow [∀ i, Pow (f i) β] : Pow (∀ i, f i) β :=
  ⟨fun x b i => x i ^ b⟩
#align pi.has_pow Pi.hasPow
#align pi.has_smul Pi.instSMul

/- warning: pi.pow_apply -> Pi.pow_apply is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {β : Type.{u3}} {f : I -> Type.{u2}} [_inst_1 : forall (i : I), Pow.{u2, u3} (f i) β] (x : forall (i : I), f i) (b : β) (i : I), Eq.{succ u2} (f i) (HPow.hPow.{max u1 u2, u3, max u1 u2} (forall (i : I), f i) β (forall (i : I), f i) (instHPow.{max u1 u2, u3} (forall (i : I), f i) β (Pi.hasPow.{u1, u2, u3} I β (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) x b i) (HPow.hPow.{u2, u3, u2} (f i) β (f i) (instHPow.{u2, u3} (f i) β (_inst_1 i)) (x i) b)
but is expected to have type
  forall {I : Type.{u2}} {β : Type.{u1}} {f : I -> Type.{u3}} [_inst_1 : forall (i : I), Pow.{u3, u1} (f i) β] (x : forall (i : I), f i) (b : β) (i : I), Eq.{succ u3} (f i) (HPow.hPow.{max u2 u3, u1, max u2 u3} (forall (i : I), f i) β (forall (i : I), f i) (instHPow.{max u2 u3, u1} (forall (i : I), f i) β (Pi.instPow.{u2, u3, u1} I β (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) x b i) (HPow.hPow.{u3, u1, u3} (f i) β (f i) (instHPow.{u3, u1} (f i) β (_inst_1 i)) (x i) b)
Case conversion may be inaccurate. Consider using '#align pi.pow_apply Pi.pow_applyₓ'. -/
@[simp, to_additive Pi.smul_apply, to_additive_reorder 5]
theorem pow_apply [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) (i : I) : (x ^ b) i = x i ^ b :=
  rfl
#align pi.pow_apply Pi.pow_apply
#align pi.smul_apply Pi.smul_apply

/- warning: pi.pow_def -> Pi.pow_def is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {β : Type.{u3}} {f : I -> Type.{u2}} [_inst_1 : forall (i : I), Pow.{u2, u3} (f i) β] (x : forall (i : I), f i) (b : β), Eq.{succ (max u1 u2)} (forall (i : I), f i) (HPow.hPow.{max u1 u2, u3, max u1 u2} (forall (i : I), f i) β (forall (i : I), f i) (instHPow.{max u1 u2, u3} (forall (i : I), f i) β (Pi.hasPow.{u1, u2, u3} I β (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) x b) (fun (i : I) => HPow.hPow.{u2, u3, u2} (f i) β (f i) (instHPow.{u2, u3} (f i) β (_inst_1 i)) (x i) b)
but is expected to have type
  forall {I : Type.{u2}} {β : Type.{u1}} {f : I -> Type.{u3}} [_inst_1 : forall (i : I), Pow.{u3, u1} (f i) β] (x : forall (i : I), f i) (b : β), Eq.{max (succ u2) (succ u3)} (forall (i : I), f i) (HPow.hPow.{max u2 u3, u1, max u2 u3} (forall (i : I), f i) β (forall (i : I), f i) (instHPow.{max u2 u3, u1} (forall (i : I), f i) β (Pi.instPow.{u2, u3, u1} I β (fun (i : I) => f i) (fun (i : I) => _inst_1 i))) x b) (fun (i : I) => HPow.hPow.{u3, u1, u3} (f i) β (f i) (instHPow.{u3, u1} (f i) β (_inst_1 i)) (x i) b)
Case conversion may be inaccurate. Consider using '#align pi.pow_def Pi.pow_defₓ'. -/
@[to_additive Pi.smul_def, to_additive_reorder 5]
theorem pow_def [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) : x ^ b = fun i => x i ^ b :=
  rfl
#align pi.pow_def Pi.pow_def
#align pi.smul_def Pi.smul_def

/- warning: pi.const_pow -> Pi.const_pow is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Pow.{u3, u2} β α] (b : β) (a : α), Eq.{succ (max u1 u3)} (I -> β) (HPow.hPow.{max u1 u3, u2, max u1 u3} (I -> β) α (I -> β) (instHPow.{max u1 u3, u2} (I -> β) α (Pi.hasPow.{u1, u3, u2} I α (fun (ᾰ : I) => β) (fun (i : I) => _inst_1))) (Function.const.{succ u3, succ u1} β I b) a) (Function.const.{succ u3, succ u1} β I (HPow.hPow.{u3, u2, u3} β α β (instHPow.{u3, u2} β α _inst_1) b a))
but is expected to have type
  forall {I : Type.{u3}} {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Pow.{u2, u1} α β] (b : α) (a : β), Eq.{max (succ u3) (succ u2)} (I -> α) (HPow.hPow.{max u3 u2, u1, max u3 u2} (I -> α) β (I -> α) (instHPow.{max u3 u2, u1} (I -> α) β (Pi.instPow.{u3, u2, u1} I β (fun (ᾰ : I) => α) (fun (i : I) => _inst_1))) (Function.const.{succ u2, succ u3} α I b) a) (Function.const.{succ u2, succ u3} α I (HPow.hPow.{u2, u1, u2} α β α (instHPow.{u2, u1} α β _inst_1) b a))
Case conversion may be inaccurate. Consider using '#align pi.const_pow Pi.const_powₓ'. -/
-- `to_additive` generates bad output if we take `has_pow α β`.
@[simp, to_additive smul_const, to_additive_reorder 5]
theorem const_pow [Pow β α] (b : β) (a : α) : const I b ^ a = const I (b ^ a) :=
  rfl
#align pi.const_pow Pi.const_pow
#align pi.smul_const Pi.smul_const

/- warning: pi.pow_comp -> Pi.pow_comp is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} [_inst_1 : Pow.{u4, u2} γ α] (x : β -> γ) (a : α) (y : I -> β), Eq.{max (succ u1) (succ u4)} (I -> γ) (Function.comp.{succ u1, succ u3, succ u4} I β γ (HPow.hPow.{max u3 u4, u2, max u3 u4} (β -> γ) α (β -> γ) (instHPow.{max u3 u4, u2} (β -> γ) α (Pi.hasPow.{u3, u4, u2} β α (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) x a) y) (HPow.hPow.{max u1 u4, u2, max u1 u4} (I -> γ) α (I -> γ) (instHPow.{max u1 u4, u2} (I -> γ) α (Pi.hasPow.{u1, u4, u2} I α (fun (ᾰ : I) => γ) (fun (i : I) => _inst_1))) (Function.comp.{succ u1, succ u3, succ u4} I β γ x y) a)
but is expected to have type
  forall {I : Type.{u4}} {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : Pow.{u3, u2} γ α] (x : β -> γ) (a : α) (y : I -> β), Eq.{max (succ u4) (succ u3)} (I -> γ) (Function.comp.{succ u4, succ u1, succ u3} I β γ (HPow.hPow.{max u1 u3, u2, max u1 u3} (β -> γ) α (β -> γ) (instHPow.{max u1 u3, u2} (β -> γ) α (Pi.instPow.{u1, u3, u2} β α (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) x a) y) (HPow.hPow.{max u4 u3, u2, max u4 u3} (I -> γ) α (I -> γ) (instHPow.{max u4 u3, u2} (I -> γ) α (Pi.instPow.{u4, u3, u2} I α (fun (ᾰ : I) => γ) (fun (i : I) => _inst_1))) (Function.comp.{succ u4, succ u1, succ u3} I β γ x y) a)
Case conversion may be inaccurate. Consider using '#align pi.pow_comp Pi.pow_compₓ'. -/
@[to_additive smul_comp, to_additive_reorder 6]
theorem pow_comp [Pow γ α] (x : β → γ) (a : α) (y : I → β) : (x ^ a) ∘ y = x ∘ y ^ a :=
  rfl
#align pi.pow_comp Pi.pow_comp
#align pi.smul_comp Pi.smul_comp

#print Pi.bit0_apply /-
@[simp]
theorem bit0_apply [∀ i, Add <| f i] : (bit0 x) i = bit0 (x i) :=
  rfl
#align pi.bit0_apply Pi.bit0_apply
-/

#print Pi.bit1_apply /-
@[simp]
theorem bit1_apply [∀ i, Add <| f i] [∀ i, One <| f i] : (bit1 x) i = bit1 (x i) :=
  rfl
#align pi.bit1_apply Pi.bit1_apply
-/

#print Pi.instInv /-
@[to_additive]
instance instInv [∀ i, Inv <| f i] : Inv (∀ i : I, f i) :=
  ⟨fun f i => (f i)⁻¹⟩
#align pi.has_inv Pi.instInv
#align pi.has_neg Pi.instNeg
-/

#print Pi.inv_apply /-
@[simp, to_additive]
theorem inv_apply [∀ i, Inv <| f i] : x⁻¹ i = (x i)⁻¹ :=
  rfl
#align pi.inv_apply Pi.inv_apply
#align pi.neg_apply Pi.neg_apply
-/

#print Pi.inv_def /-
@[to_additive]
theorem inv_def [∀ i, Inv <| f i] : x⁻¹ = fun i => (x i)⁻¹ :=
  rfl
#align pi.inv_def Pi.inv_def
#align pi.neg_def Pi.neg_def
-/

#print Pi.const_inv /-
@[to_additive]
theorem const_inv [Inv β] (a : β) : (const α a)⁻¹ = const α a⁻¹ :=
  rfl
#align pi.const_inv Pi.const_inv
#align pi.const_neg Pi.const_neg
-/

/- warning: pi.inv_comp -> Pi.inv_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Inv.{u3} γ] (x : β -> γ) (y : α -> β), Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ (Inv.inv.{max u2 u3} (β -> γ) (Pi.instInv.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1)) x) y) (Inv.inv.{max u1 u3} (α -> γ) (Pi.instInv.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1)) (Function.comp.{succ u1, succ u2, succ u3} α β γ x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : Inv.{u3} γ] (x : β -> γ) (y : α -> β), Eq.{max (succ u2) (succ u3)} (α -> γ) (Function.comp.{succ u2, succ u1, succ u3} α β γ (Inv.inv.{max u1 u3} (β -> γ) (Pi.instInv.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1)) x) y) (Inv.inv.{max u2 u3} (α -> γ) (Pi.instInv.{u2, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1)) (Function.comp.{succ u2, succ u1, succ u3} α β γ x y))
Case conversion may be inaccurate. Consider using '#align pi.inv_comp Pi.inv_compₓ'. -/
@[to_additive]
theorem inv_comp [Inv γ] (x : β → γ) (y : α → β) : x⁻¹ ∘ y = (x ∘ y)⁻¹ :=
  rfl
#align pi.inv_comp Pi.inv_comp
#align pi.neg_comp Pi.neg_comp

#print Pi.instDiv /-
@[to_additive]
instance instDiv [∀ i, Div <| f i] : Div (∀ i : I, f i) :=
  ⟨fun f g i => f i / g i⟩
#align pi.has_div Pi.instDiv
#align pi.has_sub Pi.instSub
-/

#print Pi.div_apply /-
@[simp, to_additive]
theorem div_apply [∀ i, Div <| f i] : (x / y) i = x i / y i :=
  rfl
#align pi.div_apply Pi.div_apply
#align pi.sub_apply Pi.sub_apply
-/

#print Pi.div_def /-
@[to_additive]
theorem div_def [∀ i, Div <| f i] : x / y = fun i => x i / y i :=
  rfl
#align pi.div_def Pi.div_def
#align pi.sub_def Pi.sub_def
-/

/- warning: pi.div_comp -> Pi.div_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Div.{u3} γ] (x : β -> γ) (y : β -> γ) (z : α -> β), Eq.{max (succ u1) (succ u3)} (α -> γ) (Function.comp.{succ u1, succ u2, succ u3} α β γ (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (β -> γ) (β -> γ) (β -> γ) (instHDiv.{max u2 u3} (β -> γ) (Pi.instDiv.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) x y) z) (HDiv.hDiv.{max u1 u3, max u1 u3, max u1 u3} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u1 u3} (α -> γ) (Pi.instDiv.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) (Function.comp.{succ u1, succ u2, succ u3} α β γ x z) (Function.comp.{succ u1, succ u2, succ u3} α β γ y z))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : Div.{u3} γ] (x : β -> γ) (y : β -> γ) (z : α -> β), Eq.{max (succ u2) (succ u3)} (α -> γ) (Function.comp.{succ u2, succ u1, succ u3} α β γ (HDiv.hDiv.{max u1 u3, max u1 u3, max u1 u3} (β -> γ) (β -> γ) (β -> γ) (instHDiv.{max u1 u3} (β -> γ) (Pi.instDiv.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) x y) z) (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u2 u3} (α -> γ) (Pi.instDiv.{u2, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) (Function.comp.{succ u2, succ u1, succ u3} α β γ x z) (Function.comp.{succ u2, succ u1, succ u3} α β γ y z))
Case conversion may be inaccurate. Consider using '#align pi.div_comp Pi.div_compₓ'. -/
@[to_additive]
theorem div_comp [Div γ] (x y : β → γ) (z : α → β) : (x / y) ∘ z = x ∘ z / y ∘ z :=
  rfl
#align pi.div_comp Pi.div_comp
#align pi.sub_comp Pi.sub_comp

#print Pi.const_div /-
@[simp, to_additive]
theorem const_div [Div β] (a b : β) : const α a / const α b = const α (a / b) :=
  rfl
#align pi.const_div Pi.const_div
#align pi.const_sub Pi.const_sub
-/

section

variable [DecidableEq I]

variable [∀ i, One (f i)] [∀ i, One (g i)] [∀ i, One (h i)]

#print Pi.mulSingle /-
/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive Pi.single "The function supported at `i`, with value `x` there, and `0` elsewhere."]
def mulSingle (i : I) (x : f i) : ∀ i, f i :=
  Function.update 1 i x
#align pi.mul_single Pi.mulSingle
#align pi.single Pi.single
-/

#print Pi.mulSingle_eq_same /-
@[simp, to_additive]
theorem mulSingle_eq_same (i : I) (x : f i) : mulSingle i x i = x :=
  Function.update_same i x _
#align pi.mul_single_eq_same Pi.mulSingle_eq_same
#align pi.single_eq_same Pi.single_eq_same
-/

#print Pi.mulSingle_eq_of_ne /-
@[simp, to_additive]
theorem mulSingle_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : mulSingle i x i' = 1 :=
  Function.update_noteq h x _
#align pi.mul_single_eq_of_ne Pi.mulSingle_eq_of_ne
#align pi.single_eq_of_ne Pi.single_eq_of_ne
-/

#print Pi.mulSingle_eq_of_ne' /-
/-- Abbreviation for `mul_single_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[simp, to_additive "Abbreviation for `single_eq_of_ne h.symm`, for ease of\nuse by `simp`."]
theorem mulSingle_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x
#align pi.mul_single_eq_of_ne' Pi.mulSingle_eq_of_ne'
#align pi.single_eq_of_ne' Pi.single_eq_of_ne'
-/

#print Pi.mulSingle_one /-
@[simp, to_additive]
theorem mulSingle_one (i : I) : mulSingle i (1 : f i) = 1 :=
  Function.update_eq_self _ _
#align pi.mul_single_one Pi.mulSingle_one
#align pi.single_zero Pi.single_zero
-/

/- warning: pi.mul_single_apply -> Pi.mulSingle_apply is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {β : Type.{u2}} [_inst_5 : One.{u2} β] (i : I) (x : β) (i' : I), Eq.{succ u2} β (Pi.mulSingle.{u1, u2} I (fun (i : I) => β) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5) i x i') (ite.{succ u2} β (Eq.{succ u1} I i' i) (_inst_1 i' i) x (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_5))))
but is expected to have type
  forall {I : Type.{u2}} {_inst_1 : Type.{u1}} [β : DecidableEq.{succ u2} I] [_inst_5 : One.{u1} _inst_1] (i : I) (x : _inst_1) (i' : I), Eq.{succ u1} _inst_1 (Pi.mulSingle.{u2, u1} I (fun (i : I) => _inst_1) (fun (a : I) (b : I) => β a b) (fun (i : I) => _inst_5) i x i') (ite.{succ u1} _inst_1 (Eq.{succ u2} I i' i) (β i' i) x (OfNat.ofNat.{u1} _inst_1 1 (One.toOfNat1.{u1} _inst_1 _inst_5)))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_apply Pi.mulSingle_applyₓ'. -/
/-- On non-dependent functions, `pi.mul_single` can be expressed as an `ite` -/
@[to_additive "On non-dependent functions, `pi.single` can be expressed as an `ite`"]
theorem mulSingle_apply {β : Sort _} [One β] (i : I) (x : β) (i' : I) :
    mulSingle i x i' = if i' = i then x else 1 :=
  Function.update_apply 1 i x i'
#align pi.mul_single_apply Pi.mulSingle_apply
#align pi.single_apply Pi.single_apply

/- warning: pi.mul_single_comm -> Pi.mulSingle_comm is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {β : Type.{u2}} [_inst_5 : One.{u2} β] (i : I) (x : β) (i' : I), Eq.{succ u2} β (Pi.mulSingle.{u1, u2} I (fun (i : I) => β) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5) i x i') (Pi.mulSingle.{u1, u2} I (fun (i' : I) => β) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5) i' x i)
but is expected to have type
  forall {I : Type.{u2}} {_inst_1 : Type.{u1}} [β : DecidableEq.{succ u2} I] [_inst_5 : One.{u1} _inst_1] (i : I) (x : _inst_1) (i' : I), Eq.{succ u1} _inst_1 (Pi.mulSingle.{u2, u1} I (fun (i : I) => _inst_1) (fun (a : I) (b : I) => β a b) (fun (i : I) => _inst_5) i x i') (Pi.mulSingle.{u2, u1} I (fun (i' : I) => _inst_1) (fun (a : I) (b : I) => β a b) (fun (i : I) => _inst_5) i' x i)
Case conversion may be inaccurate. Consider using '#align pi.mul_single_comm Pi.mulSingle_commₓ'. -/
/-- On non-dependent functions, `pi.mul_single` is symmetric in the two indices. -/
@[to_additive "On non-dependent functions, `pi.single` is symmetric in the two\nindices."]
theorem mulSingle_comm {β : Sort _} [One β] (i : I) (x : β) (i' : I) :
    mulSingle i x i' = mulSingle i' x i := by simp [mul_single_apply, eq_comm]
#align pi.mul_single_comm Pi.mulSingle_comm
#align pi.single_comm Pi.single_comm

#print Pi.apply_mulSingle /-
@[to_additive]
theorem apply_mulSingle (f' : ∀ i, f i → g i) (hf' : ∀ i, f' i 1 = 1) (i : I) (x : f i) (j : I) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mul_single] using Function.apply_update f' 1 i x j
#align pi.apply_mul_single Pi.apply_mulSingle
#align pi.apply_single Pi.apply_single
-/

#print Pi.apply_mulSingle₂ /-
@[to_additive apply_single₂]
theorem apply_mulSingle₂ (f' : ∀ i, f i → g i → h i) (hf' : ∀ i, f' i 1 1 = 1) (i : I) (x : f i)
    (y : g i) (j : I) : f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j :=
  by
  by_cases h : j = i
  · subst h
    simp only [mul_single_eq_same]
  · simp only [mul_single_eq_of_ne h, hf']
#align pi.apply_mul_single₂ Pi.apply_mulSingle₂
#align pi.apply_single₂ Pi.apply_single₂
-/

/- warning: pi.mul_single_op -> Pi.mulSingle_op is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), One.{u2} (f i)] {g : I -> Type.{u3}} [_inst_5 : forall (i : I), One.{u3} (g i)] (op : forall (i : I), (f i) -> (g i)), (forall (i : I), Eq.{succ u3} (g i) (op i (OfNat.ofNat.{u2} (f i) 1 (OfNat.mk.{u2} (f i) 1 (One.one.{u2} (f i) (_inst_2 i))))) (OfNat.ofNat.{u3} (g i) 1 (OfNat.mk.{u3} (g i) 1 (One.one.{u3} (g i) (_inst_5 i))))) -> (forall (i : I) (x : f i), Eq.{max (succ u1) (succ u3)} (forall (i : I), g i) (Pi.mulSingle.{u1, u3} I (fun (i : I) => g i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5 i) i (op i x)) (fun (j : I) => op j (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_2 i) i x j)))
but is expected to have type
  forall {I : Type.{u2}} {f : I -> Type.{u3}} [_inst_1 : DecidableEq.{succ u2} I] [_inst_2 : forall (i : I), One.{u3} (f i)] {g : I -> Type.{u1}} [_inst_5 : forall (i : I), One.{u1} (g i)] (op : forall (i : I), (f i) -> (g i)), (forall (i : I), Eq.{succ u1} (g i) (op i (OfNat.ofNat.{u3} (f i) 1 (One.toOfNat1.{u3} (f i) (_inst_2 i)))) (OfNat.ofNat.{u1} (g i) 1 (One.toOfNat1.{u1} (g i) (_inst_5 i)))) -> (forall (i : I) (x : f i), Eq.{max (succ u2) (succ u1)} (forall (i : I), g i) (Pi.mulSingle.{u2, u1} I g (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5 i) i (op i x)) (fun (j : I) => op j (Pi.mulSingle.{u2, u3} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_2 i) i x j)))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_op Pi.mulSingle_opₓ'. -/
@[to_additive]
theorem mulSingle_op {g : I → Type _} [∀ i, One (g i)] (op : ∀ i, f i → g i) (h : ∀ i, op i 1 = 1)
    (i : I) (x : f i) : mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  Eq.symm <| funext <| apply_mulSingle op h i x
#align pi.mul_single_op Pi.mulSingle_op
#align pi.single_op Pi.single_op

/- warning: pi.mul_single_op₂ -> Pi.mulSingle_op₂ is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), One.{u2} (f i)] {g₁ : I -> Type.{u3}} {g₂ : I -> Type.{u4}} [_inst_5 : forall (i : I), One.{u3} (g₁ i)] [_inst_6 : forall (i : I), One.{u4} (g₂ i)] (op : forall (i : I), (g₁ i) -> (g₂ i) -> (f i)), (forall (i : I), Eq.{succ u2} (f i) (op i (OfNat.ofNat.{u3} (g₁ i) 1 (OfNat.mk.{u3} (g₁ i) 1 (One.one.{u3} (g₁ i) (_inst_5 i)))) (OfNat.ofNat.{u4} (g₂ i) 1 (OfNat.mk.{u4} (g₂ i) 1 (One.one.{u4} (g₂ i) (_inst_6 i))))) (OfNat.ofNat.{u2} (f i) 1 (OfNat.mk.{u2} (f i) 1 (One.one.{u2} (f i) (_inst_2 i))))) -> (forall (i : I) (x₁ : g₁ i) (x₂ : g₂ i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_2 i) i (op i x₁ x₂)) (fun (j : I) => op j (Pi.mulSingle.{u1, u3} I g₁ (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5 i) i x₁ j) (Pi.mulSingle.{u1, u4} I g₂ (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_6 i) i x₂ j)))
but is expected to have type
  forall {I : Type.{u3}} {f : I -> Type.{u4}} [_inst_1 : DecidableEq.{succ u3} I] [_inst_2 : forall (i : I), One.{u4} (f i)] {g₁ : I -> Type.{u2}} {g₂ : I -> Type.{u1}} [_inst_5 : forall (i : I), One.{u2} (g₁ i)] [_inst_6 : forall (i : I), One.{u1} (g₂ i)] (op : forall (i : I), (g₁ i) -> (g₂ i) -> (f i)), (forall (i : I), Eq.{succ u4} (f i) (op i (OfNat.ofNat.{u2} (g₁ i) 1 (One.toOfNat1.{u2} (g₁ i) (_inst_5 i))) (OfNat.ofNat.{u1} (g₂ i) 1 (One.toOfNat1.{u1} (g₂ i) (_inst_6 i)))) (OfNat.ofNat.{u4} (f i) 1 (One.toOfNat1.{u4} (f i) (_inst_2 i)))) -> (forall (i : I) (x₁ : g₁ i) (x₂ : g₂ i), Eq.{max (succ u3) (succ u4)} (forall (i : I), f i) (Pi.mulSingle.{u3, u4} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_2 i) i (op i x₁ x₂)) (fun (j : I) => op j (Pi.mulSingle.{u3, u2} I g₁ (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_5 i) i x₁ j) (Pi.mulSingle.{u3, u1} I g₂ (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_6 i) i x₂ j)))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_op₂ Pi.mulSingle_op₂ₓ'. -/
@[to_additive]
theorem mulSingle_op₂ {g₁ g₂ : I → Type _} [∀ i, One (g₁ i)] [∀ i, One (g₂ i)]
    (op : ∀ i, g₁ i → g₂ i → f i) (h : ∀ i, op i 1 1 = 1) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
    mulSingle i (op i x₁ x₂) = fun j => op j (mulSingle i x₁ j) (mulSingle i x₂ j) :=
  Eq.symm <| funext <| apply_mulSingle₂ op h i x₁ x₂
#align pi.mul_single_op₂ Pi.mulSingle_op₂
#align pi.single_op₂ Pi.single_op₂

variable (f)

#print Pi.mulSingle_injective /-
@[to_additive]
theorem mulSingle_injective (i : I) : Function.Injective (mulSingle i : f i → ∀ i, f i) :=
  Function.update_injective _ i
#align pi.mul_single_injective Pi.mulSingle_injective
#align pi.single_injective Pi.single_injective
-/

#print Pi.mulSingle_inj /-
@[simp, to_additive]
theorem mulSingle_inj (i : I) {x y : f i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (Pi.mulSingle_injective _ _).eq_iff
#align pi.mul_single_inj Pi.mulSingle_inj
#align pi.single_inj Pi.single_inj
-/

end

#print Pi.prod /-
/-- The mapping into a product type built from maps into each component. -/
@[simp]
protected def prod (f' : ∀ i, f i) (g' : ∀ i, g i) (i : I) : f i × g i :=
  (f' i, g' i)
#align pi.prod Pi.prod
-/

/- warning: pi.prod_fst_snd -> Pi.prod_fst_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max (succ (max u1 u2)) (succ u1) (succ u2)} ((Prod.{u1, u2} α β) -> (Prod.{u1, u2} α β)) (Pi.prod.{max u1 u2, u1, u2} (Prod.{u1, u2} α β) (fun (self : Prod.{u1, u2} α β) => α) (fun (self : Prod.{u1, u2} α β) => β) (Prod.fst.{u1, u2} α β) (Prod.snd.{u1, u2} α β)) (id.{max (succ u1) (succ u2)} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} ((Prod.{u2, u1} α β) -> (Prod.{u2, u1} α β)) (Pi.prod.{max u2 u1, u2, u1} (Prod.{u2, u1} α β) (fun (self : Prod.{u2, u1} α β) => α) (fun (self : Prod.{u2, u1} α β) => β) (Prod.fst.{u2, u1} α β) (Prod.snd.{u2, u1} α β)) (id.{max (succ u2) (succ u1)} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align pi.prod_fst_snd Pi.prod_fst_sndₓ'. -/
@[simp]
theorem prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id :=
  funext fun _ => Prod.mk.eta
#align pi.prod_fst_snd Pi.prod_fst_snd

/- warning: pi.prod_snd_fst -> Pi.prod_snd_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{max (succ (max u1 u2)) (succ u2) (succ u1)} ((Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (Pi.prod.{max u1 u2, u2, u1} (Prod.{u1, u2} α β) (fun (self : Prod.{u1, u2} α β) => β) (fun (self : Prod.{u1, u2} α β) => α) (Prod.snd.{u1, u2} α β) (Prod.fst.{u1, u2} α β)) (Prod.swap.{u1, u2} α β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} ((Prod.{u2, u1} α β) -> (Prod.{u1, u2} β α)) (Pi.prod.{max u2 u1, u1, u2} (Prod.{u2, u1} α β) (fun (self : Prod.{u2, u1} α β) => β) (fun (self : Prod.{u2, u1} α β) => α) (Prod.snd.{u2, u1} α β) (Prod.fst.{u2, u1} α β)) (Prod.swap.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align pi.prod_snd_fst Pi.prod_snd_fstₓ'. -/
@[simp]
theorem prod_snd_fst : Pi.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = Prod.swap :=
  rfl
#align pi.prod_snd_fst Pi.prod_snd_fst

end Pi

namespace Function

section Extend

#print Function.extend_one /-
@[to_additive]
theorem extend_one [One γ] (f : α → β) : Function.extend f (1 : α → γ) (1 : β → γ) = 1 :=
  funext fun _ => by apply if_t_t _ _
#align function.extend_one Function.extend_one
#align function.extend_zero Function.extend_zero
-/

#print Function.extend_mul /-
@[to_additive]
theorem extend_mul [Mul γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂ :=
  funext fun _ => by convert (apply_dite₂ (· * ·) _ _ _ _ _).symm
#align function.extend_mul Function.extend_mul
#align function.extend_add Function.extend_add
-/

#print Function.extend_inv /-
@[to_additive]
theorem extend_inv [Inv γ] (f : α → β) (g : α → γ) (e : β → γ) :
    Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹ :=
  funext fun _ => by convert (apply_dite Inv.inv _ _ _).symm
#align function.extend_inv Function.extend_inv
#align function.extend_neg Function.extend_neg
-/

#print Function.extend_div /-
@[to_additive]
theorem extend_div [Div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂ :=
  funext fun _ => by convert (apply_dite₂ (· / ·) _ _ _ _ _).symm
#align function.extend_div Function.extend_div
#align function.extend_sub Function.extend_sub
-/

end Extend

#print Function.surjective_pi_map /-
theorem surjective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Surjective (F i)) :
    Surjective fun x : ∀ i, f i => fun i => F i (x i) := fun y =>
  ⟨fun i => (hF i (y i)).some, funext fun i => (hF i (y i)).choose_spec⟩
#align function.surjective_pi_map Function.surjective_pi_map
-/

#print Function.injective_pi_map /-
theorem injective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Injective (F i)) :
    Injective fun x : ∀ i, f i => fun i => F i (x i) := fun x y h =>
  funext fun i => hF i <| (congr_fun h i : _)
#align function.injective_pi_map Function.injective_pi_map
-/

#print Function.bijective_pi_map /-
theorem bijective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Bijective (F i)) :
    Bijective fun x : ∀ i, f i => fun i => F i (x i) :=
  ⟨injective_pi_map fun i => (hF i).Injective, surjective_pi_map fun i => (hF i).Surjective⟩
#align function.bijective_pi_map Function.bijective_pi_map
-/

end Function

#print uniqueOfSurjectiveOne /-
/-- If the one function is surjective, the codomain is trivial. -/
@[to_additive "If the zero function is surjective, the codomain is trivial."]
def uniqueOfSurjectiveOne (α : Type _) {β : Type _} [One β] (h : Function.Surjective (1 : α → β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)
#align unique_of_surjective_one uniqueOfSurjectiveOne
#align unique_of_surjective_zero uniqueOfSurjectiveZero
-/

/- warning: subsingleton.pi_mul_single_eq -> Subsingleton.pi_mulSingle_eq is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : Subsingleton.{succ u1} I] [_inst_3 : One.{u2} α] (i : I) (x : α), Eq.{max (succ u1) (succ u2)} (I -> α) (Pi.mulSingle.{u1, u2} I (fun (i : I) => α) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_3) i x) (fun (_x : I) => x)
but is expected to have type
  forall {I : Type.{u2}} {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} I] [_inst_2 : Subsingleton.{succ u2} I] [_inst_3 : One.{u1} α] (i : I) (x : α), Eq.{max (succ u2) (succ u1)} (I -> α) (Pi.mulSingle.{u2, u1} I (fun (i : I) => α) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_3) i x) (fun (_x : I) => x)
Case conversion may be inaccurate. Consider using '#align subsingleton.pi_mul_single_eq Subsingleton.pi_mulSingle_eqₓ'. -/
@[to_additive Subsingleton.pi_single_eq]
theorem Subsingleton.pi_mulSingle_eq {α : Type _} [DecidableEq I] [Subsingleton I] [One α] (i : I)
    (x : α) : Pi.mulSingle i x = fun _ => x :=
  funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]
#align subsingleton.pi_mul_single_eq Subsingleton.pi_mulSingle_eq
#align subsingleton.pi_single_eq Subsingleton.pi_single_eq

namespace Sum

variable (a a' : α → γ) (b b' : β → γ)

/- warning: sum.elim_one_one -> Sum.elim_one_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : One.{u3} γ], Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (OfNat.ofNat.{max u1 u3} (α -> γ) 1 (OfNat.mk.{max u1 u3} (α -> γ) 1 (One.one.{max u1 u3} (α -> γ) (Pi.instOne.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))))) (OfNat.ofNat.{max u2 u3} (β -> γ) 1 (OfNat.mk.{max u2 u3} (β -> γ) 1 (One.one.{max u2 u3} (β -> γ) (Pi.instOne.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1)))))) (OfNat.ofNat.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) 1 (OfNat.mk.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) 1 (One.one.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) (Pi.instOne.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (i : Sum.{u1, u2} α β) => _inst_1)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : One.{u3} γ], Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u2, u1} α β) -> γ) (Sum.elim.{u2, u1, succ u3} α β γ (OfNat.ofNat.{max u2 u3} (α -> γ) 1 (One.toOfNat1.{max u2 u3} (α -> γ) (Pi.instOne.{u2, u3} α (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.4107 : α) => γ) (fun (i : α) => _inst_1)))) (OfNat.ofNat.{max u1 u3} (β -> γ) 1 (One.toOfNat1.{max u1 u3} (β -> γ) (Pi.instOne.{u1, u3} β (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.4113 : β) => γ) (fun (i : β) => _inst_1))))) (OfNat.ofNat.{max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) 1 (One.toOfNat1.{max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) (Pi.instOne.{max u2 u1, u3} (Sum.{u2, u1} α β) (fun (a._@.Mathlib.Data.Sum.Basic._hyg.1871 : Sum.{u2, u1} α β) => γ) (fun (i : Sum.{u2, u1} α β) => _inst_1))))
Case conversion may be inaccurate. Consider using '#align sum.elim_one_one Sum.elim_one_oneₓ'. -/
@[simp, to_additive]
theorem elim_one_one [One γ] : Sum.elim (1 : α → γ) (1 : β → γ) = 1 :=
  Sum.elim_const_const 1
#align sum.elim_one_one Sum.elim_one_one
#align sum.elim_zero_zero Sum.elim_zero_zero

/- warning: sum.elim_mul_single_one -> Sum.elim_mulSingle_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : One.{u3} γ] (i : α) (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (Pi.mulSingle.{u1, u3} α (fun (i : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) (fun (i : α) => _inst_3) i c) (OfNat.ofNat.{max u2 u3} (β -> γ) 1 (OfNat.mk.{max u2 u3} (β -> γ) 1 (One.one.{max u2 u3} (β -> γ) (Pi.instOne.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_3)))))) (Pi.mulSingle.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) β (fun (a : β) (b : β) => _inst_2 a b) a b) (fun (i : Sum.{u1, u2} α β) => _inst_3) (Sum.inl.{u1, u2} α β i) c)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : One.{u1} γ] (i : α) (c : γ), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((Sum.{u3, u2} α β) -> γ) (Sum.elim.{u3, u2, succ u1} α β γ (Pi.mulSingle.{u3, u1} α (fun (i : α) => γ) (fun (a : α) (b : α) => _inst_1 a b) (fun (i : α) => _inst_3) i c) (OfNat.ofNat.{max u2 u1} (β -> γ) 1 (One.toOfNat1.{max u2 u1} (β -> γ) (Pi.instOne.{u2, u1} β (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.4181 : β) => γ) (fun (i : β) => _inst_3))))) (Pi.mulSingle.{max u2 u3, u1} (Sum.{u3, u2} α β) (fun (ᾰ : Sum.{u3, u2} α β) => γ) (fun (a : Sum.{u3, u2} α β) (b : Sum.{u3, u2} α β) => Sum.instDecidableEqSum.{u3, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (fun (i : Sum.{u3, u2} α β) => _inst_3) (Sum.inl.{u3, u2} α β i) c)
Case conversion may be inaccurate. Consider using '#align sum.elim_mul_single_one Sum.elim_mulSingle_oneₓ'. -/
@[simp, to_additive]
theorem elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β → γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]
#align sum.elim_mul_single_one Sum.elim_mulSingle_one
#align sum.elim_single_zero Sum.elim_single_zero

/- warning: sum.elim_one_mul_single -> Sum.elim_one_mulSingle is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : One.{u3} γ] (i : β) (c : γ), Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (OfNat.ofNat.{max u1 u3} (α -> γ) 1 (OfNat.mk.{max u1 u3} (α -> γ) 1 (One.one.{max u1 u3} (α -> γ) (Pi.instOne.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_3))))) (Pi.mulSingle.{u2, u3} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_2 a b) (fun (i : β) => _inst_3) i c)) (Pi.mulSingle.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (a : Sum.{u1, u2} α β) (b : Sum.{u1, u2} α β) => Sum.decidableEq.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) β (fun (a : β) (b : β) => _inst_2 a b) a b) (fun (i : Sum.{u1, u2} α β) => _inst_3) (Sum.inr.{u1, u2} α β i) c)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : DecidableEq.{succ u3} α] [_inst_2 : DecidableEq.{succ u2} β] [_inst_3 : One.{u1} γ] (i : β) (c : γ), Eq.{max (max (succ u3) (succ u2)) (succ u1)} ((Sum.{u3, u2} α β) -> γ) (Sum.elim.{u3, u2, succ u1} α β γ (OfNat.ofNat.{max u3 u1} (α -> γ) 1 (One.toOfNat1.{max u3 u1} (α -> γ) (Pi.instOne.{u3, u1} α (fun (a._@.Mathlib.Data.Pi.Algebra._hyg.4249 : α) => γ) (fun (i : α) => _inst_3)))) (Pi.mulSingle.{u2, u1} β (fun (ᾰ : β) => γ) (fun (a : β) (b : β) => _inst_2 a b) (fun (i : β) => _inst_3) i c)) (Pi.mulSingle.{max u2 u3, u1} (Sum.{u3, u2} α β) (fun (ᾰ : Sum.{u3, u2} α β) => γ) (fun (a : Sum.{u3, u2} α β) (b : Sum.{u3, u2} α β) => Sum.instDecidableEqSum.{u3, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (fun (i : Sum.{u3, u2} α β) => _inst_3) (Sum.inr.{u3, u2} α β i) c)
Case conversion may be inaccurate. Consider using '#align sum.elim_one_mul_single Sum.elim_one_mulSingleₓ'. -/
@[simp, to_additive]
theorem elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
    Sum.elim (1 : α → γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]
#align sum.elim_one_mul_single Sum.elim_one_mulSingle
#align sum.elim_zero_single Sum.elim_zero_single

/- warning: sum.elim_inv_inv -> Sum.elim_inv_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α -> γ) (b : β -> γ) [_inst_1 : Inv.{u3} γ], Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (Inv.inv.{max u1 u3} (α -> γ) (Pi.instInv.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1)) a) (Inv.inv.{max u2 u3} (β -> γ) (Pi.instInv.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1)) b)) (Inv.inv.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) (Pi.instInv.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (i : Sum.{u1, u2} α β) => _inst_1)) (Sum.elim.{u1, u2, succ u3} α β γ a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (a : α -> γ) (b : β -> γ) [_inst_1 : Inv.{u3} γ], Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u2, u1} α β) -> γ) (Sum.elim.{u2, u1, succ u3} α β γ (Inv.inv.{max u2 u3} (α -> γ) (Pi.instInv.{u2, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1)) a) (Inv.inv.{max u3 u1} (β -> γ) (Pi.instInv.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1)) b)) (Inv.inv.{max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) (Pi.instInv.{max u2 u1, u3} (Sum.{u2, u1} α β) (fun (ᾰ : Sum.{u2, u1} α β) => γ) (fun (i : Sum.{u2, u1} α β) => _inst_1)) (Sum.elim.{u2, u1, succ u3} α β γ a b))
Case conversion may be inaccurate. Consider using '#align sum.elim_inv_inv Sum.elim_inv_invₓ'. -/
@[to_additive]
theorem elim_inv_inv [Inv γ] : Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹ :=
  (Sum.comp_elim Inv.inv a b).symm
#align sum.elim_inv_inv Sum.elim_inv_inv
#align sum.elim_neg_neg Sum.elim_neg_neg

/- warning: sum.elim_mul_mul -> Sum.elim_mul_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α -> γ) (a' : α -> γ) (b : β -> γ) (b' : β -> γ) [_inst_1 : Mul.{u3} γ], Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (HMul.hMul.{max u1 u3, max u1 u3, max u1 u3} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u1 u3} (α -> γ) (Pi.instMul.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) a a') (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (β -> γ) (β -> γ) (β -> γ) (instHMul.{max u2 u3} (β -> γ) (Pi.instMul.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) b b')) (HMul.hMul.{max (max u1 u2) u3, max (max u1 u2) u3, max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) ((Sum.{u1, u2} α β) -> γ) ((Sum.{u1, u2} α β) -> γ) (instHMul.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) (Pi.instMul.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (i : Sum.{u1, u2} α β) => _inst_1))) (Sum.elim.{u1, u2, succ u3} α β γ a b) (Sum.elim.{u1, u2, succ u3} α β γ a' b'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (a : α -> γ) (a' : α -> γ) (b : β -> γ) (b' : β -> γ) [_inst_1 : Mul.{u3} γ], Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u2, u1} α β) -> γ) (Sum.elim.{u2, u1, succ u3} α β γ (HMul.hMul.{max u2 u3, max u2 u3, max u2 u3} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u2 u3} (α -> γ) (Pi.instMul.{u2, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) a a') (HMul.hMul.{max u1 u3, max u1 u3, max u1 u3} (β -> γ) (β -> γ) (β -> γ) (instHMul.{max u1 u3} (β -> γ) (Pi.instMul.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) b b')) (HMul.hMul.{max (max u2 u1) u3, max (max u2 u1) u3, max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) ((Sum.{u2, u1} α β) -> γ) ((Sum.{u2, u1} α β) -> γ) (instHMul.{max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) (Pi.instMul.{max u2 u1, u3} (Sum.{u2, u1} α β) (fun (ᾰ : Sum.{u2, u1} α β) => γ) (fun (i : Sum.{u2, u1} α β) => _inst_1))) (Sum.elim.{u2, u1, succ u3} α β γ a b) (Sum.elim.{u2, u1, succ u3} α β γ a' b'))
Case conversion may be inaccurate. Consider using '#align sum.elim_mul_mul Sum.elim_mul_mulₓ'. -/
@[to_additive]
theorem elim_mul_mul [Mul γ] : Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b' :=
  by
  ext x
  cases x <;> rfl
#align sum.elim_mul_mul Sum.elim_mul_mul
#align sum.elim_add_add Sum.elim_add_add

/- warning: sum.elim_div_div -> Sum.elim_div_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (a : α -> γ) (a' : α -> γ) (b : β -> γ) (b' : β -> γ) [_inst_1 : Div.{u3} γ], Eq.{max (max (succ u1) (succ u2)) (succ u3)} ((Sum.{u1, u2} α β) -> γ) (Sum.elim.{u1, u2, succ u3} α β γ (HDiv.hDiv.{max u1 u3, max u1 u3, max u1 u3} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u1 u3} (α -> γ) (Pi.instDiv.{u1, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) a a') (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (β -> γ) (β -> γ) (β -> γ) (instHDiv.{max u2 u3} (β -> γ) (Pi.instDiv.{u2, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) b b')) (HDiv.hDiv.{max (max u1 u2) u3, max (max u1 u2) u3, max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) ((Sum.{u1, u2} α β) -> γ) ((Sum.{u1, u2} α β) -> γ) (instHDiv.{max (max u1 u2) u3} ((Sum.{u1, u2} α β) -> γ) (Pi.instDiv.{max u1 u2, u3} (Sum.{u1, u2} α β) (fun (ᾰ : Sum.{u1, u2} α β) => γ) (fun (i : Sum.{u1, u2} α β) => _inst_1))) (Sum.elim.{u1, u2, succ u3} α β γ a b) (Sum.elim.{u1, u2, succ u3} α β γ a' b'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} (a : α -> γ) (a' : α -> γ) (b : β -> γ) (b' : β -> γ) [_inst_1 : Div.{u3} γ], Eq.{max (max (succ u2) (succ u1)) (succ u3)} ((Sum.{u2, u1} α β) -> γ) (Sum.elim.{u2, u1, succ u3} α β γ (HDiv.hDiv.{max u2 u3, max u2 u3, max u2 u3} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u2 u3} (α -> γ) (Pi.instDiv.{u2, u3} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_1))) a a') (HDiv.hDiv.{max u1 u3, max u1 u3, max u1 u3} (β -> γ) (β -> γ) (β -> γ) (instHDiv.{max u1 u3} (β -> γ) (Pi.instDiv.{u1, u3} β (fun (ᾰ : β) => γ) (fun (i : β) => _inst_1))) b b')) (HDiv.hDiv.{max (max u2 u1) u3, max (max u2 u1) u3, max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) ((Sum.{u2, u1} α β) -> γ) ((Sum.{u2, u1} α β) -> γ) (instHDiv.{max (max u2 u1) u3} ((Sum.{u2, u1} α β) -> γ) (Pi.instDiv.{max u2 u1, u3} (Sum.{u2, u1} α β) (fun (ᾰ : Sum.{u2, u1} α β) => γ) (fun (i : Sum.{u2, u1} α β) => _inst_1))) (Sum.elim.{u2, u1, succ u3} α β γ a b) (Sum.elim.{u2, u1, succ u3} α β γ a' b'))
Case conversion may be inaccurate. Consider using '#align sum.elim_div_div Sum.elim_div_divₓ'. -/
@[to_additive]
theorem elim_div_div [Div γ] : Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b' :=
  by
  ext x
  cases x <;> rfl
#align sum.elim_div_div Sum.elim_div_div
#align sum.elim_sub_sub Sum.elim_sub_sub

end Sum

