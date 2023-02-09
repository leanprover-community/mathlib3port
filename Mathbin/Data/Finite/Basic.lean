/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.finite.basic
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Powerset
import Mathbin.Data.Fintype.Prod
import Mathbin.Data.Fintype.Sigma
import Mathbin.Data.Fintype.Sum
import Mathbin.Data.Fintype.Vector

/-!
# Finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove some theorems about `finite` and provide some instances. This typeclass is a
`Prop`-valued counterpart of the typeclass `fintype`. See more details in the file where `finite` is
defined.

## Main definitions

* `fintype.finite`, `finite.of_fintype` creates a `finite` instance from a `fintype` instance. The
  former lemma takes `fintype α` as an explicit argument while the latter takes it as an instance
  argument.
* `fintype.of_finite` noncomputably creates a `fintype` instance from a `finite` instance.

## Implementation notes

There is an apparent duplication of many `fintype` instances in this module,
however they follow a pattern: if a `fintype` instance depends on `decidable`
instances or other `fintype` instances, then we need to "lower" the instance
to be a `finite` instance by removing the `decidable` instances and switching
the `fintype` instances to `finite` instances. These are precisely the ones
that cannot be inferred using `finite.of_fintype`. (However, when using
`open_locale classical` or the `classical` tactic the instances relying only
on `decidable` instances will give `finite` instances.) In the future we might
consider writing automation to create these "lowered" instances.

## Tags

finiteness, finite types
-/


noncomputable section

open Classical

variable {α β γ : Type _}

namespace Finite

#print Finite.of_subsingleton /-
-- see Note [lower instance priority]
instance (priority := 100) of_subsingleton {α : Sort _} [Subsingleton α] : Finite α :=
  of_injective (Function.const α ()) <| Function.injective_of_subsingleton _
#align finite.of_subsingleton Finite.of_subsingleton
-/

#print Finite.prop /-
-- Higher priority for `Prop`s
@[nolint instance_priority]
instance prop (p : Prop) : Finite p :=
  Finite.of_subsingleton
#align finite.prop Finite.prop
-/

instance [Finite α] [Finite β] : Finite (α × β) :=
  by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

instance {α β : Sort _} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equiv.pprodEquivProdPLift.symm

#print Finite.prod_left /-
theorem prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjective
#align finite.prod_left Finite.prod_left
-/

#print Finite.prod_right /-
theorem prod_right (α) [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective
#align finite.prod_right Finite.prod_right
-/

instance [Finite α] [Finite β] : Finite (Sum α β) :=
  by
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  infer_instance

#print Finite.sum_left /-
theorem sum_left (β) [Finite (Sum α β)] : Finite α :=
  of_injective (Sum.inl : α → Sum α β) Sum.inl_injective
#align finite.sum_left Finite.sum_left
-/

#print Finite.sum_right /-
theorem sum_right (α) [Finite (Sum α β)] : Finite β :=
  of_injective (Sum.inr : β → Sum α β) Sum.inr_injective
#align finite.sum_right Finite.sum_right
-/

instance {β : α → Type _} [Finite α] [∀ a, Finite (β a)] : Finite (Σa, β a) :=
  by
  letI := Fintype.ofFinite α
  letI := fun a => Fintype.ofFinite (β a)
  infer_instance

instance {ι : Sort _} {π : ι → Sort _} [Finite ι] [∀ i, Finite (π i)] : Finite (Σ'i, π i) :=
  of_equiv _ (Equiv.psigmaEquivSigmaPLift π).symm

instance [Finite α] : Finite (Set α) :=
  by
  cases nonempty_fintype α
  infer_instance

end Finite

#print Subtype.finite /-
/-- This instance also provides `[finite s]` for `s : set α`. -/
instance Subtype.finite {α : Sort _} [Finite α] {p : α → Prop} : Finite { x // p x } :=
  Finite.of_injective coe Subtype.coe_injective
#align subtype.finite Subtype.finite
-/

#print Pi.finite /-
instance Pi.finite {α : Sort _} {β : α → Sort _} [Finite α] [∀ a, Finite (β a)] :
    Finite (∀ a, β a) := by
  haveI := Fintype.ofFinite (PLift α)
  haveI := fun a => Fintype.ofFinite (PLift (β a))
  exact
    Finite.of_equiv (∀ a : PLift α, PLift (β (Equiv.plift a)))
      (Equiv.piCongr Equiv.plift fun _ => Equiv.plift)
#align pi.finite Pi.finite
-/

#print Vector.finite /-
instance Vector.finite {α : Type _} [Finite α] {n : ℕ} : Finite (Vector α n) :=
  by
  haveI := Fintype.ofFinite α
  infer_instance
#align vector.finite Vector.finite
-/

#print Quot.finite /-
instance Quot.finite {α : Sort _} [Finite α] (r : α → α → Prop) : Finite (Quot r) :=
  Finite.of_surjective _ (surjective_quot_mk r)
#align quot.finite Quot.finite
-/

#print Quotient.finite /-
instance Quotient.finite {α : Sort _} [Finite α] (s : Setoid α) : Finite (Quotient s) :=
  Quot.finite _
#align quotient.finite Quotient.finite
-/

/- warning: function.embedding.finite -> Function.Embedding.finite is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u2} β], Finite.{max 1 (imax u1 u2)} (Function.Embedding.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u2} β], Finite.{max (max 1 u2) u1} (Function.Embedding.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align function.embedding.finite Function.Embedding.finiteₓ'. -/
instance Function.Embedding.finite {α β : Sort _} [Finite β] : Finite (α ↪ β) :=
  by
  cases' isEmpty_or_nonempty (α ↪ β) with _ h
  · infer_instance
  · refine' h.elim fun f => _
    haveI : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ FunLike.coe_injective
#align function.embedding.finite Function.Embedding.finite

/- warning: equiv.finite_right -> Equiv.finite_right is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u2} β], Finite.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u2} β], Finite.{max (max 1 u2) u1} (Equiv.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align equiv.finite_right Equiv.finite_rightₓ'. -/
instance Equiv.finite_right {α β : Sort _} [Finite β] : Finite (α ≃ β) :=
  Finite.of_injective Equiv.toEmbedding fun e₁ e₂ h => Equiv.ext <| by convert FunLike.congr_fun h
#align equiv.finite_right Equiv.finite_right

/- warning: equiv.finite_left -> Equiv.finite_left is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u1} α], Finite.{max 1 (imax u1 u2) (imax u2 u1)} (Equiv.{u1, u2} α β)
but is expected to have type
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u1} α], Finite.{max (max 1 u2) u1} (Equiv.{u1, u2} α β)
Case conversion may be inaccurate. Consider using '#align equiv.finite_left Equiv.finite_leftₓ'. -/
instance Equiv.finite_left {α β : Sort _} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equiv.symm, Equiv.symm, Equiv.symm_symm, Equiv.symm_symm⟩
#align equiv.finite_left Equiv.finite_left

instance [Finite α] {n : ℕ} : Finite (Sym α n) :=
  by
  haveI := Fintype.ofFinite α
  infer_instance

