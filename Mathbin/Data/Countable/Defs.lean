/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.countable.defs
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finite.Defs

/-!
# Countable types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a typeclass saying that a given `Sort*` is countable. See also `encodable`
for a version that singles out a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of this typeclass. More instances can be found in other
files.
-/


open Function

universe u v

variable {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/


#print Countable /-
/- ./././Mathport/Syntax/Translate/Command.lean:379:30: infer kinds are unsupported in Lean 4: #[`exists_injective_nat] [] -/
/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
@[mk_iff countable_iff_exists_injective]
class Countable (α : Sort u) : Prop where
  exists_injective_nat : ∃ f : α → ℕ, Injective f
#align countable Countable
-/

instance : Countable ℕ :=
  ⟨⟨id, injective_id⟩⟩

export Countable (exists_injective_nat)

#print Function.Injective.countable /-
protected theorem Function.Injective.countable [Countable β] {f : α → β} (hf : Injective f) :
    Countable α :=
  let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩
#align function.injective.countable Function.Injective.countable
-/

#print Function.Surjective.countable /-
protected theorem Function.Surjective.countable [Countable α] {f : α → β} (hf : Surjective f) :
    Countable β :=
  (injective_surjInv hf).Countable
#align function.surjective.countable Function.Surjective.countable
-/

#print exists_surjective_nat /-
theorem exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : ∃ f : ℕ → α, Surjective f :=
  let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, invFun_surjective hf⟩
#align exists_surjective_nat exists_surjective_nat
-/

#print countable_iff_exists_surjective /-
theorem countable_iff_exists_surjective [Nonempty α] : Countable α ↔ ∃ f : ℕ → α, Surjective f :=
  ⟨@exists_surjective_nat _ _, fun ⟨f, hf⟩ => hf.Countable⟩
#align countable_iff_exists_surjective countable_iff_exists_surjective
-/

/- warning: countable.of_equiv -> Countable.of_equiv is a dubious translation:
lean 3 declaration is
  forall {β : Sort.{u1}} (α : Sort.{u2}) [_inst_1 : Countable.{u2} α], (Equiv.{u2, u1} α β) -> (Countable.{u1} β)
but is expected to have type
  forall {β : Sort.{u2}} (α : Sort.{u1}) [_inst_1 : Countable.{u1} α], (Equiv.{u1, u2} α β) -> (Countable.{u2} β)
Case conversion may be inaccurate. Consider using '#align countable.of_equiv Countable.of_equivₓ'. -/
theorem Countable.of_equiv (α : Sort _) [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.Injective.Countable
#align countable.of_equiv Countable.of_equiv

#print Equiv.countable_iff /-
theorem Equiv.countable_iff (e : α ≃ β) : Countable α ↔ Countable β :=
  ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩
#align equiv.countable_iff Equiv.countable_iff
-/

instance {β : Type v} [Countable β] : Countable (ULift.{u} β) :=
  Countable.of_equiv _ Equiv.ulift.symm

/-!
### Operations on `Sort*`s
-/


instance [Countable α] : Countable (PLift α) :=
  Equiv.plift.Injective.Countable

#print Subsingleton.to_countable /-
instance (priority := 100) Subsingleton.to_countable [Subsingleton α] : Countable α :=
  ⟨⟨fun _ => 0, fun x y h => Subsingleton.elim x y⟩⟩
#align subsingleton.to_countable Subsingleton.to_countable
-/

instance (priority := 500) [Countable α] {p : α → Prop} : Countable { x // p x } :=
  Subtype.val_injective.Countable

instance {n : ℕ} : Countable (Fin n) :=
  Function.Injective.countable (@Fin.eq_of_veq n)

#print Finite.to_countable /-
instance (priority := 100) Finite.to_countable [Finite α] : Countable α :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  Countable.of_equiv _ e.symm
#align finite.to_countable Finite.to_countable
-/

instance : Countable PUnit.{u} :=
  Subsingleton.to_countable

-- Since this always succeeds, there is no reason not to have this at normal priority.
-- Perhaps the `instance_priority` linter could be clever enough to notice this itself.
@[nolint instance_priority]
instance PropCat.countable (p : Prop) : Countable p :=
  Subsingleton.to_countable
#align Prop.countable PropCat.countable

#print Bool.countable /-
instance Bool.countable : Countable Bool :=
  ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩
#align bool.countable Bool.countable
-/

instance PropCat.countable' : Countable Prop :=
  Countable.of_equiv Bool Equiv.propEquivBool.symm
#align Prop.countable' PropCat.countable'

instance (priority := 500) [Countable α] {r : α → α → Prop} : Countable (Quot r) :=
  (surjective_quot_mk r).Countable

instance (priority := 500) [Countable α] {s : Setoid α} : Countable (Quotient s) :=
  Quot.countable

