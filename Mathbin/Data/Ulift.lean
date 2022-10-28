/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Logic.Equiv.Basic

/-!
# Extra lemmas about `ulift` and `plift`

In this file we provide `subsingleton`, `unique`, `decidable_eq`, and `is_empty` instances for
`ulift α` and `plift α`. We also prove `ulift.forall`, `ulift.exists`, `plift.forall`, and
`plift.exists`.
-/


universe u v

open Function

namespace PLift

variable {α : Sort u} {β : Sort v}

instance [Subsingleton α] : Subsingleton (PLift α) :=
  Equiv.plift.Subsingleton

instance [Nonempty α] : Nonempty (PLift α) :=
  Equiv.plift.Nonempty

instance [Unique α] : Unique (PLift α) :=
  Equiv.plift.unique

instance [DecidableEq α] : DecidableEq (PLift α) :=
  Equiv.plift.DecidableEq

instance [IsEmpty α] : IsEmpty (PLift α) :=
  Equiv.plift.isEmpty

theorem up_injective : Injective (@up α) :=
  Equiv.plift.symm.Injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.plift.symm.Surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.plift.symm.Bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff

theorem down_surjective : Surjective (@down α) :=
  Equiv.plift.Surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.plift.Bijective

@[simp]
theorem forall {p : PLift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (PLift.up x) :=
  up_surjective.forall

@[simp]
theorem exists {p : PLift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (PLift.up x) :=
  up_surjective.exists

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

instance [Subsingleton α] : Subsingleton (ULift α) :=
  Equiv.ulift.Subsingleton

instance [Nonempty α] : Nonempty (ULift α) :=
  Equiv.ulift.Nonempty

instance [Unique α] : Unique (ULift α) :=
  Equiv.ulift.unique

instance [DecidableEq α] : DecidableEq (ULift α) :=
  Equiv.ulift.DecidableEq

instance [IsEmpty α] : IsEmpty (ULift α) :=
  Equiv.ulift.isEmpty

theorem up_injective : Injective (@up α) :=
  Equiv.ulift.symm.Injective

theorem up_surjective : Surjective (@up α) :=
  Equiv.ulift.symm.Surjective

theorem up_bijective : Bijective (@up α) :=
  Equiv.ulift.symm.Bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff

theorem down_surjective : Surjective (@down α) :=
  Equiv.ulift.Surjective

theorem down_bijective : Bijective (@down α) :=
  Equiv.ulift.Bijective

@[simp]
theorem forall {p : ULift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ULift.up x) :=
  up_surjective.forall

@[simp]
theorem exists {p : ULift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ULift.up x) :=
  up_surjective.exists

end ULift

