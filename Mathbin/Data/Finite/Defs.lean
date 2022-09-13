/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Logic.Equiv.Basic

/-!
# Definition of the `finite` typeclass

This file defines a typeclass `finite` saying that `α : Sort*` is finite. A type is `finite` if it
is equivalent to `fin n` for some `n`. We also define `infinite α` as a typeclass equivalent to
`¬finite α`.

The `finite` predicate has no computational relevance and, being `Prop`-valued, gets to enjoy proof
irrelevance -- it represents the mere fact that the type is finite.  While the `fintype` class also
represents finiteness of a type, a key difference is that a `fintype` instance represents finiteness
in a computable way: it gives a concrete algorithm to produce a `finset` whose elements enumerate
the terms of the given type. As such, one generally relies on congruence lemmas when rewriting
expressions involving `fintype` instances.

Every `fintype` instance automatically gives a `finite` instance, see `fintype.finite`, but not vice
versa. Every `fintype` instance should be computable since they are meant for computation. If it's
not possible to write a computable `fintype` instance, one should prefer writing a `finite` instance
instead.

## Main definitions

* `finite α` denotes that `α` is a finite type.
* `infinite α` denotes that `α` is an infinite type.

## Implementation notes

The definition of `finite α` is not just `nonempty (fintype α)` since `fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `finite.prop`.

## Tags

finite, fintype
-/


universe u v

open Function

variable {α β : Sort _}

/-- A type is `finite` if it is in bijective correspondence to some
`fin n`.

While this could be defined as `nonempty (fintype α)`, it is defined
in this way to allow there to be `finite` instances for propositions.
-/
class inductive Finite (α : Sort _) : Prop
  | intro {n : ℕ} : α ≃ Finₓ n → Finite

theorem finite_iff_exists_equiv_fin {α : Sort _} : Finite α ↔ ∃ n, Nonempty (α ≃ Finₓ n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨n, ⟨e⟩⟩ => ⟨e⟩⟩

theorem Finite.exists_equiv_fin (α : Sort _) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Finₓ n) :=
  finite_iff_exists_equiv_fin.mp h

theorem Finite.of_equiv (α : Sort _) [h : Finite α] (f : α ≃ β) : Finite β := by
  cases' h with n e
  exact Finite.intro (f.symm.trans e)

theorem Equivₓ.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

theorem Function.Bijective.finite_iff {f : α → β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equivₓ.ofBijective f h).finite_iff

theorem Finite.of_bijective [Finite α] {f : α → β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›

instance [Finite α] : Finite (Plift α) :=
  Finite.of_equiv α Equivₓ.plift.symm

instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equivₓ.ulift.symm

/-- A type is said to be infinite if it is not finite. Note that `infinite α` is equivalent to
`is_empty (fintype α)` or `is_empty (finite α)`. -/
class Infinite (α : Sort _) : Prop where
  not_finite : ¬Finite α

@[simp]
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩

@[simp]
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm

theorem finite_or_infinite (α : Sort _) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 <| not_finite_iff_infinite.1

theorem not_finite (α : Sort _) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›

protected theorem Finite.false [Infinite α] (h : Finite α) : False :=
  not_finite α

protected theorem Infinite.false [Finite α] (h : Infinite α) : False :=
  not_finite α

alias not_infinite_iff_finite ↔ Finite.of_not_infinite Finite.not_infinite

