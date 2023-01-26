/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

! This file was ported from Lean 3 source module data.finite.defs
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Basic

/-!
# Definition of the `finite` typeclass

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Finite /-
/-- A type is `finite` if it is in bijective correspondence to some
`fin n`.

While this could be defined as `nonempty (fintype α)`, it is defined
in this way to allow there to be `finite` instances for propositions.
-/
class inductive Finite (α : Sort _) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite
#align finite Finite
-/

/- warning: finite_iff_exists_equiv_fin -> finite_iff_exists_equiv_fin is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Iff (Finite.{u1} α) (Exists.{1} Nat (fun (n : Nat) => Nonempty.{max 1 (max u1 1) (imax 1 u1)} (Equiv.{u1, 1} α (Fin n))))
but is expected to have type
  forall {α : Sort.{u1}}, Iff (Finite.{u1} α) (Exists.{1} Nat (fun (n : Nat) => Nonempty.{max 1 u1} (Equiv.{u1, 1} α (Fin n))))
Case conversion may be inaccurate. Consider using '#align finite_iff_exists_equiv_fin finite_iff_exists_equiv_finₓ'. -/
theorem finite_iff_exists_equiv_fin {α : Sort _} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨n, ⟨e⟩⟩ => ⟨e⟩⟩
#align finite_iff_exists_equiv_fin finite_iff_exists_equiv_fin

/- warning: finite.exists_equiv_fin -> Finite.exists_equiv_fin is a dubious translation:
lean 3 declaration is
  forall (α : Sort.{u1}) [h : Finite.{u1} α], Exists.{1} Nat (fun (n : Nat) => Nonempty.{max 1 (max u1 1) (imax 1 u1)} (Equiv.{u1, 1} α (Fin n)))
but is expected to have type
  forall (α : Sort.{u1}) [h : Finite.{u1} α], Exists.{1} Nat (fun (n : Nat) => Nonempty.{max 1 u1} (Equiv.{u1, 1} α (Fin n)))
Case conversion may be inaccurate. Consider using '#align finite.exists_equiv_fin Finite.exists_equiv_finₓ'. -/
theorem Finite.exists_equiv_fin (α : Sort _) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h
#align finite.exists_equiv_fin Finite.exists_equiv_fin

#print Finite.of_equiv /-
theorem Finite.of_equiv (α : Sort _) [h : Finite α] (f : α ≃ β) : Finite β :=
  by
  cases' h with n e
  exact Finite.intro (f.symm.trans e)
#align finite.of_equiv Finite.of_equiv
-/

/- warning: equiv.finite_iff -> Equiv.finite_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (Equiv.{u1, u2} α β) -> (Iff (Finite.{u1} α) (Finite.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, (Equiv.{u2, u1} α β) -> (Iff (Finite.{u2} α) (Finite.{u1} β))
Case conversion may be inaccurate. Consider using '#align equiv.finite_iff Equiv.finite_iffₓ'. -/
theorem Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩
#align equiv.finite_iff Equiv.finite_iff

/- warning: function.bijective.finite_iff -> Function.Bijective.finite_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {f : α -> β}, (Function.Bijective.{u1, u2} α β f) -> (Iff (Finite.{u1} α) (Finite.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {f : α -> β}, (Function.Bijective.{u2, u1} α β f) -> (Iff (Finite.{u2} α) (Finite.{u1} β))
Case conversion may be inaccurate. Consider using '#align function.bijective.finite_iff Function.Bijective.finite_iffₓ'. -/
theorem Function.Bijective.finite_iff {f : α → β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equiv.ofBijective f h).finite_iff
#align function.bijective.finite_iff Function.Bijective.finite_iff

/- warning: finite.of_bijective -> Finite.ofBijective is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} [_inst_1 : Finite.{u1} α] {f : α -> β}, (Function.Bijective.{u1, u2} α β f) -> (Finite.{u2} β)
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} [_inst_1 : Finite.{u2} α] {f : α -> β}, (Function.Bijective.{u2, u1} α β f) -> (Finite.{u1} β)
Case conversion may be inaccurate. Consider using '#align finite.of_bijective Finite.ofBijectiveₓ'. -/
theorem Finite.ofBijective [Finite α] {f : α → β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›
#align finite.of_bijective Finite.ofBijective

instance [Finite α] : Finite (PLift α) :=
  Finite.of_equiv α Equiv.plift.symm

instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equiv.ulift.symm

#print Infinite /-
/-- A type is said to be infinite if it is not finite. Note that `infinite α` is equivalent to
`is_empty (fintype α)` or `is_empty (finite α)`. -/
class Infinite (α : Sort _) : Prop where
  not_finite : ¬Finite α
#align infinite Infinite
-/

#print not_finite_iff_infinite /-
@[simp]
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩
#align not_finite_iff_infinite not_finite_iff_infinite
-/

#print not_infinite_iff_finite /-
@[simp]
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm
#align not_infinite_iff_finite not_infinite_iff_finite
-/

/- warning: equiv.infinite_iff -> Equiv.infinite_iff is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}}, (Equiv.{u1, u2} α β) -> (Iff (Infinite.{u1} α) (Infinite.{u2} β))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}}, (Equiv.{u2, u1} α β) -> (Iff (Infinite.{u2} α) (Infinite.{u1} β))
Case conversion may be inaccurate. Consider using '#align equiv.infinite_iff Equiv.infinite_iffₓ'. -/
theorem Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β :=
  not_finite_iff_infinite.symm.trans <| e.finite_iff.Not.trans not_finite_iff_infinite
#align equiv.infinite_iff Equiv.infinite_iff

instance [Infinite α] : Infinite (PLift α) :=
  Equiv.plift.infinite_iff.2 ‹_›

instance {α : Type v} [Infinite α] : Infinite (ULift.{u} α) :=
  Equiv.ulift.infinite_iff.2 ‹_›

#print finite_or_infinite /-
theorem finite_or_infinite (α : Sort _) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 <| not_finite_iff_infinite.1
#align finite_or_infinite finite_or_infinite
-/

#print not_finite /-
theorem not_finite (α : Sort _) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›
#align not_finite not_finite
-/

#print Finite.false /-
protected theorem Finite.false [Infinite α] (h : Finite α) : False :=
  not_finite α
#align finite.false Finite.false
-/

#print Infinite.false /-
protected theorem Infinite.false [Finite α] (h : Infinite α) : False :=
  not_finite α
#align infinite.false Infinite.false
-/

alias not_infinite_iff_finite ↔ Finite.of_not_infinite Finite.not_infinite
#align finite.of_not_infinite Finite.of_not_infinite
#align finite.not_infinite Finite.not_infinite

