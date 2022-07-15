/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Fintype.Basic

/-!
# Finite types

This module defines a finiteness predicate on types called `finite`.
A type is `finite` if it is equivalent to `fin n` for some `n`, and
otherwise it is `infinite` (see `finite_or_infinite`). This predicate is
a `class`, and finiteness proofs are given as instances.

The `finite` predicate has no computational relevance and, being
`Prop`-valued, gets to enjoy proof irrelevance -- it represents the mere fact
that the type is finite.
While the `fintype` class also represents finiteness of a type, a key
difference is that a `fintype` instance represents finiteness in a
computable way: it gives a concrete algorithm to produce a `finset` whose
elements enumerate the terms of the given type. As such, one generally
relies on congruence lemmas when rewriting expressions involving
`fintype` instances.

Every `fintype` instance automatically gives a `finite` instance, but not
vice versa. Every `fintype` instance should be computable since they are meant
for computation. If it's not possible to write a computable `fintype` instance,
one should prefer writing a `finite` instance instead.

## Main definitions

* `finite α` denotes that `α` is a finite type.
* `finite.of_fintype` creates a `finite` instance from a `fintype` instance.
* `fintype.of_finite` noncomputably creates a `fintype` instance from a `finite` instance.
* `finite_or_infinite` is that every type is either `finite` or `infinite`.

## Implementation notes

The definition of `finite α` is not just `nonempty (fintype α)` since `fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `finite.prop`.

There is an apparent duplication of many `fintype` instances in this module,
however they follow a pattern: if a `fintype` instance depends on `decidable`
instances or other `fintype` instances, then we need to "lower" the instance
to be a `finite` instance by removing the `decidable` instances and switching
the `fintype` instances to `finite` instances. These are precisely the ones
that cannot be inferred using `finite.of_fintype'`. (However, when using
`open_locale classical` or the `classical` tactic the instances relying only
on `decidable` instances will give `finite` instances.) In the future we might
consider writing automation to create these "lowered" instances.

## Tags

finiteness, finite types

-/


noncomputable section

open Classical

variable {α β γ : Type _}

/-- A type is `finite` if it is in bijective correspondence to some
`fin n`.

While this could be defined as `nonempty (fintype α)`, it is defined
in this way to allow there to be `finite` instances for propositions.
-/
class inductive Finite (α : Sort _) : Prop
  | intro {n : ℕ} : α ≃ Finₓ n → Finite

theorem Finite.exists_equiv_fin (α : Sort _) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Finₓ n) := by
  cases' h with n f
  exact ⟨n, ⟨f⟩⟩

theorem Finite.of_equiv (α : Sort _) {β : Sort _} [h : Finite α] (f : α ≃ β) : Finite β := by
  cases' h with n e
  exact Finite.intro (f.symm.trans e)

theorem Equivₓ.finite_iff {α β : Sort _} (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

theorem Finite.of_fintype {α : Type _} (h : Fintype α) : Finite α :=
  ⟨Fintype.equivFin α⟩

/-- For efficiency reasons, we want `finite` instances to have higher
priority than ones coming from `fintype` instances. -/
instance (priority := 900) Finite.of_fintype' (α : Type _) [Fintype α] : Finite α :=
  Finite.of_fintype ‹_›

/-- Noncomputably get a `fintype` instance from a `finite` instance. This is not an
instance because we want `fintype` instances to be useful for computations. -/
def Fintype.ofFinite (α : Type _) [Finite α] : Fintype α :=
  Nonempty.some <|
    let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
    ⟨Fintype.ofEquiv _ e.symm⟩

theorem finite_iff_nonempty_fintype (α : Type _) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun h =>
    let ⟨k, ⟨e⟩⟩ := @Finite.exists_equiv_fin α h
    ⟨Fintype.ofEquiv _ e.symm⟩,
    fun ⟨_⟩ => inferInstance⟩

theorem not_finite_iff_infinite {α : Type _} : ¬Finite α ↔ Infinite α := by
  rw [← is_empty_fintype, finite_iff_nonempty_fintype, not_nonempty_iff]

theorem finite_or_infinite (α : Type _) : Finite α ∨ Infinite α := by
  rw [← not_finite_iff_infinite]
  apply em

theorem not_finite (α : Type _) [h1 : Infinite α] [h2 : Finite α] : False :=
  not_finite_iff_infinite.mpr h1 h2

theorem Finite.of_not_infinite {α : Type _} (h : ¬Infinite α) : Finite α := by
  rwa [← not_finite_iff_infinite, not_not] at h

theorem Infinite.of_not_finite {α : Type _} (h : ¬Finite α) : Infinite α :=
  not_finite_iff_infinite.mp h

theorem not_infinite_iff_finite {α : Type _} : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm

theorem of_subsingleton {α : Sort _} [Subsingleton α] : Finite α :=
  Finite.of_equiv _ Equivₓ.plift

@[nolint instance_priority]
instance Finite.prop (p : Prop) : Finite p :=
  of_subsingleton

namespace Finite

theorem exists_max [Finite α] [Nonempty α] [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x ≤ f x₀ := by
  have := Fintype.ofFinite α
  exact Fintype.exists_max f

theorem exists_min [Finite α] [Nonempty α] [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by
  have := Fintype.ofFinite α
  exact Fintype.exists_min f

instance {α : Sort _} [Finite α] : Finite (Plift α) :=
  Finite.of_equiv _ Equivₓ.plift.symm

theorem of_bijective {α β : Sort _} [Finite α] (f : α → β) (H : Function.Bijective f) : Finite β :=
  Finite.of_equiv _ (Equivₓ.ofBijective _ H)

theorem of_injective {α β : Sort _} [Finite β] (f : α → β) (H : Function.Injective f) : Finite α := by
  have := Fintype.ofFinite (Plift β)
  rw [← Equivₓ.injective_comp Equivₓ.plift f, ← Equivₓ.comp_injective _ equiv.plift.symm] at H
  have := Fintype.ofInjective _ H
  exact Finite.of_equiv _ Equivₓ.plift

theorem of_surjective {α β : Sort _} [Finite α] (f : α → β) (H : Function.Surjective f) : Finite β :=
  of_injective _ <| Function.injective_surj_inv H

-- see Note [lower instance priority]
instance (priority := 100) of_is_empty {α : Sort _} [IsEmpty α] : Finite α :=
  Finite.of_equiv _ Equivₓ.plift

instance [Finite α] [Finite β] : Finite (α × β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

instance {α β : Sort _} [Finite α] [Finite β] : Finite (PProd α β) :=
  of_equiv _ Equivₓ.pprodEquivProdPlift.symm

theorem prod_left β [Finite (α × β)] [Nonempty β] : Finite α :=
  of_surjective (Prod.fst : α × β → α) Prod.fst_surjectiveₓ

theorem prod_right α [Finite (α × β)] [Nonempty α] : Finite β :=
  of_surjective (Prod.snd : α × β → β) Prod.snd_surjective

instance [Finite α] : Finite (ULift α) := by
  have := Fintype.ofFinite α
  infer_instance

instance [Finite α] [Finite β] : Finite (Sum α β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  infer_instance

theorem sum_left β [Finite (Sum α β)] : Finite α :=
  of_injective (Sum.inl : α → Sum α β) Sum.inl_injective

theorem sum_right α [Finite (Sum α β)] : Finite β :=
  of_injective (Sum.inr : β → Sum α β) Sum.inr_injective

instance {β : α → Type _} [Finite α] [∀ a, Finite (β a)] : Finite (Σa, β a) := by
  let this := Fintype.ofFinite α
  let this := fun a => Fintype.ofFinite (β a)
  infer_instance

instance {ι : Sort _} {π : ι → Sort _} [Finite ι] [∀ i, Finite (π i)] : Finite (Σ'i, π i) :=
  of_equiv _ (Equivₓ.psigmaEquivSigmaPlift π).symm

end Finite

/-- This instance also provides `[finite s]` for `s : set α`. -/
instance Subtype.finite {α : Sort _} [Finite α] {p : α → Prop} : Finite { x // p x } :=
  Finite.of_injective coe Subtype.coe_injective

instance Pi.finite {α : Sort _} {β : α → Sort _} [Finite α] [∀ a, Finite (β a)] : Finite (∀ a, β a) := by
  have := Fintype.ofFinite (Plift α)
  have := fun a => Fintype.ofFinite (Plift (β a))
  exact Finite.of_equiv (∀ a : Plift α, Plift (β (Equivₓ.plift a))) (Equivₓ.piCongr Equivₓ.plift fun _ => Equivₓ.plift)

instance Vector.finite {α : Type _} [Finite α] {n : ℕ} : Finite (Vector α n) := by
  have := Fintype.ofFinite α
  infer_instance

instance Quot.finite {α : Sort _} [Finite α] (r : α → α → Prop) : Finite (Quot r) :=
  Finite.of_surjective _ (surjective_quot_mk r)

instance Quotientₓ.finite {α : Sort _} [Finite α] (s : Setoidₓ α) : Finite (Quotientₓ s) :=
  Quot.finite _

instance Function.Embedding.finite {α β : Sort _} [Finite β] : Finite (α ↪ β) := by
  cases' is_empty_or_nonempty (α ↪ β) with _ h
  · infer_instance
    
  · refine' h.elim fun f => _
    have : Finite α := Finite.of_injective _ f.injective
    exact Finite.of_injective _ FunLike.coe_injective
    

instance Equivₓ.finite_right {α β : Sort _} [Finite β] : Finite (α ≃ β) :=
  (Finite.of_injective Equivₓ.toEmbedding) fun e₁ e₂ h =>
    Equivₓ.ext <| by
      convert FunLike.congr_fun h

instance Equivₓ.finite_left {α β : Sort _} [Finite α] : Finite (α ≃ β) :=
  Finite.of_equiv _ ⟨Equivₓ.symm, Equivₓ.symm, Equivₓ.symm_symm, Equivₓ.symm_symm⟩

instance [Finite α] {n : ℕ} : Finite (Sym α n) := by
  have := Fintype.ofFinite α
  infer_instance

