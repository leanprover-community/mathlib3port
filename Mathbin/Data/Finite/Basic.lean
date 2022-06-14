/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.SetTheory.Cardinal.Finite

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

The cardinality of a finite type `α` is given by `nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `finite` instance
for the type. (Note: we could have defined a `finite.card` that required you to
supply a `finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

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

Theorems about `nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `set_theory.cardinal.finite` module.

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

/-- There is (noncomputably) an equivalence between a finite type `α` and `fin (nat.card α)`. -/
def Finite.equivFin (α : Type _) [Finite α] : α ≃ Finₓ (Nat.card α) := by
  have := (Finite.exists_equiv_fin α).some_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

/-- Similar to `finite.equiv_fin` but with control over the term used for the cardinality. -/
def Finite.equivFinOfCardEq [Finite α] {n : ℕ} (h : Nat.card α = n) : α ≃ Finₓ n := by
  subst h
  apply Finite.equivFin

/-- Noncomputably get a `fintype` instance from a `finite` instance. This is not an
instance because we want `fintype` instances to be useful for computations. -/
def Fintype.ofFinite (α : Type _) [Finite α] : Fintype α :=
  Fintype.ofEquiv _ (Finite.equivFin α).symm

theorem finite_iff_nonempty_fintype (α : Type _) : Finite α ↔ Nonempty (Fintype α) :=
  ⟨fun _ => ⟨Fintype.ofFinite α⟩, fun ⟨_⟩ => inferInstance⟩

theorem finite_or_infinite (α : Type _) : Finite α ∨ Infinite α := by
  cases fintypeOrInfinite α
  · exact Or.inl inferInstance
    
  · exact Or.inr inferInstance
    

theorem not_finite (α : Type _) [h1 : Infinite α] [h2 : Finite α] : False :=
  have := Fintype.ofFinite α
  not_fintype α

theorem Finite.of_not_infinite {α : Type _} (h : ¬Infinite α) : Finite α :=
  Finite.of_fintype (fintypeOfNotInfinite h)

theorem Infinite.of_not_finite {α : Type _} (h : ¬Finite α) : Infinite α :=
  ⟨fun h' => h (Finite.of_fintype h')⟩

theorem not_infinite_iff_finite {α : Type _} : ¬Infinite α ↔ Finite α :=
  ⟨Finite.of_not_infinite, fun h h' => not_finite α⟩

theorem not_finite_iff_infinite {α : Type _} : ¬Finite α ↔ Infinite α :=
  not_infinite_iff_finite.not_right.symm

theorem Nat.card_eq (α : Type _) : Nat.card α = if h : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  · let this := Fintype.ofFinite α
    simp only [*, Nat.card_eq_fintype_card, dif_pos]
    
  · simp [*, not_finite_iff_infinite.mpr h]
    

theorem Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card]
  exact Fintype.card_pos_iff

theorem of_subsingleton {α : Sort _} [Subsingleton α] : Finite α :=
  Finite.of_equiv _ Equivₓ.plift

@[nolint instance_priority]
instance Finite.prop (p : Prop) : Finite p :=
  of_subsingleton

namespace Finite

theorem exists_max [Finite α] [Nonempty α] [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
  have := Fintype.ofFinite α
  Fintype.exists_max f

theorem exists_min [Finite α] [Nonempty α] [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x₀ ≤ f x :=
  have := Fintype.ofFinite α
  Fintype.exists_min f

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

theorem card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp [Fintype.card_eq]

-- see Note [lower instance priority]
instance (priority := 100) of_is_empty {α : Sort _} [IsEmpty α] : Finite α :=
  Finite.of_equiv _ Equivₓ.plift

theorem card_le_one_iff_subsingleton [Finite α] : Nat.card α ≤ 1 ↔ Subsingleton α := by
  have := Fintype.ofFinite α
  simp [Fintype.card_le_one_iff_subsingleton]

theorem one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α := by
  have := Fintype.ofFinite α
  simp [Fintype.one_lt_card_iff_nontrivial]

theorem one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.card α :=
  one_lt_card_iff_nontrivial.mpr h

@[simp]
theorem card_option [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  have := Fintype.ofFinite α
  simp

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

theorem card_sum [Finite α] [Finite β] : Nat.card (Sum α β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp

theorem card_le_of_injective [Finite β] (f : α → β) (hf : Function.Injective f) : Nat.card α ≤ Nat.card β := by
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f hf
  simpa using Fintype.card_le_of_injective f hf

theorem card_le_of_embedding [Finite β] (f : α ↪ β) : Nat.card α ≤ Nat.card β :=
  card_le_of_injective _ f.Injective

theorem card_le_of_surjective [Finite α] (f : α → β) (hf : Function.Surjective f) : Nat.card β ≤ Nat.card α := by
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f hf
  simpa using Fintype.card_le_of_surjective f hf

theorem card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α := by
  have := Fintype.ofFinite α
  simp [Fintype.card_eq_zero_iff]

end Finite

instance Subtype.finite {α : Sort _} [Finite α] {p : α → Prop} : Finite { x // p x } :=
  Finite.of_injective coe Subtype.coe_injective

theorem Finite.card_subtype_le [Finite α] (p : α → Prop) : Nat.card { x // p x } ≤ Nat.card α := by
  have := Fintype.ofFinite α
  simpa using Fintype.card_subtype_le p

theorem Finite.card_subtype_lt [Finite α] {p : α → Prop} {x : α} (hx : ¬p x) : Nat.card { x // p x } < Nat.card α := by
  have := Fintype.ofFinite α
  simpa using Fintype.card_subtype_lt hx

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

