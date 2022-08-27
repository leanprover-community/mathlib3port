/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.BoundedOrder

/-!
# Heyting algebras

This file defines Heyting, co-Heyting and bi-Heyting algebras.

An Heyting algebra is a bounded distributive lattice with an implication operation `⇨` such that
`a ≤ b ⇨ c ↔ a ⊓ b ≤ c`. It also comes with a pseudo-complement `ᶜ`, such that `aᶜ = a ⇨ ⊥`.

Co-Heyting algebras are dual to Heyting algebras. They have a difference `\` and a negation `￢`
such that `a \ b ≤ c ↔ a ≤ b ⊔ c` and `￢a = ⊤ \ a`.

Bi-Heyting algebras are Heyting algebras that are also co-Heyting algebras.

From a logic standpoint, Heyting algebras precisely model intuitionistic logic, whereas boolean
algebras model classical logic.

Heyting algebras are the order theoretic equivalent of cartesian-closed categories.

## Main declarations

* `generalized_heyting_algebra`: Heyting algebra without a top element (nor negation).
* `generalized_coheyting_algebra`: Co-Heyting algebra without a bottom element (nor complement).
* `heyting_algebra`: Heyting algebra.
* `coheyting_algebra`: Co-Heyting algebra.
* `biheyting_algebra`: bi-Heyting algebra.

## Notation

* `⇨`: Heyting implication
* `\`: Difference
* `￢`: Heyting negation
* `ᶜ`: (Pseudo-)complement

## References

* [Francis Borceux, *Handbook of Categorical Algebra III*][borceux-vol3]

## Tags

Heyting, Brouwer, algebra, implication, negation, intuitionistic
-/


open Function OrderDual

universe u

variable {ι α β : Type _}

/-! ### Notation -/


-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Syntax typeclass for Heyting implication `⇨`. -/
@[«./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasHimp (α : Type _) where
  himp : α → α → α

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
/-- Syntax typeclass for Heyting negation `￢`.

The difference between `has_hnot` and `has_compl` is that the former belongs to Heyting algebras,
while the latter belongs to co-Heyting algebras. They are both pseudo-complements, but `compl`
underestimates while `hnot` overestimates. In boolean algebras, they are equal. See `hnot_eq_compl`.
-/
@[«./././Mathport/Syntax/Translate/Command.lean:96:19: in notation_class: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg»]
class HasHnot (α : Type _) where
  hnot : α → α

export HasHimp (himp)

export Sdiff (sdiff)

export HasHnot (hnot)

-- mathport name: «expr ⇨ »
infixr:60 " ⇨ " => himp

-- mathport name: «expr￢ »
prefix:72 "￢" => hnot

instance [HasHimp α] [HasHimp β] : HasHimp (α × β) :=
  ⟨fun a b => (a.1 ⇨ b.1, a.2 ⇨ b.2)⟩

instance [HasHnot α] [HasHnot β] : HasHnot (α × β) :=
  ⟨fun a => (￢a.1, ￢a.2)⟩

instance [Sdiff α] [Sdiff β] : Sdiff (α × β) :=
  ⟨fun a b => (a.1 \ b.1, a.2 \ b.2)⟩

instance [HasCompl α] [HasCompl β] : HasCompl (α × β) :=
  ⟨fun a => (a.1ᶜ, a.2ᶜ)⟩

@[simp]
theorem fst_himp [HasHimp α] [HasHimp β] (a b : α × β) : (a ⇨ b).1 = a.1 ⇨ b.1 :=
  rfl

@[simp]
theorem snd_himp [HasHimp α] [HasHimp β] (a b : α × β) : (a ⇨ b).2 = a.2 ⇨ b.2 :=
  rfl

@[simp]
theorem fst_hnot [HasHnot α] [HasHnot β] (a : α × β) : (￢a).1 = ￢a.1 :=
  rfl

@[simp]
theorem snd_hnot [HasHnot α] [HasHnot β] (a : α × β) : (￢a).2 = ￢a.2 :=
  rfl

@[simp]
theorem fst_sdiff [Sdiff α] [Sdiff β] (a b : α × β) : (a \ b).1 = a.1 \ b.1 :=
  rfl

@[simp]
theorem snd_sdiff [Sdiff α] [Sdiff β] (a b : α × β) : (a \ b).2 = a.2 \ b.2 :=
  rfl

@[simp]
theorem fst_compl [HasCompl α] [HasCompl β] (a : α × β) : aᶜ.1 = a.1ᶜ :=
  rfl

@[simp]
theorem snd_compl [HasCompl α] [HasCompl β] (a : α × β) : aᶜ.2 = a.2ᶜ :=
  rfl

namespace Pi

variable {π : ι → Type _}

instance [∀ i, HasHimp (π i)] : HasHimp (∀ i, π i) :=
  ⟨fun a b i => a i ⇨ b i⟩

instance [∀ i, HasHnot (π i)] : HasHnot (∀ i, π i) :=
  ⟨fun a i => ￢a i⟩

theorem himp_def [∀ i, HasHimp (π i)] (a b : ∀ i, π i) : a ⇨ b = fun i => a i ⇨ b i :=
  rfl

theorem hnot_def [∀ i, HasHnot (π i)] (a : ∀ i, π i) : ￢a = fun i => ￢a i :=
  rfl

@[simp]
theorem himp_apply [∀ i, HasHimp (π i)] (a b : ∀ i, π i) (i : ι) : (a ⇨ b) i = a i ⇨ b i :=
  rfl

@[simp]
theorem hnot_apply [∀ i, HasHnot (π i)] (a : ∀ i, π i) (i : ι) : (￢a) i = ￢a i :=
  rfl

end Pi

/-- A generalized Heyting algebra is a lattice with an additional binary operation `⇨` called
Heyting implication such that `a ⇨` is right adjoint to `a ⊓`.

 This generalizes `heyting_algebra` by not requiring a bottom element. -/
class GeneralizedHeytingAlgebra (α : Type _) extends Lattice α, HasTop α, HasHimp α where
  le_top : ∀ a : α, a ≤ ⊤
  le_himp_iff (a b c : α) : a ≤ b ⇨ c ↔ a⊓b ≤ c

/-- A generalized co-Heyting algebra is a lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`.

This generalizes `coheyting_algebra` by not requiring a top element. -/
class GeneralizedCoheytingAlgebra (α : Type _) extends Lattice α, HasBot α, Sdiff α where
  bot_le : ∀ a : α, ⊥ ≤ a
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b⊔c

/-- A Heyting algebra is a bounded lattice with an additional binary operation `⇨` called Heyting
implication such that `a ⇨` is right adjoint to `a ⊓`. -/
class HeytingAlgebra (α : Type _) extends GeneralizedHeytingAlgebra α, HasBot α, HasCompl α where
  bot_le : ∀ a : α, ⊥ ≤ a
  himp_bot (a : α) : a ⇨ ⊥ = aᶜ

/-- A co-Heyting algebra is a bounded  lattice with an additional binary difference operation `\`
such that `\ a` is right adjoint to `⊔ a`. -/
class CoheytingAlgebra (α : Type _) extends GeneralizedCoheytingAlgebra α, HasTop α, HasHnot α where
  le_top : ∀ a : α, a ≤ ⊤
  top_sdiff (a : α) : ⊤ \ a = ￢a

/-- A bi-Heyting algebra is a Heyting algebra that is also a co-Heyting algebra. -/
class BiheytingAlgebra (α : Type _) extends HeytingAlgebra α, Sdiff α, HasHnot α where
  sdiff_le_iff (a b c : α) : a \ b ≤ c ↔ a ≤ b⊔c
  top_sdiff (a : α) : ⊤ \ a = ￢a

-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toOrderTop [GeneralizedHeytingAlgebra α] : OrderTop α :=
  { ‹GeneralizedHeytingAlgebra α› with }

-- See note [lower instance priority]
instance (priority := 100) GeneralizedCoheytingAlgebra.toOrderBot [GeneralizedCoheytingAlgebra α] : OrderBot α :=
  { ‹GeneralizedCoheytingAlgebra α› with }

-- See note [lower instance priority]
instance (priority := 100) HeytingAlgebra.toBoundedOrder [HeytingAlgebra α] : BoundedOrder α :=
  { ‹HeytingAlgebra α› with }

-- See note [lower instance priority]
instance (priority := 100) CoheytingAlgebra.toBoundedOrder [CoheytingAlgebra α] : BoundedOrder α :=
  { ‹CoheytingAlgebra α› with }

-- See note [lower instance priority]
instance (priority := 100) BiheytingAlgebra.toCoheytingAlgebra [BiheytingAlgebra α] : CoheytingAlgebra α :=
  { ‹BiheytingAlgebra α› with }

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and Heyting implication alone. -/
@[reducible]
def HeytingAlgebra.ofHimp [DistribLattice α] [BoundedOrder α] (himp : α → α → α)
    (le_himp_iff : ∀ a b c, a ≤ himp b c ↔ a⊓b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with himp, compl := fun a => himp a ⊥, le_himp_iff, himp_bot := fun a => rfl }

-- See note [reducible non-instances]
/-- Construct a Heyting algebra from the lattice structure and complement operator alone. -/
@[reducible]
def HeytingAlgebra.ofCompl [DistribLattice α] [BoundedOrder α] (compl : α → α)
    (le_himp_iff : ∀ a b c, a ≤ compl b⊔c ↔ a⊓b ≤ c) : HeytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with himp := fun a => (·⊔·) (compl a), compl, le_himp_iff,
    himp_bot := fun a => sup_bot_eq }

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the lattice structure and the difference alone. -/
@[reducible]
def CoheytingAlgebra.ofSdiff [DistribLattice α] [BoundedOrder α] (sdiff : α → α → α)
    (sdiff_le_iff : ∀ a b c, sdiff a b ≤ c ↔ a ≤ b⊔c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with sdiff, hnot := fun a => sdiff ⊤ a, sdiff_le_iff,
    top_sdiff := fun a => rfl }

-- See note [reducible non-instances]
/-- Construct a co-Heyting algebra from the difference and Heyting negation alone. -/
@[reducible]
def CoheytingAlgebra.ofHnot [DistribLattice α] [BoundedOrder α] (hnot : α → α)
    (sdiff_le_iff : ∀ a b c, a⊓hnot b ≤ c ↔ a ≤ b⊔c) : CoheytingAlgebra α :=
  { ‹DistribLattice α›, ‹BoundedOrder α› with sdiff := fun a b => a⊓hnot b, hnot, sdiff_le_iff,
    top_sdiff := fun a => top_inf_eq }

section GeneralizedHeytingAlgebra

variable [GeneralizedHeytingAlgebra α] {a b c d : α}

/- In this section, we'll give interpretations of these results in the Heyting algebra model of
intuitionistic logic,- where `≤` can be interpreted as "validates", `⇨` as "implies", `⊓` as "and",
`⊔` as "or", `⊥` as "false" and `⊤` as "true". Note that we confuse `→` and `⊢` because those are
the same in this logic.

See also `Prop.heyting_algebra`. -/
-- `p → q → r ↔ p ∧ q → r`
@[simp]
theorem le_himp_iff : a ≤ b ⇨ c ↔ a⊓b ≤ c :=
  GeneralizedHeytingAlgebra.le_himp_iff _ _ _

-- `p → q → r ↔ q → p → r`
theorem le_himp_comm : a ≤ b ⇨ c ↔ b ≤ a ⇨ c := by
  rw [le_himp_iff, le_himp_iff, inf_comm]

-- `p → q → p`
theorem le_himp : a ≤ b ⇨ a :=
  le_himp_iff.2 inf_le_left

-- `p → p → q ↔ p → q`
@[simp]
theorem le_himp_iff_left : a ≤ a ⇨ b ↔ a ≤ b := by
  rw [le_himp_iff, inf_idem]

-- `p → p`
@[simp]
theorem himp_self : a ⇨ a = ⊤ :=
  top_le_iff.1 <| le_himp_iff.2 inf_le_right

-- `(p → q) ∧ p → q`
theorem himp_inf_le : (a ⇨ b)⊓a ≤ b :=
  le_himp_iff.1 le_rflₓ

-- `p ∧ (p → q) → q`
theorem inf_himp_le : a⊓(a ⇨ b) ≤ b := by
  rw [inf_comm, ← le_himp_iff]

-- `p ∧ (p → q) ↔ p ∧ q`
@[simp]
theorem inf_himp (a b : α) : a⊓(a ⇨ b) = a⊓b :=
  le_antisymmₓ
      (le_inf inf_le_left <| by
        rw [inf_comm, ← le_himp_iff]) <|
    inf_le_inf_left _ le_himp

-- `(p → q) ∧ p ↔ q ∧ p`
@[simp]
theorem himp_inf_self (a b : α) : (a ⇨ b)⊓a = b⊓a := by
  rw [inf_comm, inf_himp, inf_comm]

/-- The **deduction theorem** in the Heyting algebra model of intuitionistic logic:
an implication holds iff the conclusion follows from the hypothesis. -/
@[simp]
theorem himp_eq_top_iff : a ⇨ b = ⊤ ↔ a ≤ b := by
  rw [← top_le_iff, le_himp_iff, top_inf_eq]

-- `p → true`, `true → p ↔ p`
@[simp]
theorem himp_top : a ⇨ ⊤ = ⊤ :=
  himp_eq_top_iff.2 le_top

@[simp]
theorem top_himp : ⊤ ⇨ a = a :=
  eq_of_forall_le_iffₓ fun b => by
    rw [le_himp_iff, inf_top_eq]

-- `p → q → r ↔ p ∧ q → r`
theorem himp_himp (a b c : α) : a ⇨ b ⇨ c = a⊓b ⇨ c :=
  eq_of_forall_le_iffₓ fun d => by
    simp_rw [le_himp_iff, inf_assoc]

-- `(q → r) → (p → q) → q → r`
@[simp]
theorem himp_le_himp_himp : b ⇨ c ≤ (a ⇨ b) ⇨ a ⇨ c := by
  rw [le_himp_iff, le_himp_iff, inf_assoc, himp_inf_self, ← inf_assoc, himp_inf_self, inf_assoc]
  exact inf_le_left

-- `p → q → r ↔ q → p → r`
theorem himp_left_comm (a b c : α) : a ⇨ b ⇨ c = b ⇨ a ⇨ c := by
  simp_rw [himp_himp, inf_comm]

theorem himp_inf_distrib (a b c : α) : a ⇨ b⊓c = (a ⇨ b)⊓(a ⇨ c) :=
  eq_of_forall_le_iffₓ fun d => by
    simp_rw [le_himp_iff, le_inf_iff, le_himp_iff]

theorem sup_himp_distrib (a b c : α) : a⊔b ⇨ c = (a ⇨ c)⊓(b ⇨ c) :=
  eq_of_forall_le_iffₓ fun d => by
    rw [le_inf_iff, le_himp_comm, sup_le_iff]
    simp_rw [le_himp_comm]

theorem himp_le_himp_left (h : a ≤ b) : c ⇨ a ≤ c ⇨ b :=
  le_himp_iff.2 <| himp_inf_le.trans h

theorem himp_le_himp_right (h : a ≤ b) : b ⇨ c ≤ a ⇨ c :=
  le_himp_iff.2 <| (inf_le_inf_left _ h).trans himp_inf_le

theorem himp_le_himp (hab : a ≤ b) (hcd : c ≤ d) : b ⇨ c ≤ a ⇨ d :=
  (himp_le_himp_right hab).trans <| himp_le_himp_left hcd

@[simp]
theorem sup_himp_self_left (a b : α) : a⊔b ⇨ a = b ⇨ a := by
  rw [sup_himp_distrib, himp_self, top_inf_eq]

@[simp]
theorem sup_himp_self_right (a b : α) : a⊔b ⇨ b = a ⇨ b := by
  rw [sup_himp_distrib, himp_self, inf_top_eq]

-- See note [lower instance priority]
instance (priority := 100) GeneralizedHeytingAlgebra.toDistribLattice : DistribLattice α :=
  DistribLattice.ofInfSupLe fun a b c => by
    simp_rw [@inf_comm _ _ a, ← le_himp_iff, sup_le_iff, le_himp_iff, ← sup_le_iff]

instance : GeneralizedCoheytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.orderBot α with sdiff := fun a b => toDual (ofDual b ⇨ ofDual a),
    sdiff_le_iff := fun a b c => by
      rw [sup_comm]
      exact le_himp_iff }

instance Prod.generalizedHeytingAlgebra [GeneralizedHeytingAlgebra β] : GeneralizedHeytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.orderTop α β, Prod.hasHimp, Prod.hasCompl with
    le_himp_iff := fun a b c => and_congr le_himp_iff le_himp_iff }

instance Pi.generalizedHeytingAlgebra {α : ι → Type _} [∀ i, GeneralizedHeytingAlgebra (α i)] :
    GeneralizedHeytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congrₓ fun i => le_himp_iff

end GeneralizedHeytingAlgebra

section GeneralizedCoheytingAlgebra

variable [GeneralizedCoheytingAlgebra α] {a b c d : α}

@[simp]
theorem sdiff_le_iff : a \ b ≤ c ↔ a ≤ b⊔c :=
  GeneralizedCoheytingAlgebra.sdiff_le_iff _ _ _

theorem sdiff_le_comm : a \ b ≤ c ↔ a \ c ≤ b := by
  rw [sdiff_le_iff, sdiff_le_iff, sup_comm]

theorem sdiff_le : a \ b ≤ a :=
  sdiff_le_iff.2 le_sup_right

theorem Disjoint.disjoint_sdiff_left (h : Disjoint a b) : Disjoint (a \ c) b :=
  h.mono_left sdiff_le

theorem Disjoint.disjoint_sdiff_right (h : Disjoint a b) : Disjoint a (b \ c) :=
  h.mono_right sdiff_le

@[simp]
theorem sdiff_le_iff_left : a \ b ≤ b ↔ a ≤ b := by
  rw [sdiff_le_iff, sup_idem]

@[simp]
theorem sdiff_self : a \ a = ⊥ :=
  le_bot_iff.1 <| sdiff_le_iff.2 le_sup_left

theorem le_sup_sdiff : a ≤ b⊔a \ b :=
  sdiff_le_iff.1 le_rflₓ

theorem le_sdiff_sup : a ≤ a \ b⊔b := by
  rw [sup_comm, ← sdiff_le_iff]

@[simp]
theorem sup_sdiff_self (a b : α) : a⊔b \ a = a⊔b :=
  le_antisymmₓ (sup_le_sup_left sdiff_le _) (sup_le le_sup_left le_sup_sdiff)

@[simp]
theorem sdiff_sup_self (a b : α) : b \ a⊔a = b⊔a := by
  rw [sup_comm, sup_sdiff_self, sup_comm]

@[simp]
theorem sdiff_eq_bot_iff : a \ b = ⊥ ↔ a ≤ b := by
  rw [← le_bot_iff, sdiff_le_iff, sup_bot_eq]

@[simp]
theorem sdiff_bot : a \ ⊥ = a :=
  eq_of_forall_ge_iffₓ fun b => by
    rw [sdiff_le_iff, bot_sup_eq]

@[simp]
theorem bot_sdiff : ⊥ \ a = ⊥ :=
  sdiff_eq_bot_iff.2 bot_le

theorem sdiff_sdiff (a b c : α) : (a \ b) \ c = a \ (b⊔c) :=
  eq_of_forall_ge_iffₓ fun d => by
    simp_rw [sdiff_le_iff, sup_assoc]

@[simp]
theorem sdiff_sdiff_le_sdiff : (a \ b) \ (a \ c) ≤ c \ b := by
  rw [sdiff_le_iff, sdiff_le_iff, sup_left_comm, sup_sdiff_self, sup_left_comm, sdiff_sup_self, sup_left_comm]
  exact le_sup_left

theorem sdiff_right_comm (a b c : α) : (a \ b) \ c = (a \ c) \ b := by
  simp_rw [sdiff_sdiff, sup_comm]

theorem sup_sdiff_distrib (a b c : α) : (a⊔b) \ c = a \ c⊔b \ c :=
  eq_of_forall_ge_iffₓ fun d => by
    simp_rw [sdiff_le_iff, sup_le_iff, sdiff_le_iff]

theorem sdiff_inf_distrib (a b c : α) : a \ (b⊓c) = a \ b⊔a \ c :=
  eq_of_forall_ge_iffₓ fun d => by
    rw [sup_le_iff, sdiff_le_comm, le_inf_iff]
    simp_rw [sdiff_le_comm]

theorem sdiff_le_sdiff_right (h : a ≤ b) : a \ c ≤ b \ c :=
  sdiff_le_iff.2 <| h.trans <| le_sup_sdiff

theorem sdiff_le_sdiff_left (h : a ≤ b) : c \ b ≤ c \ a :=
  sdiff_le_iff.2 <| le_sup_sdiff.trans <| sup_le_sup_right h _

theorem sdiff_le_sdiff (hab : a ≤ b) (hcd : c ≤ d) : a \ d ≤ b \ c :=
  (sdiff_le_sdiff_right hab).trans <| sdiff_le_sdiff_left hcd

-- cf. `is_compl.inf_sup`
theorem sdiff_inf : a \ (b⊓c) = a \ b⊔a \ c :=
  sdiff_inf_distrib _ _ _

@[simp]
theorem sdiff_inf_self_left (a b : α) : a \ (a⊓b) = a \ b := by
  rw [sdiff_inf, sdiff_self, bot_sup_eq]

@[simp]
theorem sdiff_inf_self_right (a b : α) : b \ (a⊓b) = b \ a := by
  rw [sdiff_inf, sdiff_self, sup_bot_eq]

-- See note [lower instance priority]
instance (priority := 100) GeneralizedCoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹GeneralizedCoheytingAlgebra α› with
    le_sup_inf := fun a b c => by
      simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff] }

instance : GeneralizedHeytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.orderTop α with himp := fun a b => toDual (ofDual b \ ofDual a),
    le_himp_iff := fun a b c => by
      rw [inf_comm]
      exact sdiff_le_iff }

instance Prod.generalizedCoheytingAlgebra [GeneralizedCoheytingAlgebra β] : GeneralizedCoheytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.orderBot α β, Prod.hasSdiff, Prod.hasHnot with
    sdiff_le_iff := fun a b c => and_congr sdiff_le_iff sdiff_le_iff }

instance Pi.generalizedCoheytingAlgebra {α : ι → Type _} [∀ i, GeneralizedCoheytingAlgebra (α i)] :
    GeneralizedCoheytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congrₓ fun i => sdiff_le_iff

end GeneralizedCoheytingAlgebra

section HeytingAlgebra

variable [HeytingAlgebra α] {a b c : α}

@[simp]
theorem himp_bot (a : α) : a ⇨ ⊥ = aᶜ :=
  HeytingAlgebra.himp_bot _

@[simp]
theorem bot_himp (a : α) : ⊥ ⇨ a = ⊤ :=
  himp_eq_top_iff.2 bot_le

theorem compl_sup_distrib (a b : α) : (a⊔b)ᶜ = aᶜ⊓bᶜ := by
  simp_rw [← himp_bot, sup_himp_distrib]

@[simp]
theorem compl_sup : (a⊔b)ᶜ = aᶜ⊓bᶜ :=
  compl_sup_distrib _ _

theorem compl_le_himp : aᶜ ≤ a ⇨ b :=
  (himp_bot _).Ge.trans <| himp_le_himp_left bot_le

theorem compl_sup_le_himp : aᶜ⊔b ≤ a ⇨ b :=
  sup_le compl_le_himp le_himp

theorem sup_compl_le_himp : b⊔aᶜ ≤ a ⇨ b :=
  sup_le le_himp compl_le_himp

-- `p → ¬ p ↔ ¬ p`
@[simp]
theorem himp_compl (a : α) : a ⇨ aᶜ = aᶜ := by
  rw [← himp_bot, himp_himp, inf_idem]

-- `p → ¬ q ↔ q → ¬ p`
theorem himp_compl_comm (a b : α) : a ⇨ bᶜ = b ⇨ aᶜ := by
  simp_rw [← himp_bot, himp_left_comm]

theorem le_compl_iff_disjoint_right : a ≤ bᶜ ↔ Disjoint a b := by
  rw [← himp_bot, le_himp_iff, Disjoint]

theorem le_compl_iff_disjoint_left : a ≤ bᶜ ↔ Disjoint b a :=
  le_compl_iff_disjoint_right.trans Disjoint.comm

theorem le_compl_comm : a ≤ bᶜ ↔ b ≤ aᶜ := by
  rw [le_compl_iff_disjoint_right, le_compl_iff_disjoint_left]

alias le_compl_iff_disjoint_right ↔ _ Disjoint.le_compl_right

alias le_compl_iff_disjoint_left ↔ _ Disjoint.le_compl_left

theorem disjoint_compl_left : Disjoint (aᶜ) a :=
  le_himp_iff.1 (himp_bot _).Ge

theorem disjoint_compl_right : Disjoint a (aᶜ) :=
  disjoint_compl_left.symm

@[simp]
theorem inf_compl_self (a : α) : a⊓aᶜ = ⊥ :=
  disjoint_compl_right.eq_bot

@[simp]
theorem compl_inf_self (a : α) : aᶜ⊓a = ⊥ :=
  disjoint_compl_left.eq_bot

theorem inf_compl_eq_bot : a⊓aᶜ = ⊥ :=
  inf_compl_self _

theorem compl_inf_eq_bot : aᶜ⊓a = ⊥ :=
  compl_inf_self _

@[simp]
theorem compl_top : (⊤ : α)ᶜ = ⊥ :=
  eq_of_forall_le_iffₓ fun a => by
    rw [le_compl_iff_disjoint_right, disjoint_top, le_bot_iff]

@[simp]
theorem compl_bot : (⊥ : α)ᶜ = ⊤ := by
  rw [← himp_bot, himp_self]

theorem le_compl_compl : a ≤ aᶜᶜ :=
  disjoint_compl_right.le_compl_right

theorem compl_anti : Antitone (compl : α → α) := fun a b h => le_compl_comm.1 <| h.trans le_compl_compl

theorem compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ :=
  compl_anti h

@[simp]
theorem compl_compl_compl (a : α) : aᶜᶜᶜ = aᶜ :=
  (compl_anti le_compl_compl).antisymm le_compl_compl

@[simp]
theorem disjoint_compl_compl_left_iff : Disjoint (aᶜᶜ) b ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_left, compl_compl_compl]

@[simp]
theorem disjoint_compl_compl_right_iff : Disjoint a (bᶜᶜ) ↔ Disjoint a b := by
  simp_rw [← le_compl_iff_disjoint_right, compl_compl_compl]

theorem compl_sup_compl_le : aᶜ⊔bᶜ ≤ (a⊓b)ᶜ :=
  sup_le (compl_anti inf_le_left) <| compl_anti inf_le_right

theorem compl_compl_inf_distrib (a b : α) : (a⊓b)ᶜᶜ = aᶜᶜ⊓bᶜᶜ := by
  refine' ((compl_anti compl_sup_compl_le).trans (compl_sup_distrib _ _).le).antisymm _
  rw [le_compl_iff_disjoint_right, disjoint_assoc, disjoint_compl_compl_left_iff, disjoint_left_comm,
    disjoint_compl_compl_left_iff, ← disjoint_assoc, inf_comm]
  exact disjoint_compl_right

theorem compl_compl_himp_distrib (a b : α) : (a ⇨ b)ᶜᶜ = aᶜᶜ ⇨ bᶜᶜ := by
  refine' le_antisymmₓ _ _
  · rw [le_himp_iff, ← compl_compl_inf_distrib]
    exact compl_anti (compl_anti himp_inf_le)
    
  · refine' le_compl_comm.1 ((compl_anti compl_sup_le_himp).trans _)
    rw [compl_sup_distrib, le_compl_iff_disjoint_right, disjoint_right_comm, ← le_compl_iff_disjoint_right]
    exact inf_himp_le
    

instance : CoheytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.boundedOrder α with hnot := to_dual ∘ compl ∘ of_dual,
    sdiff := fun a b => toDual (ofDual b ⇨ ofDual a),
    sdiff_le_iff := fun a b c => by
      rw [sup_comm]
      exact le_himp_iff,
    top_sdiff := himp_bot }

@[simp]
theorem of_dual_hnot (a : αᵒᵈ) : ofDual (￢a) = ofDual aᶜ :=
  rfl

@[simp]
theorem to_dual_compl (a : α) : toDual (aᶜ) = ￢toDual a :=
  rfl

instance Prod.heytingAlgebra [HeytingAlgebra β] : HeytingAlgebra (α × β) :=
  { Prod.generalizedHeytingAlgebra, Prod.boundedOrder α β, Prod.hasCompl with
    himp_bot := fun a => Prod.extₓ (himp_bot a.1) (himp_bot a.2) }

instance Pi.heytingAlgebra {α : ι → Type _} [∀ i, HeytingAlgebra (α i)] : HeytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congrₓ fun i => le_himp_iff

end HeytingAlgebra

section CoheytingAlgebra

variable [CoheytingAlgebra α] {a b c : α}

@[simp]
theorem top_sdiff' (a : α) : ⊤ \ a = ￢a :=
  CoheytingAlgebra.top_sdiff _

@[simp]
theorem sdiff_top (a : α) : a \ ⊤ = ⊥ :=
  sdiff_eq_bot_iff.2 le_top

theorem hnot_inf_distrib (a b : α) : ￢(a⊓b) = ￢a⊔￢b := by
  simp_rw [← top_sdiff', sdiff_inf_distrib]

theorem sdiff_le_hnot : a \ b ≤ ￢b :=
  (sdiff_le_sdiff_right le_top).trans_eq <| top_sdiff' _

theorem sdiff_le_inf_hnot : a \ b ≤ a⊓￢b :=
  le_inf sdiff_le sdiff_le_hnot

-- See note [lower instance priority]
instance (priority := 100) CoheytingAlgebra.toDistribLattice : DistribLattice α :=
  { ‹CoheytingAlgebra α› with
    le_sup_inf := fun a b c => by
      simp_rw [← sdiff_le_iff, le_inf_iff, sdiff_le_iff, ← le_inf_iff] }

@[simp]
theorem hnot_sdiff (a : α) : ￢a \ a = ￢a := by
  rw [← top_sdiff', sdiff_sdiff, sup_idem]

theorem hnot_sdiff_comm (a b : α) : ￢a \ b = ￢b \ a := by
  simp_rw [← top_sdiff', sdiff_right_comm]

theorem hnot_le_iff_codisjoint_right : ￢a ≤ b ↔ Codisjoint a b := by
  rw [← top_sdiff', sdiff_le_iff, Codisjoint]

theorem hnot_le_iff_codisjoint_left : ￢a ≤ b ↔ Codisjoint b a :=
  hnot_le_iff_codisjoint_right.trans Codisjoint.comm

theorem hnot_le_comm : ￢a ≤ b ↔ ￢b ≤ a := by
  rw [hnot_le_iff_codisjoint_right, hnot_le_iff_codisjoint_left]

alias hnot_le_iff_codisjoint_right ↔ _ Codisjoint.hnot_le_right

alias hnot_le_iff_codisjoint_left ↔ _ Codisjoint.hnot_le_left

theorem codisjoint_hnot_right : Codisjoint a (￢a) :=
  sdiff_le_iff.1 (top_sdiff' _).le

theorem codisjoint_hnot_left : Codisjoint (￢a) a :=
  codisjoint_hnot_right.symm

@[simp]
theorem sup_hnot_self (a : α) : a⊔￢a = ⊤ :=
  codisjoint_hnot_right.eq_top

@[simp]
theorem hnot_sup_self (a : α) : ￢a⊔a = ⊤ :=
  codisjoint_hnot_left.eq_top

@[simp]
theorem hnot_bot : ￢(⊥ : α) = ⊤ :=
  eq_of_forall_ge_iffₓ fun a => by
    rw [hnot_le_iff_codisjoint_left, codisjoint_bot, top_le_iff]

@[simp]
theorem hnot_top : ￢(⊤ : α) = ⊥ := by
  rw [← top_sdiff', sdiff_self]

theorem hnot_hnot_le : ￢￢a ≤ a :=
  codisjoint_hnot_right.hnot_le_left

theorem hnot_anti : Antitone (hnot : α → α) := fun a b h => hnot_le_comm.1 <| hnot_hnot_le.trans h

theorem hnot_le_hnot (h : a ≤ b) : ￢b ≤ ￢a :=
  hnot_anti h

@[simp]
theorem hnot_hnot_hnot (a : α) : ￢￢￢a = ￢a :=
  hnot_hnot_le.antisymm <| hnot_anti hnot_hnot_le

@[simp]
theorem codisjoint_hnot_hnot_left_iff : Codisjoint (￢￢a) b ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_right, hnot_hnot_hnot]

@[simp]
theorem codisjoint_hnot_hnot_right_iff : Codisjoint a (￢￢b) ↔ Codisjoint a b := by
  simp_rw [← hnot_le_iff_codisjoint_left, hnot_hnot_hnot]

theorem le_hnot_inf_hnot : ￢(a⊔b) ≤ ￢a⊓￢b :=
  le_inf (hnot_anti le_sup_left) <| hnot_anti le_sup_right

theorem hnot_hnot_sup_distrib (a b : α) : ￢￢(a⊔b) = ￢￢a⊔￢￢b := by
  refine' ((hnot_inf_distrib _ _).Ge.trans <| hnot_anti le_hnot_inf_hnot).antisymm' _
  rw [hnot_le_iff_codisjoint_left, codisjoint_assoc, codisjoint_hnot_hnot_left_iff, codisjoint_left_comm,
    codisjoint_hnot_hnot_left_iff, ← codisjoint_assoc, sup_comm]
  exact codisjoint_hnot_right

theorem hnot_hnot_sdiff_distrib (a b : α) : ￢￢(a \ b) = ￢￢a \ ￢￢b := by
  refine' le_antisymmₓ _ _
  · refine' hnot_le_comm.1 ((hnot_anti sdiff_le_inf_hnot).trans' _)
    rw [hnot_inf_distrib, hnot_le_iff_codisjoint_right, codisjoint_left_comm, ← hnot_le_iff_codisjoint_right]
    exact le_sdiff_sup
    
  · rw [sdiff_le_iff, ← hnot_hnot_sup_distrib]
    exact hnot_anti (hnot_anti le_sup_sdiff)
    

instance : HeytingAlgebra αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.boundedOrder α with compl := to_dual ∘ hnot ∘ of_dual,
    himp := fun a b => toDual (ofDual b \ ofDual a),
    le_himp_iff := fun a b c => by
      rw [inf_comm]
      exact sdiff_le_iff,
    himp_bot := top_sdiff' }

@[simp]
theorem of_dual_compl (a : αᵒᵈ) : ofDual (aᶜ) = ￢ofDual a :=
  rfl

@[simp]
theorem of_dual_himp (a b : αᵒᵈ) : ofDual (a ⇨ b) = ofDual b \ ofDual a :=
  rfl

@[simp]
theorem to_dual_hnot (a : α) : toDual (￢a) = toDual aᶜ :=
  rfl

@[simp]
theorem to_dual_sdiff (a b : α) : toDual (a \ b) = toDual b ⇨ toDual a :=
  rfl

instance Prod.coheytingAlgebra [CoheytingAlgebra β] : CoheytingAlgebra (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.hasSdiff, Prod.hasHnot with
    sdiff_le_iff := fun a b c => and_congr sdiff_le_iff sdiff_le_iff,
    top_sdiff := fun a => Prod.extₓ (top_sdiff' a.1) (top_sdiff' a.2) }

instance Pi.coheytingAlgebra {α : ι → Type _} [∀ i, CoheytingAlgebra (α i)] : CoheytingAlgebra (∀ i, α i) := by
  pi_instance
  exact fun a b c => forall_congrₓ fun i => sdiff_le_iff

end CoheytingAlgebra

section BiheytingAlgebra

variable [BiheytingAlgebra α] {a : α}

theorem compl_le_hnot : aᶜ ≤ ￢a :=
  (disjoint_compl_left : Disjoint _ a).le_of_codisjoint codisjoint_hnot_right

end BiheytingAlgebra

-- ./././Mathport/Syntax/Translate/Expr.lean:219:4: warning: unsupported binary notation `«->»
/-- Propositions form a Heyting algebra with implication as Heyting implication and negation as
complement. -/
instance Prop.heytingAlgebra : HeytingAlgebra Prop :=
  { Prop.hasCompl, Prop.distribLattice, Prop.boundedOrder with himp := («->» · ·),
    le_himp_iff := fun p q r => and_imp.symm, himp_bot := fun p => rfl }

@[simp]
theorem himp_iff_imp (p q : Prop) : p ⇨ q ↔ p → q :=
  Iff.rfl

@[simp]
theorem compl_iff_not (p : Prop) : pᶜ ↔ ¬p :=
  Iff.rfl

-- See note [reducible non-instances]
/-- A bounded linear order is a bi-Heyting algebra by setting
* `a ⇨ b = ⊤` if `a ≤ b` and `a ⇨ b = b` otherwise.
* `a \ b = ⊥` if `a ≤ b` and `a \ b = a` otherwise. -/
@[reducible]
def LinearOrderₓ.toBiheytingAlgebra [LinearOrderₓ α] [BoundedOrder α] : BiheytingAlgebra α :=
  { LinearOrderₓ.toLattice, ‹BoundedOrder α› with himp := fun a b => if a ≤ b then ⊤ else b,
    compl := fun a => if a = ⊥ then ⊤ else ⊥,
    le_himp_iff := fun a b c => by
      change _ ≤ ite _ _ _ ↔ _
      split_ifs
      · exact iff_of_true le_top (inf_le_of_right_le h)
        
      · rw [inf_le_iff, or_iff_left h]
        ,
    himp_bot := fun a => if_congr le_bot_iff rfl rfl, sdiff := fun a b => if a ≤ b then ⊥ else a,
    hnot := fun a => if a = ⊤ then ⊥ else ⊤,
    sdiff_le_iff := fun a b c => by
      change ite _ _ _ ≤ _ ↔ _
      split_ifs
      · exact iff_of_true bot_le (le_sup_of_le_left h)
        
      · rw [le_sup_iff, or_iff_right h]
        ,
    top_sdiff := fun a => if_congr top_le_iff rfl rfl }

section lift

-- See note [reducible non-instances]
/-- Pullback a `generalized_heyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedHeytingAlgebra [HasSup α] [HasInf α] [HasTop α] [HasHimp α]
    [GeneralizedHeytingAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_top : f ⊤ = ⊤) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) :
    GeneralizedHeytingAlgebra α :=
  { hf.Lattice f map_sup map_inf, ‹HasTop α›, ‹HasHimp α› with
    le_top := fun a => by
      change f _ ≤ _
      rw [map_top]
      exact le_top,
    le_himp_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      erw [map_himp, map_inf, le_himp_iff] }

-- See note [reducible non-instances]
/-- Pullback a `generalized_coheyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.generalizedCoheytingAlgebra [HasSup α] [HasInf α] [HasBot α] [Sdiff α]
    [GeneralizedCoheytingAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_bot : f ⊥ = ⊥) (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) :
    GeneralizedCoheytingAlgebra α :=
  { hf.Lattice f map_sup map_inf, ‹HasBot α›, ‹Sdiff α› with
    bot_le := fun a => by
      change f _ ≤ _
      rw [map_bot]
      exact bot_le,
    sdiff_le_iff := fun a b c => by
      change f _ ≤ _ ↔ f _ ≤ _
      erw [map_sdiff, map_sup, sdiff_le_iff] }

-- See note [reducible non-instances]
/-- Pullback a `heyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.heytingAlgebra [HasSup α] [HasInf α] [HasTop α] [HasBot α] [HasCompl α] [HasHimp α]
    [HeytingAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f (aᶜ) = f aᶜ)
    (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b) : HeytingAlgebra α :=
  { hf.GeneralizedHeytingAlgebra f map_sup map_inf map_top map_himp, ‹HasBot α›, ‹HasCompl α› with
    bot_le := fun a => by
      change f _ ≤ _
      rw [map_bot]
      exact bot_le,
    himp_bot := fun a =>
      hf <| by
        erw [map_himp, map_compl, map_bot, himp_bot] }

-- See note [reducible non-instances]
/-- Pullback a `coheyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.coheytingAlgebra [HasSup α] [HasInf α] [HasTop α] [HasBot α] [HasHnot α] [Sdiff α]
    [CoheytingAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_hnot : ∀ a, f (￢a) = ￢f a)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : CoheytingAlgebra α :=
  { hf.GeneralizedCoheytingAlgebra f map_sup map_inf map_bot map_sdiff, ‹HasTop α›, ‹HasHnot α› with
    le_top := fun a => by
      change f _ ≤ _
      rw [map_top]
      exact le_top,
    top_sdiff := fun a =>
      hf <| by
        erw [map_sdiff, map_hnot, map_top, top_sdiff'] }

-- See note [reducible non-instances]
/-- Pullback a `biheyting_algebra` along an injection. -/
@[reducible]
protected def Function.Injective.biheytingAlgebra [HasSup α] [HasInf α] [HasTop α] [HasBot α] [HasCompl α] [HasHnot α]
    [HasHimp α] [Sdiff α] [BiheytingAlgebra β] (f : α → β) (hf : Injective f) (map_sup : ∀ a b, f (a⊔b) = f a⊔f b)
    (map_inf : ∀ a b, f (a⊓b) = f a⊓f b) (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) (map_compl : ∀ a, f (aᶜ) = f aᶜ)
    (map_hnot : ∀ a, f (￢a) = ￢f a) (map_himp : ∀ a b, f (a ⇨ b) = f a ⇨ f b)
    (map_sdiff : ∀ a b, f (a \ b) = f a \ f b) : BiheytingAlgebra α :=
  { hf.HeytingAlgebra f map_sup map_inf map_top map_bot map_compl map_himp,
    hf.CoheytingAlgebra f map_sup map_inf map_top map_bot map_hnot map_sdiff with }

end lift

namespace PUnit

variable (a b : PUnit.{u + 1})

instance : BiheytingAlgebra PUnit := by
  refine_struct
      { PUnit.linearOrder with top := star, bot := star, sup := fun _ _ => star, inf := fun _ _ => star,
        compl := fun _ => star, sdiff := fun _ _ => star, hnot := fun _ => star, himp := fun _ _ => star } <;>
    intros <;>
      first |
        trivial|
        exact Subsingleton.elimₓ _ _

@[simp]
theorem top_eq : (⊤ : PUnit) = star :=
  rfl

@[simp]
theorem bot_eq : (⊥ : PUnit) = star :=
  rfl

@[simp]
theorem sup_eq : a⊔b = star :=
  rfl

@[simp]
theorem inf_eq : a⊓b = star :=
  rfl

@[simp]
theorem compl_eq : aᶜ = star :=
  rfl

@[simp]
theorem sdiff_eq : a \ b = star :=
  rfl

@[simp, nolint simp_nf]
theorem hnot_eq : ￢a = star :=
  rfl

-- eligible for `dsimp`
@[simp]
theorem himp_eq : a ⇨ b = star :=
  rfl

end PUnit

