/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathbin.Order.SymmDiff
import Mathbin.Logic.Function.Iterate

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coercion from `set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the file `set_theory/zfc.lean`, which contains an encoding of ZFC set theory in Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : set α` and `s₁ s₂ : set α` are subsets of `α`

-  `t : set β` is a subset of `β`.

Definitions in the file:

* `nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `nontrivial s : Prop` : the predicate saying that `s` has at least two distinct elements.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `f ⁻¹' t` for `preimage f t`

* `f '' s` for `image f s`

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.nonempty` dot notation can be used.

* For `s : set α`, do not use `subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, image, preimage, pre-image, range, union, intersection, insert,
singleton, complement, powerset

-/


/-! ### Set coercion to a type -/


open Function

universe u v w x

namespace Set

variable {α : Type _} {s t : Set α}

instance : LE (Set α) :=
  ⟨fun s t => ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance {α : Type _} : BooleanAlgebra (Set α) :=
  { (inferInstance : BooleanAlgebra (α → Prop)) with sup := fun s t => { x | x ∈ s ∨ x ∈ t }, le := (· ≤ ·),
    lt := fun s t => s ⊆ t ∧ ¬t ⊆ s, inf := fun s t => { x | x ∈ s ∧ x ∈ t }, bot := ∅, compl := fun s => { x | x ∉ s },
    top := Univ, sdiff := fun s t => { x | x ∈ s ∧ x ∉ t } }

instance : HasSSubset (Set α) :=
  ⟨(· < ·)⟩

instance : Union (Set α) :=
  ⟨(· ⊔ ·)⟩

instance : Inter (Set α) :=
  ⟨(· ⊓ ·)⟩

@[simp]
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl

@[simp]
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl

@[simp]
theorem sup_eq_union : ((· ⊔ ·) : Set α → Set α → Set α) = (· ∪ ·) :=
  rfl

@[simp]
theorem inf_eq_inter : ((· ⊓ ·) : Set α → Set α → Set α) = (· ∩ ·) :=
  rfl

@[simp]
theorem le_eq_subset : ((· ≤ ·) : Set α → Set α → Prop) = (· ⊆ ·) :=
  rfl

@[simp]
theorem lt_eq_ssubset : ((· < ·) : Set α → Set α → Prop) = (· ⊂ ·) :=
  rfl

theorem le_iff_subset : s ≤ t ↔ s ⊆ t :=
  Iff.rfl

theorem lt_iff_ssubset : s < t ↔ s ⊂ t :=
  Iff.rfl

alias le_iff_subset ↔ _root_.has_le.le.subset _root_.has_subset.subset.le

alias lt_iff_ssubset ↔ _root_.has_lt.lt.ssubset _root_.has_ssubset.ssubset.lt

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Set α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

instance PiSetCoe.canLift (ι : Type u) (α : ∀ i : ι, Type v) [ne : ∀ i, Nonempty (α i)] (s : Set ι) :
    CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α s

instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [ne : Nonempty α] (s : Set ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSetCoe.canLift ι (fun _ => α) s

end Set

section SetCoe

variable {α : Type u}

theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x ∈ s } :=
  rfl

@[simp]
theorem Set.coe_set_of (p : α → Prop) : ↥{ x | p x } = { x // p x } :=
  rfl

@[simp]
theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ (x) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall

@[simp]
theorem SetCoe.exists {s : Set α} {p : s → Prop} : (∃ x : s, p x) ↔ ∃ (x : _)(h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists

theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} : (∃ (x : _)(h : x ∈ s), p x h) ↔ ∃ x : s, p x x.2 :=
  ((@SetCoe.exists _ _) fun x => p x.1 x.2).symm

theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} : (∀ (x) (h : x ∈ s), p x h) ↔ ∀ x : s, p x x.2 :=
  ((@SetCoe.forall _ _) fun x => p x.1 x.2).symm

@[simp]
theorem set_coe_cast : ∀ {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | s, _, rfl, _, ⟨x, h⟩ => rfl

theorem SetCoe.ext {s : Set α} {a b : s} : (↑a : α) = ↑b → a = b :=
  Subtype.eq

theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl

end SetCoe

/-- See also `subtype.prop` -/
theorem Subtype.mem {α : Type _} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.Prop

/-- Duplicate of `eq.subset'`, which currently has elaboration problems. -/
theorem Eq.subset {α} {s t : Set α} : s = t → s ⊆ t :=
  Eq.subset'

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a b : α} {s t u : Set α}

instance : Inhabited (Set α) :=
  ⟨∅⟩

@[ext]
theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext fun x => propext (h x)

theorem ext_iff {s t : Set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
  ⟨fun h x => by rw [h], ext⟩

@[trans]
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx

theorem forall_in_swap {p : α → β → Prop} : (∀ a ∈ s, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ s, p a b := by tauto

/-! ### Lemmas about `mem` and `set_of` -/


theorem mem_set_of {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a :=
  Iff.rfl

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
theorem _root_.has_mem.mem.out {p : α → Prop} {a : α} (h : a ∈ { x | p x }) : p a :=
  h

theorem nmem_set_of_iff {a : α} {p : α → Prop} : a ∉ { x | p x } ↔ ¬p a :=
  Iff.rfl

@[simp]
theorem set_of_mem_eq {s : Set α} : { x | x ∈ s } = s :=
  rfl

theorem set_of_set {s : Set α} : SetOf s = s :=
  rfl

theorem set_of_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x :=
  Iff.rfl

theorem mem_def {a : α} {s : Set α} : a ∈ s ↔ s a :=
  Iff.rfl

theorem set_of_bijective : Bijective (SetOf : (α → Prop) → Set α) :=
  bijective_id

@[simp]
theorem set_of_subset_set_of {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl

theorem set_of_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl

theorem set_of_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl

/-! ### Subset and strict subset relations -/


instance : IsRefl (Set α) (· ⊆ ·) :=
  LE.le.is_refl

instance : IsTrans (Set α) (· ⊆ ·) :=
  LE.le.is_trans

instance : IsAntisymm (Set α) (· ⊆ ·) :=
  LE.le.is_antisymm

instance : IsIrrefl (Set α) (· ⊂ ·) :=
  LT.lt.is_irrefl

instance : IsTrans (Set α) (· ⊂ ·) :=
  LT.lt.is_trans

instance : IsAsymm (Set α) (· ⊂ ·) :=
  LT.lt.is_asymm

instance : IsNonstrictStrictOrder (Set α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬t ⊆ s) :=
  rfl

@[refl]
theorem Subset.refl (a : Set α) : a ⊆ a := fun x => id

theorem Subset.rfl {s : Set α} : s ⊆ s :=
  Subset.refl s

@[trans]
theorem Subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c := fun x h => bc <| ab h

@[trans]
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
  hx.symm ▸ h

theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  Set.ext fun x => ⟨@h₁ _, @h₂ _⟩

theorem Subset.antisymm_iff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨e.Subset, e.symm.Subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩

-- an alternative name
theorem eq_of_subset_of_subset {a b : Set α} : a ⊆ b → b ⊆ a → a = b :=
  subset.antisymm

theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
  @h _

theorem not_mem_subset (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| mem_of_subset_of_mem h

theorem not_subset : ¬s ⊆ t ↔ ∃ a ∈ s, a ∉ t := by simp only [subset_def, not_forall]

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/


protected theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h

theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset.1 h.2

protected theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne (Set α) _ s t

theorem ssubset_iff_of_subset {s t : Set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
  ⟨exists_of_ssubset, fun ⟨x, hxt, hxs⟩ => ⟨h, fun h => hxs <| h hxt⟩⟩

protected theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩

protected theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩

theorem not_mem_empty (x : α) : ¬x ∈ (∅ : Set α) :=
  id

@[simp]
theorem not_not_mem : ¬a ∉ s ↔ a ∈ s :=
  not_not

/-! ### Non-empty sets -/


/-- The property `s.nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s

@[simp]
theorem nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype

alias nonempty_coe_sort ↔ _ nonempty.coe_sort

theorem nonempty_def : s.Nonempty ↔ ∃ x, x ∈ s :=
  Iff.rfl

theorem nonempty_of_mem {x} (h : x ∈ s) : s.Nonempty :=
  ⟨x, h⟩

theorem Nonempty.not_subset_empty : s.Nonempty → ¬s ⊆ ∅
  | ⟨x, hx⟩, hs => hs hx

theorem Nonempty.ne_empty : ∀ {s : Set α}, s.Nonempty → s ≠ ∅
  | _, ⟨x, hx⟩, rfl => hx

@[simp]
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun h => h.ne_empty rfl

/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected noncomputable def Nonempty.some (h : s.Nonempty) : α :=
  Classical.choose h

protected theorem Nonempty.some_mem (h : s.Nonempty) : h.some ∈ s :=
  Classical.choose_spec h

theorem Nonempty.mono (ht : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  hs.imp ht

theorem nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩

theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2

theorem Nonempty.of_diff (h : (s \ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty :=
  (nonempty_of_ssubset ht).of_diff

theorem Nonempty.inl (hs : s.Nonempty) : (s ∪ t).Nonempty :=
  hs.imp fun _ => Or.inl

theorem Nonempty.inr (ht : t.Nonempty) : (s ∪ t).Nonempty :=
  ht.imp fun _ => Or.inr

@[simp]
theorem union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  exists_or

theorem Nonempty.left (h : (s ∩ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left

theorem Nonempty.right (h : (s ∩ t).Nonempty) : t.Nonempty :=
  h.imp fun _ => And.right

theorem inter_nonempty : (s ∩ t).Nonempty ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Iff.rfl

theorem inter_nonempty_iff_exists_left : (s ∩ t).Nonempty ↔ ∃ x ∈ s, x ∈ t := by simp_rw [inter_nonempty, exists_prop]

theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, exists_prop, and_comm']

theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (Univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]
theorem univ_nonempty : ∀ [h : Nonempty α], (Univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩

theorem Nonempty.to_subtype (h : s.Nonempty) : Nonempty s :=
  nonempty_subtype.2 h

instance [Nonempty α] : Nonempty (Set.Univ : Set α) :=
  Set.univ_nonempty.to_subtype

theorem nonempty_of_nonempty_subtype [Nonempty s] : s.Nonempty :=
  nonempty_subtype.mp ‹_›

/-! ### Lemmas about the empty set -/


theorem empty_def : (∅ : Set α) = { x | False } :=
  rfl

@[simp]
theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  Iff.rfl

@[simp]
theorem set_of_false : { a : α | False } = ∅ :=
  rfl

@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  fun.

theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ s = ∅ :=
  (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm

theorem eq_empty_iff_forall_not_mem {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  subset_empty_iff.symm

theorem eq_empty_of_forall_not_mem (h : ∀ x, x ∉ s) : s = ∅ :=
  subset_empty_iff.1 h

theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ :=
  subset_empty_iff.1

theorem eq_empty_of_is_empty [IsEmpty α] (s : Set α) : s = ∅ :=
  eq_empty_of_subset_empty fun x hx => isEmptyElim x

/-- There is exactly one set of a type that is empty. -/
instance uniqueEmpty [IsEmpty α] : Unique (Set α) where
  default := ∅
  uniq := eq_empty_of_is_empty

theorem not_nonempty_iff_eq_empty {s : Set α} : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, eq_empty_iff_forall_not_mem, not_exists]

theorem empty_not_nonempty : ¬(∅ : Set α).Nonempty := fun h => h.ne_empty rfl

theorem ne_empty_iff_nonempty : s ≠ ∅ ↔ s.Nonempty :=
  not_iff_comm.1 not_nonempty_iff_eq_empty

@[simp]
theorem is_empty_coe_sort {s : Set α} : IsEmpty ↥s ↔ s = ∅ :=
  not_iff_not.1 <| by simpa using ne_empty_iff_nonempty.symm

theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 ne_empty_iff_nonempty.1

theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1 <| e ▸ h

theorem ball_empty_iff {p : α → Prop} : (∀ x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun x => False.elim

instance (α : Type u) : IsEmpty.{u + 1} (∅ : Set α) :=
  ⟨fun x => x.2⟩

@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Set α) _ _ _).trans ne_empty_iff_nonempty

/-!

### Universal set.

In Lean `@univ α` (or `univ : set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp]
theorem set_of_true : { x : α | True } = univ :=
  rfl

@[simp]
theorem mem_univ (x : α) : x ∈ @Univ α :=
  trivial

@[simp]
theorem univ_eq_empty_iff : (Univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_not_mem.trans ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩

theorem empty_ne_univ [Nonempty α] : (∅ : Set α) ≠ univ := fun e =>
  not_is_empty_of_nonempty α <| univ_eq_empty_iff.1 e.symm

@[simp]
theorem subset_univ (s : Set α) : s ⊆ univ := fun x H => trivial

theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s

alias univ_subset_iff ↔ eq_univ_of_univ_subset _

theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun x => imp_iff_right trivial

theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ := by
  rintro ⟨x, hx⟩
  refine' eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]

theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset <| hs ▸ h

theorem exists_mem_of_nonempty (α) : ∀ [Nonempty α], ∃ x : α, x ∈ (Univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩

theorem ne_univ_iff_exists_not_mem {α : Type _} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s := by
  rw [← not_forall, ← eq_univ_iff_forall]

theorem not_subset_iff_exists_mem_not_mem {α : Type _} {s t : Set α} : ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t := by
  simp [subset_def]

theorem univ_unique [Unique α] : @Set.Univ α = {default} :=
  Set.ext fun x => iff_of_true trivial <| Subsingleton.elim x default

theorem ssubset_univ_iff : s ⊂ univ ↔ s ≠ univ :=
  lt_top_iff_ne_top

instance nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α) :=
  ⟨⟨∅, Univ, empty_ne_univ⟩⟩

/-! ### Lemmas about union -/


theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ } :=
  rfl

theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x ∈ a → x ∈ a ∪ b :=
  Or.inl

theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x ∈ b → x ∈ a ∪ b :=
  Or.inr

theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b :=
  H

theorem MemUnion.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
  Or.elim H₁ H₂ H₃

@[simp]
theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  Iff.rfl

@[simp]
theorem union_self (a : Set α) : a ∪ a = a :=
  ext fun x => or_self_iff _

@[simp]
theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  ext fun x => or_false_iff _

@[simp]
theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  ext fun x => false_or_iff _

theorem union_comm (a b : Set α) : a ∪ b = b ∪ a :=
  ext fun x => or_comm

theorem union_assoc (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext fun x => or_assoc

instance union_is_assoc : IsAssociative (Set α) (· ∪ ·) :=
  ⟨union_assoc⟩

instance union_is_comm : IsCommutative (Set α) (· ∪ ·) :=
  ⟨union_comm⟩

theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext fun x => or_left_comm

theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext fun x => or_right_comm

@[simp]
theorem union_eq_left_iff_subset {s t : Set α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left

@[simp]
theorem union_eq_right_iff_subset {s t : Set α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right

theorem union_eq_self_of_subset_left {s t : Set α} (h : s ⊆ t) : s ∪ t = t :=
  union_eq_right_iff_subset.mpr h

theorem union_eq_self_of_subset_right {s t : Set α} (h : t ⊆ s) : s ∪ t = s :=
  union_eq_left_iff_subset.mpr h

@[simp]
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := fun x => Or.inl

@[simp]
theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t := fun x => Or.inr

theorem union_subset {s t r : Set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r := fun x => Or.ndrec (@sr _) (@tr _)

@[simp]
theorem union_subset_iff {s t u : Set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (forall_congr' fun x => or_imp).trans forall_and

theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun x =>
  Or.imp (@h₁ _) (@h₂ _)

theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl

theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h

theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_left t u)

theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_right t u)

theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ⊔ u :=
  sup_congr_left ht hu

theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht

theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left

theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right

@[simp]
theorem union_empty_iff {s t : Set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := by
  simp only [← subset_empty_iff] <;> exact union_subset_iff

@[simp]
theorem union_univ {s : Set α} : s ∪ univ = univ :=
  sup_top_eq

@[simp]
theorem univ_union {s : Set α} : univ ∪ s = univ :=
  top_sup_eq

/-! ### Lemmas about intersection -/


theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ } :=
  rfl

@[simp]
theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  Iff.rfl

theorem mem_inter {x : α} {a b : Set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
  ⟨ha, hb⟩

theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ a :=
  h.left

theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ b :=
  h.right

@[simp]
theorem inter_self (a : Set α) : a ∩ a = a :=
  ext fun x => and_self_iff _

@[simp]
theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  ext fun x => and_false_iff _

@[simp]
theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  ext fun x => false_and_iff _

theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a :=
  ext fun x => and_comm

theorem inter_assoc (a b c : Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext fun x => and_assoc

instance inter_is_assoc : IsAssociative (Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩

instance inter_is_comm : IsCommutative (Set α) (· ∩ ·) :=
  ⟨inter_comm⟩

theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun x => and_left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun x => and_right_comm

@[simp]
theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s := fun x => And.left

@[simp]
theorem inter_subset_right (s t : Set α) : s ∩ t ⊆ t := fun x => And.right

theorem subset_inter {s t r : Set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t := fun x h => ⟨rs h, rt h⟩

@[simp]
theorem subset_inter_iff {s t r : Set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  (forall_congr' fun x => imp_and).trans forall_and

@[simp]
theorem inter_eq_left_iff_subset {s t : Set α} : s ∩ t = s ↔ s ⊆ t :=
  inf_eq_left

@[simp]
theorem inter_eq_right_iff_subset {s t : Set α} : s ∩ t = t ↔ t ⊆ s :=
  inf_eq_right

theorem inter_eq_self_of_subset_left {s t : Set α} : s ⊆ t → s ∩ t = s :=
  inter_eq_left_iff_subset.mpr

theorem inter_eq_self_of_subset_right {s t : Set α} : t ⊆ s → s ∩ t = t :=
  inter_eq_right_iff_subset.mpr

theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu

theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht

theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left

theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right

@[simp]
theorem inter_univ (a : Set α) : a ∩ univ = a :=
  inf_top_eq

@[simp]
theorem univ_inter (a : Set α) : univ ∩ a = a :=
  top_inf_eq

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun x =>
  And.imp (@h₁ _) (@h₂ _)

theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H Subset.rfl

theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter Subset.rfl H

theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right <| subset_union_left _ _

theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right <| subset_union_right _ _

/-! ### Distributivity laws -/


theorem inter_distrib_left (s t u : Set α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left

theorem inter_union_distrib_left {s t u : Set α} : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left

theorem inter_distrib_right (s t u : Set α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right

theorem union_inter_distrib_right {s t u : Set α} : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right

theorem union_distrib_left (s t u : Set α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left

theorem union_inter_distrib_left {s t u : Set α} : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left

theorem union_distrib_right (s t u : Set α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right

theorem inter_union_distrib_right {s t u : Set α} : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right

theorem union_union_distrib_left (s t u : Set α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _

theorem union_union_distrib_right (s t u : Set α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _

theorem inter_inter_distrib_left (s t u : Set α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _

theorem inter_inter_distrib_right (s t u : Set α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _

theorem union_union_union_comm (s t u v : Set α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _

theorem inter_inter_inter_comm (s t u v : Set α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/


theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl

@[simp]
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s := fun y => Or.inr

theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
  Or.inl rfl

theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr

theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
  id

theorem mem_of_mem_insert_of_ne : b ∈ insert a s → b ≠ a → b ∈ s :=
  Or.resolve_left

theorem eq_of_not_mem_of_mem_insert : b ∈ insert a s → b ∉ s → b = a :=
  Or.resolve_right

@[simp]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl

@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s :=
  ext fun x => or_iff_right_of_imp fun e => e.symm ▸ h

theorem ne_insert_of_not_mem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t :=
  mt fun e => e.symm ▸ mem_insert _ _

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert _ _, insert_eq_of_mem⟩

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.Not

theorem insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, or_imp, forall_and, forall_eq, mem_insert_iff]

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := fun x => Or.imp_right (@h _)

theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  refine' ⟨fun h x hx => _, insert_subset_insert⟩
  rcases h (subset_insert _ _ hx) with (rfl | hxt)
  exacts[(ha hx).elim, hxt]

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (a «expr ∉ » s) -/
theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ (a : _)(_ : a ∉ s), insert a s ⊆ t := by
  simp only [insert_subset, exists_and_right, ssubset_def, not_subset]
  simp only [exists_prop, and_comm']

theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff_insert.2 ⟨a, h, Subset.rfl⟩

theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => or_left_comm

@[simp]
theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s :=
  insert_eq_of_mem <| mem_insert _ _

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
  ext fun x => or_assoc

@[simp]
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
  ext fun x => or_left_comm

@[simp]
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

theorem insert_inter_distrib (a : α) (s t : Set α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
  ext fun y => or_and_left

theorem insert_union_distrib (a : α) (s t : Set α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
  ext fun _ => or_or_distrib_left _ _ _

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert a s) ha, congr_arg _⟩

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x) (x) (h : x ∈ s) :
    P x :=
  H _ (Or.inr h)

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a) (x)
    (h : x ∈ insert a s) : P x :=
  h.elim (fun e => e.symm ▸ ha) (H _)

theorem bex_insert_iff {P : α → Prop} {a : α} {s : Set α} : (∃ x ∈ insert a s, P x) ↔ P a ∨ ∃ x ∈ s, P x :=
  bex_or_left.trans <| or_congr_left bex_eq_left

theorem ball_insert_iff {P : α → Prop} {a : α} {s : Set α} : (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x :=
  ball_or_left.trans <| and_congr_left' forall_eq

/-! ### Lemmas about singletons -/


theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_emptyc_eq _).symm

@[simp]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl

@[simp]
theorem set_of_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl

@[simp]
theorem set_of_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun x => eq_comm

-- TODO: again, annotation needed
@[simp]
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
  @rfl _ _

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h

@[simp]
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  ext_iff.trans eq_iff_eq_cancel_left

theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ => singleton_eq_singleton_iff.mp

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
  H

theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) ∪ s :=
  rfl

@[simp]
theorem singleton_nonempty (a : α) : ({a} : Set α).Nonempty :=
  ⟨a, rfl⟩

@[simp]
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq

theorem set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a} :=
  rfl

@[simp]
theorem singleton_union : {a} ∪ s = insert a s :=
  rfl

@[simp]
theorem union_singleton : s ∪ {a} = insert a s :=
  union_comm _ _

@[simp]
theorem singleton_inter_nonempty : ({a} ∩ s).Nonempty ↔ a ∈ s := by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp]
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s := by rw [inter_comm, singleton_inter_nonempty]

@[simp]
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.Not

@[simp]
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s := by rw [inter_comm, singleton_inter_eq_empty]

theorem nmem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  ne_empty_iff_nonempty

instance uniqueSingleton (a : α) : Unique ↥({a} : Set α) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨x, h⟩ => Subtype.eq h⟩

theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  Subset.antisymm_iff.trans <| and_comm.trans <| and_congr_left' singleton_subset_iff

theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans <| and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl

/-! ### Lemmas about pairs -/


@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _

theorem pair_eq_pair_iff {x y z w : α} : ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp only [Set.Subset.antisymm_iff, Set.insert_subset, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.singleton_subset_iff]
  constructor
  · tauto!
    
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
    

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/


section Sep

variable {p q : α → Prop} {x : α}

theorem mem_sep (xs : x ∈ s) (px : p x) : x ∈ { x ∈ s | p x } :=
  ⟨xs, px⟩

@[simp]
theorem sep_mem_eq : { x ∈ s | x ∈ t } = s ∩ t :=
  rfl

@[simp]
theorem mem_sep_iff : x ∈ { x ∈ s | p x } ↔ x ∈ s ∧ p x :=
  Iff.rfl

theorem sep_ext_iff : { x ∈ s | p x } = { x ∈ s | q x } ↔ ∀ x ∈ s, p x ↔ q x := by
  simp_rw [ext_iff, mem_sep_iff, and_congr_right_iff]

theorem sep_eq_of_subset (h : s ⊆ t) : { x ∈ t | x ∈ s } = s :=
  inter_eq_self_of_subset_right h

@[simp]
theorem sep_subset (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ s := fun x => And.left

@[simp]
theorem sep_eq_self_iff_mem_true : { x ∈ s | p x } = s ↔ ∀ x ∈ s, p x := by
  simp_rw [ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp]
theorem sep_eq_empty_iff_mem_false : { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x := by
  simp_rw [ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false_iff, not_and]

@[simp]
theorem sep_true : { x ∈ s | True } = s :=
  inter_univ s

@[simp]
theorem sep_false : { x ∈ s | False } = ∅ :=
  inter_empty s

@[simp]
theorem sep_empty (p : α → Prop) : { x ∈ (∅ : Set α) | p x } = ∅ :=
  empty_inter p

@[simp]
theorem sep_univ : { x ∈ (Univ : Set α) | p x } = { x | p x } :=
  univ_inter p

@[simp]
theorem sep_union : { x ∈ s ∪ t | p x } = { x ∈ s | p x } ∪ { x ∈ t | p x } :=
  union_inter_distrib_right

@[simp]
theorem sep_inter : { x ∈ s ∩ t | p x } = { x ∈ s | p x } ∩ { x ∈ t | p x } :=
  inter_inter_distrib_right s t p

@[simp]
theorem sep_and : { x ∈ s | p x ∧ q x } = { x ∈ s | p x } ∩ { x ∈ s | q x } :=
  inter_inter_distrib_left s p q

@[simp]
theorem sep_or : { x ∈ s | p x ∨ q x } = { x ∈ s | p x } ∪ { x ∈ s | q x } :=
  inter_union_distrib_left

@[simp]
theorem sep_set_of : { x ∈ { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl

end Sep

@[simp]
theorem subset_singleton_iff {α : Type _} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl

theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  use ⟨fun _ => Or.inl rfl, fun _ => empty_subset _⟩
  simp [eq_singleton_iff_nonempty_unique_mem, hs, ne_empty_iff_nonempty.2 hs]

theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty

theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ := by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false_iff,
    and_iff_left_iff_imp]
  rintro rfl
  refine' ne_comm.1 (ne_empty_iff_nonempty.2 (singleton_nonempty _))

theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/-! ### Disjointness -/


protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  Iff.rfl

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

theorem _root_.disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot

theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  forall_congr' fun _ => not_and

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [Disjoint.comm, disjoint_left]

/-! ### Lemmas about complement -/


theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl

theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h

theorem compl_set_of {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl

theorem not_mem_of_mem_compl {s : Set α} {x : α} (h : x ∈ sᶜ) : x ∉ s :=
  h

@[simp]
theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s :=
  Iff.rfl

theorem not_mem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not

@[simp]
theorem inter_compl_self (s : Set α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
theorem compl_inter_self (s : Set α) : sᶜ ∩ s = ∅ :=
  compl_inf_eq_bot

@[simp]
theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  compl_bot

@[simp]
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup

theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf

@[simp]
theorem compl_univ : (Univ : Set α)ᶜ = ∅ :=
  compl_top

@[simp]
theorem compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
theorem compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top

theorem compl_ne_univ : sᶜ ≠ univ ↔ s.Nonempty :=
  compl_univ_iff.Not.trans ne_empty_iff_nonempty

theorem nonempty_compl {s : Set α} : sᶜ.Nonempty ↔ s ≠ univ :=
  (ne_univ_iff_exists_not_mem s).symm

theorem mem_compl_singleton_iff {a x : α} : x ∈ ({a} : Set α)ᶜ ↔ x ≠ a :=
  Iff.rfl

theorem compl_singleton_eq (a : α) : ({a} : Set α)ᶜ = { x | x ≠ a } :=
  rfl

@[simp]
theorem compl_ne_eq_singleton (a : α) : ({ x | x ≠ a } : Set α)ᶜ = {a} :=
  compl_compl _

theorem union_eq_compl_compl_inter_compl (s t : Set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
  ext fun x => or_iff_not_and_not

theorem inter_eq_compl_compl_union_compl (s t : Set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
  ext fun x => and_iff_not_or_not

@[simp]
theorem union_compl_self (s : Set α) : s ∪ sᶜ = univ :=
  eq_univ_iff_forall.2 fun x => em _

@[simp]
theorem compl_union_self (s : Set α) : sᶜ ∪ s = univ := by rw [union_comm, union_compl_self]

theorem compl_subset_comm : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
  @compl_le_iff_compl_le _ s _ _

theorem subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ :=
  @le_compl_iff_le_compl _ _ _ t

@[simp]
theorem compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s :=
  @compl_le_compl_iff_le (Set α) _ _ _

theorem subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s :=
  @le_compl_iff_disjoint_left (Set α) _ _ _

theorem subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t :=
  @le_compl_iff_disjoint_right (Set α) _ _ _

theorem disjoint_compl_left_iff_subset : Disjoint (sᶜ) t ↔ t ⊆ s :=
  disjoint_compl_left_iff

theorem disjoint_compl_right_iff_subset : Disjoint s (tᶜ) ↔ s ⊆ t :=
  disjoint_compl_right_iff

alias subset_compl_iff_disjoint_right ↔ _ _root_.disjoint.subset_compl_right

alias subset_compl_iff_disjoint_left ↔ _ _root_.disjoint.subset_compl_left

alias disjoint_compl_left_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_left

alias disjoint_compl_right_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_right

theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
  (@isComplCompl _ u _).le_sup_right_iff_inf_left_le

theorem compl_subset_iff_union {s t : Set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
  Iff.symm <| eq_univ_iff_forall.trans <| forall_congr' fun a => or_iff_not_imp_left

@[simp]
theorem subset_compl_singleton_iff {a : α} {s : Set α} : s ⊆ {a}ᶜ ↔ a ∉ s :=
  subset_compl_comm.trans singleton_subset_iff

theorem inter_subset (a b c : Set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
  forall_congr' fun x => and_imp.trans <| imp_congr_right fun _ => imp_iff_not_or

theorem inter_compl_nonempty_iff {s t : Set α} : (s ∩ tᶜ).Nonempty ↔ ¬s ⊆ t :=
  (not_subset.trans <| exists_congr fun x => by simp [mem_compl]).symm

/-! ### Lemmas about set difference -/


theorem diff_eq (s t : Set α) : s \ t = s ∩ tᶜ :=
  rfl

@[simp]
theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
  ⟨h1, h2⟩

theorem not_mem_diff_of_mem {s t : Set α} {x : α} (hx : x ∈ t) : x ∉ s \ t := fun h => h.2 hx

theorem mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left

theorem not_mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right

theorem diff_eq_compl_inter {s t : Set α} : s \ t = tᶜ ∩ s := by rw [diff_eq, inter_comm]

theorem nonempty_diff {s t : Set α} : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff

theorem diff_subset (s t : Set α) : s \ t ⊆ s :=
  show s \ t ≤ s from sdiff_le

theorem union_diff_cancel' {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sup_sdiff_cancel' h₁ h₂

theorem union_diff_cancel {s t : Set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h

theorem union_diff_cancel_left {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
  Disjoint.sup_sdiff_cancel_left h

theorem union_diff_cancel_right {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
  Disjoint.sup_sdiff_cancel_right h

@[simp]
theorem union_diff_left {s t : Set α} : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self

@[simp]
theorem union_diff_right {s t : Set α} : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

theorem union_diff_distrib {s t u : Set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
  sup_sdiff

theorem inter_diff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
  inf_sdiff_assoc

@[simp]
theorem inter_diff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right

@[simp]
theorem inter_union_diff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t

@[simp]
theorem diff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s := by
  rw [union_comm]
  exact sup_inf_sdiff _ _

@[simp]
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ tᶜ = s :=
  inter_union_diff _ _

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂ from sdiff_le_sdiff

theorem diff_subset_diff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
  sdiff_le_sdiff_right ‹s₁ ≤ s₂›

theorem diff_subset_diff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
  sdiff_le_sdiff_left ‹t ≤ u›

theorem compl_eq_univ_diff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm

@[simp]
theorem empty_diff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff

theorem diff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[simp]
theorem diff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot

@[simp]
theorem diff_univ (s : Set α) : s \ univ = ∅ :=
  diff_eq_empty.2 (subset_univ s)

theorem diff_diff {u : Set α} : (s \ t) \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left

-- the following statement contains parentheses to help the reader
theorem diff_diff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  sdiff_sdiff_comm

theorem diff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  show s \ t ≤ u ↔ s ≤ t ∪ u from sdiff_le_iff

theorem subset_diff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  show s ≤ s \ t ∪ t from le_sdiff_sup

theorem diff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  Subset.antisymm (union_subset (diff_subset _ _) h) (subset_diff_union _ _)

@[simp]
theorem diff_singleton_subset_iff {x : α} {s t : Set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t := by
  rw [← union_singleton, union_comm]
  apply diff_subset_iff

theorem subset_diff_singleton {x : α} {s t : Set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 hx

theorem subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by rw [← diff_singleton_subset_iff]

theorem diff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  show s \ t ≤ u ↔ s \ u ≤ t from sdiff_le_comm

theorem diff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

theorem diff_inter_diff {s t u : Set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm

theorem diff_compl : s \ tᶜ = s ∩ t :=
  sdiff_compl

theorem diff_diff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'

@[simp]
theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t := by
  ext
  constructor <;> simp (config := { contextual := true }) [or_imp, h]

theorem insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  classical
  ext x
  by_cases h':x ∈ t
  · have : x ≠ a := by
      intro H
      rw [H] at h'
      exact h h'
    simp [h, h', this]
    
  · simp [h, h']
    

theorem insert_diff_self_of_not_mem {a : α} {s : Set α} (h : a ∉ s) : insert a s \ {a} = s := by
  ext
  simp [and_iff_left_of_imp fun hx : x ∈ s => show x ≠ a from fun hxa => h <| hxa ▸ hx]

@[simp]
theorem insert_diff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} := by
  ext
  rw [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, and_not_self_iff, or_false_iff,
    and_iff_left_iff_imp]
  rintro rfl
  exact h

theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]

theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]

theorem inter_insert_of_not_mem (h : a ∉ s) : s ∩ insert a t = s ∩ t :=
  ext fun x => and_congr_right fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h

theorem insert_inter_of_not_mem (h : a ∉ t) : insert a s ∩ t = s ∩ t :=
  ext fun x => and_congr_left fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h

@[simp]
theorem union_diff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self _ _

@[simp]
theorem diff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sdiff_sup_self _ _

@[simp]
theorem diff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left

@[simp]
theorem diff_inter_self_eq_diff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _

@[simp]
theorem diff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _

@[simp]
theorem diff_eq_self {s t : Set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
  show s \ t = s ↔ t ⊓ s ≤ ⊥ from sdiff_eq_self_iff_disjoint

@[simp]
theorem diff_singleton_eq_self {a : α} {s : Set α} (h : a ∉ s) : s \ {a} = s :=
  diff_eq_self.2 <| by simp [singleton_inter_eq_empty.2 h]

@[simp]
theorem insert_diff_singleton {a : α} {s : Set α} : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp]
theorem diff_self {s : Set α} : s \ s = ∅ :=
  sdiff_self

theorem diff_diff_right_self (s t : Set α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self

theorem diff_diff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h

theorem mem_diff_singleton {x y : α} {s : Set α} : x ∈ s \ {y} ↔ x ∈ s ∧ x ≠ y :=
  Iff.rfl

theorem mem_diff_singleton_empty {s : Set α} {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_diff_singleton.trans <| Iff.rfl.And ne_empty_iff_nonempty

theorem union_eq_diff_union_diff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

/-! ### Symmetric difference -/


theorem mem_symm_diff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s :=
  Iff.rfl

theorem symm_diff_subset_union : s ∆ t ⊆ s ∪ t :=
  @symm_diff_le_sup (Set α) _ _ _

theorem inter_symm_diff_distrib_left (s t u : Set α) : s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u) :=
  inf_symm_diff_distrib_left _ _ _

theorem inter_symm_diff_distrib_right (s t u : Set α) : s ∆ t ∩ u = (s ∩ u) ∆ (t ∩ u) :=
  inf_symm_diff_distrib_right _ _ _

/-! ### Powerset -/


/-- `𝒫 s = set.powerset s` is the set of all subsets of `s`. -/
def Powerset (s : Set α) : Set (Set α) :=
  { t | t ⊆ s }

theorem mem_powerset {x s : Set α} (h : x ⊆ s) : x ∈ 𝒫 s :=
  h

theorem subset_of_mem_powerset {x s : Set α} (h : x ∈ 𝒫 s) : x ⊆ s :=
  h

@[simp]
theorem mem_powerset_iff (x s : Set α) : x ∈ 𝒫 s ↔ x ⊆ s :=
  Iff.rfl

theorem powerset_inter (s t : Set α) : 𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext fun u => subset_inter_iff

@[simp]
theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  ⟨fun h => h (Subset.refl s), fun h u hu => Subset.trans hu h⟩

theorem monotone_powerset : Monotone (Powerset : Set α → Set (Set α)) := fun s t => powerset_mono.2

@[simp]
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, empty_subset s⟩

@[simp]
theorem powerset_empty : 𝒫(∅ : Set α) = {∅} :=
  ext fun s => subset_empty_iff

@[simp]
theorem powerset_univ : 𝒫(Univ : Set α) = univ :=
  eq_univ_of_forall subset_univ

/-! ### Sets defined as an if-then-else -/


theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else Univ) ↔ ∀ h : p, x ∈ t h := by split_ifs <;> simp [h]

@[simp]
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) : x ∈ ite p t Set.Univ ↔ p → x ∈ t :=
  mem_dite_univ_right p (fun _ => t) x

theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then Univ else t h) ↔ ∀ h : ¬p, x ∈ t h := by split_ifs <;> simp [h]

@[simp]
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) : x ∈ ite p Set.Univ t ↔ ¬p → x ∈ t :=
  mem_dite_univ_left p (fun _ => t) x

/-! ### If-then-else for sets -/


/-- `ite` for sets: `set.ite t s s' ∩ t = s ∩ t`, `set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def Ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.Ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]

@[simp]
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.Ite, Set.Ite, diff_compl, union_comm, diff_eq]

@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by rw [← ite_compl, ite_inter_self]

@[simp]
theorem ite_diff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'

@[simp]
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_diff _ _

@[simp]
theorem ite_left (s t : Set α) : s.ite s t = s ∪ t := by simp [Set.Ite]

@[simp]
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s := by simp [Set.Ite]

@[simp]
theorem ite_empty (s s' : Set α) : Set.Ite ∅ s s' = s' := by simp [Set.Ite]

@[simp]
theorem ite_univ (s s' : Set α) : Set.Ite Univ s s' = s := by simp [Set.Ite]

@[simp]
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.Ite]

@[simp]
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t := by simp [Set.Ite]

theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') : t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (inter_subset_inter_left _ h')

theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union (inter_subset_left _ _) (diff_subset _ _)

theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ (inter_subset_left _ _) (inter_subset_right _ _)

theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) : t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' := by
  ext x
  simp only [Set.Ite, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
  itauto

theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s := by rw [ite_inter_inter, ite_same]

theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) : t.ite s₁ s₂ ∩ s = s₁ ∩ s := by
  rw [← ite_inter, ← h, ite_same]

theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' := by
  simp only [subset_def, ← forall_and]
  refine' forall_congr' fun x => _
  by_cases hx:x ∈ t <;> simp [*, Set.Ite]

/-! ### Inverse image -/


/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def Preimage {α : Type u} {β : Type v} (f : α → β) (s : Set β) : Set α :=
  { x | f x ∈ s }

-- mathport name: «expr ⁻¹' »
infixl:80 " ⁻¹' " => Preimage

section Preimage

variable {f : α → β} {g : β → γ}

@[simp]
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl

@[simp]
theorem mem_preimage {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s :=
  Iff.rfl

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:61:9: parse error -/
theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s := by
  congr with x
  apply_assumption

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t := fun x hx => h hx

@[simp]
theorem preimage_univ : f ⁻¹' univ = univ :=
  rfl

theorem subset_preimage_univ {s : Set α} : s ⊆ f ⁻¹' univ :=
  subset_univ _

@[simp]
theorem preimage_inter {s t : Set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t :=
  rfl

@[simp]
theorem preimage_union {s t : Set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t :=
  rfl

@[simp]
theorem preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ :=
  rfl

@[simp]
theorem preimage_diff (f : α → β) (s t : Set β) : f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t :=
  rfl

@[simp]
theorem preimage_ite (f : α → β) (s t₁ t₂ : Set β) : f ⁻¹' s.ite t₁ t₂ = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
  rfl

@[simp]
theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' { a | p a } = { a | p (f a) } :=
  rfl

@[simp]
theorem preimage_id_eq : Preimage (id : α → α) = id :=
  rfl

theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl

@[simp]
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl

@[simp]
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun x : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall fun x => h

@[simp]
theorem preimage_const_of_not_mem {b : β} {s : Set β} (h : b ∉ s) : (fun x : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty fun x hx => h hx

theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] : (fun x : α => b) ⁻¹' s = if b ∈ s then Univ else ∅ :=
  by
  split_ifs with hb hb
  exacts[preimage_const_of_mem hb, preimage_const_of_not_mem hb]

theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl

theorem preimage_comp_eq : Preimage (g ∘ f) = Preimage f ∘ Preimage g :=
  rfl

@[simp]
theorem preimage_iterate_eq {f : α → α} {n : ℕ} : Set.Preimage (f^[n]) = Set.Preimage f^[n] := by
  induction' n with n ih
  · simp
    
  rw [iterate_succ, iterate_succ', Set.preimage_comp_eq, ih]

theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} : f ⁻¹' (g ⁻¹' s) = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
    s = Subtype.val ⁻¹' t ↔ ∀ (x) (h : p x), (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t :=
  ⟨fun s_eq x h => by
    rw [s_eq]
    simp, fun h => ext fun ⟨x, hx⟩ => by simp [h]⟩

theorem nonempty_of_nonempty_preimage {s : Set β} {f : α → β} (hf : (f ⁻¹' s).Nonempty) : s.Nonempty :=
  let ⟨x, hx⟩ := hf
  ⟨f x, hx⟩

theorem preimage_subtype_coe_eq_compl {α : Type _} {s u v : Set α} (hsuv : s ⊆ u ∪ v) (H : s ∩ (u ∩ v) = ∅) :
    (coe : s → α) ⁻¹' u = (coe ⁻¹' v)ᶜ := by
  ext ⟨x, x_in_s⟩
  constructor
  · intro x_in_u x_in_v
    exact eq_empty_iff_forall_not_mem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩
    
  · intro hx
    exact Or.elim (hsuv x_in_s) id fun hx' => hx.elim hx'
    

end Preimage

/-! ### Image of a set under a function -/


section Image

/-- The image of `s : set α` by `f : α → β`, written `f '' s`,
  is the set of `y : β` such that `f x = y` for some `x ∈ s`. -/
def Image (f : α → β) (s : Set α) : Set β :=
  { y | ∃ x, x ∈ s ∧ f x = y }

-- mathport name: «expr '' »
infixl:80 " '' " => Image

theorem mem_image_iff_bex {f : α → β} {s : Set α} {y : β} : y ∈ f '' s ↔ ∃ (x : _)(_ : x ∈ s), f x = y :=
  bex_def.symm

@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y :=
  Iff.rfl

theorem image_eta (f : α → β) : f '' s = (fun x => f x) '' s :=
  rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩

theorem _root_.function.injective.mem_set_image {f : α → β} (hf : Injective f) {s : Set α} {a : α} :
    f a ∈ f '' s ↔ a ∈ s :=
  ⟨fun ⟨b, hb, Eq⟩ => hf Eq ▸ hb, mem_image_of_mem f⟩

theorem ball_image_iff {f : α → β} {s : Set α} {p : β → Prop} : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x) := by simp

theorem ball_image_of_ball {f : α → β} {s : Set α} {p : β → Prop} (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ f '' s, p y :=
  ball_image_iff.2 h

theorem bex_image_iff {f : α → β} {s : Set α} {p : β → Prop} : (∃ y ∈ f '' s, p y) ↔ ∃ x ∈ s, p (f x) := by simp

theorem mem_image_elim {f : α → β} {s : Set α} {C : β → Prop} (h : ∀ x : α, x ∈ s → C (f x)) :
    ∀ {y : β}, y ∈ f '' s → C y
  | _, ⟨a, a_in, rfl⟩ => h a a_in

theorem mem_image_elim_on {f : α → β} {s : Set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
    (h : ∀ x : α, x ∈ s → C (f x)) : C y :=
  mem_image_elim h h_y

@[congr]
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f '' s = g '' s := by safe [ext_iff, iff_def]

/-- A common special case of `image_congr` -/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f '' s = g '' s :=
  image_congr fun x _ => h x

theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g '' a = f '' (g '' a) :=
  Subset.antisymm (ball_image_of_ball fun a ha => mem_image_of_mem _ <| mem_image_of_mem _ ha)
    (ball_image_of_ball <| ball_image_of_ball fun a ha => mem_image_of_mem _ ha)

/-- A variant of `image_comp`, useful for rewriting -/
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g '' (f '' s) = (fun x => g (f x)) '' s :=
  (image_comp g f s).symm

theorem image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
    (s.Image g).Image f = (s.Image f').Image g' := by simp_rw [image_image, h_comm]

theorem _root_.function.semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β} (h : Function.Semiconj f ga gb) :
    Function.Semiconj (Image f) (Image ga) (Image gb) := fun s => image_comm h

theorem _root_.function.commute.set_image {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (Image f) (Image g) :=
  h.set_image

/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b := by
  simp only [subset_def, mem_image]
  exact fun x => fun ⟨w, h1, h2⟩ => ⟨w, h h1, h2⟩

theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t :=
  ext fun x =>
    ⟨by rintro ⟨a, h | h, rfl⟩ <;> [left, right] <;> exact ⟨_, h, rfl⟩, by
      rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩) <;> refine' ⟨_, _, rfl⟩ <;> [left, right] <;> exact h⟩

@[simp]
theorem image_empty (f : α → β) : f '' ∅ = ∅ := by
  ext
  simp

theorem image_inter_subset (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  subset_inter (image_subset _ <| inter_subset_left _ _) (image_subset _ <| inter_subset_right _ _)

theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x ∈ t, ∀ y ∈ s, f x = f y → x = y) :
    f '' s ∩ f '' t = f '' (s ∩ t) :=
  Subset.antisymm
    (fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have : a₂ = a₁ := h _ ha₂ _ ha₁ (by simp [*])
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
    (image_inter_subset _ _ _)

theorem image_inter {f : α → β} {s t : Set α} (H : Injective f) : f '' s ∩ f '' t = f '' (s ∩ t) :=
  image_inter_on fun x _ y _ h => H h

theorem image_univ_of_surjective {ι : Type _} {f : ι → β} (H : Surjective f) : f '' univ = univ :=
  eq_univ_of_forall <| by simpa [image]

@[simp]
theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} := by
  ext
  simp [image, eq_comm]

@[simp]
theorem Nonempty.image_const {s : Set α} (hs : s.Nonempty) (a : β) : (fun _ => a) '' s = {a} :=
  ext fun x =>
    ⟨fun ⟨y, _, h⟩ => h ▸ mem_singleton _, fun h => (eq_of_mem_singleton h).symm ▸ hs.imp fun y hy => ⟨hy, rfl⟩⟩

@[simp]
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f '' s = ∅ ↔ s = ∅ := by
  simp only [eq_empty_iff_forall_not_mem]
  exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

theorem preimage_compl_eq_image_compl [BooleanAlgebra α] (S : Set α) : compl ⁻¹' S = compl '' S :=
  Set.ext fun x =>
    ⟨fun h => ⟨xᶜ, h, compl_compl x⟩, fun h => Exists.elim h fun y hy => (compl_eq_comm.mp hy.2).symm.subst hy.1⟩

theorem mem_compl_image [BooleanAlgebra α] (t : α) (S : Set α) : t ∈ compl '' S ↔ tᶜ ∈ S := by
  simp [← preimage_compl_eq_image_compl]

/-- A variant of `image_id` -/
@[simp]
theorem image_id' (s : Set α) : (fun x => x) '' s = s := by
  ext
  simp

theorem image_id (s : Set α) : id '' s = s := by simp

theorem compl_compl_image [BooleanAlgebra α] (S : Set α) : compl '' (compl '' S) = S := by
  rw [← image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : Set α} : f '' insert a s = insert (f a) (f '' s) := by
  ext
  simp [and_or_left, exists_or, eq_comm, or_comm', and_comm']

theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} := by simp only [image_insert_eq, image_singleton]

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set α) : f '' s ⊆ g ⁻¹' s :=
  fun b ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : LeftInverse g f) (s : Set β) : f ⁻¹' s ⊆ g '' s :=
  fun b h => ⟨f b, h, I b⟩

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    Image f = Preimage g :=
  funext fun s => Subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : LeftInverse g f)
    (h₂ : RightInverse g f) : b ∈ f '' s ↔ g b ∈ s := by rw [image_eq_preimage_of_inverse h₁ h₂] <;> rfl

theorem image_compl_subset {f : α → β} {s : Set α} (H : Injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
  Disjoint.subset_compl_left <| by simp [Disjoint, image_inter H]

theorem subset_image_compl {f : α → β} {s : Set α} (H : Surjective f) : (f '' s)ᶜ ⊆ f '' sᶜ :=
  compl_subset_iff_union.2 <| by
    rw [← image_union]
    simp [image_univ_of_surjective H]

theorem image_compl_eq {f : α → β} {s : Set α} (H : Bijective f) : f '' sᶜ = (f '' s)ᶜ :=
  Subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

theorem subset_image_diff (f : α → β) (s t : Set α) : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rw [diff_subset_iff, ← image_union, union_diff_self]
  exact image_subset f (subset_union_right t s)

theorem image_diff {f : α → β} (hf : Injective f) (s t : Set α) : f '' (s \ t) = f '' s \ f '' t :=
  Subset.antisymm (Subset.trans (image_inter_subset _ _ _) <| inter_subset_inter_right _ <| image_compl_subset hf)
    (subset_image_diff f s t)

theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f '' s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩

theorem Nonempty.of_image {f : α → β} {s : Set α} : (f '' s).Nonempty → s.Nonempty
  | ⟨y, x, hx, _⟩ => ⟨x, hx⟩

@[simp]
theorem nonempty_image_iff {f : α → β} {s : Set α} : (f '' s).Nonempty ↔ s.Nonempty :=
  ⟨Nonempty.of_image, fun h => h.Image f⟩

theorem Nonempty.preimage {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : Surjective f) : (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf y
  ⟨x, mem_preimage.2 <| hx.symm ▸ hy⟩

instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f '' s) :=
  (Set.Nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  ball_image_iff

theorem image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s :=
  image_subset_iff.2 Subset.rfl

theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f '' s) := fun x => mem_image_of_mem f

theorem preimage_image_eq {f : α → β} (s : Set α) (h : Injective f) : f ⁻¹' (f '' s) = s :=
  Subset.antisymm (fun x ⟨y, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

theorem image_preimage_eq {f : α → β} (s : Set β) (h : Surjective f) : f '' (f ⁻¹' s) = s :=
  Subset.antisymm (image_preimage_subset f s) fun x hx =>
    let ⟨y, e⟩ := h x
    ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩

theorem preimage_eq_preimage {f : β → α} (hf : Surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  Iff.intro (fun eq => by rw [← image_preimage_eq s hf, ← image_preimage_eq t hf, Eq]) fun eq => Eq ▸ rfl

theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) : f '' (s ∩ f ⁻¹' t) = f '' s ∩ t := by
  apply subset.antisymm
  · calc
      f '' (s ∩ f ⁻¹' t) ⊆ f '' s ∩ f '' (f ⁻¹' t) := image_inter_subset _ _ _
      _ ⊆ f '' s ∩ t := inter_subset_inter_right _ (image_preimage_subset f t)
      
    
  · rintro _ ⟨⟨x, h', rfl⟩, h⟩
    exact ⟨x, ⟨h', h⟩, rfl⟩
    

theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) : f '' (f ⁻¹' t ∩ s) = t ∩ f '' s := by
  simp only [inter_comm, image_inter_preimage]

@[simp]
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} : (f '' s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty :=
  by rw [← image_inter_preimage, nonempty_image_iff]

theorem image_diff_preimage {f : α → β} {s : Set α} {t : Set β} : f '' (s \ f ⁻¹' t) = f '' s \ t := by
  simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

theorem compl_image : Image (compl : Set α → Set α) = Preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : Set α → Prop} : compl '' { s | p s } = { s | p (sᶜ) } :=
  congr_fun compl_image p

theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) : s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) := fun x h =>
  ⟨mem_image_of_mem _ h.left, h.right⟩

theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) : s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) := fun x h =>
  Or.elim h (fun l => Or.inl <| mem_image_of_mem _ l) fun r => Or.inr r

theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)

theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} : f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl

theorem image_eq_image {f : α → β} (hf : Injective f) : f '' s = f '' t ↔ s = t :=
  Iff.symm <| (Iff.intro fun eq => Eq ▸ rfl) fun eq => by rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, Eq]

theorem image_subset_image_iff {f : α → β} (hf : Injective f) : f '' s ⊆ f '' t ↔ s ⊆ t := by
  refine' Iff.symm <| (Iff.intro (image_subset f)) fun h => _
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf]
  exact preimage_mono h

theorem prod_quotient_preimage_eq_image [s : Setoid α] (g : Quotient s → β) {h : α → β} (Hh : h = g ∘ Quotient.mk)
    (r : Set (β × β)) :
    { x : Quotient s × Quotient s | (g x.1, g x.2) ∈ r } =
      (fun a : α × α => (⟦a.1⟧, ⟦a.2⟧)) '' ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext fun ⟨a₁, a₂⟩ =>
      ⟨Quotient.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩, fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
        show (g a₁, g a₂) ∈ r from
          have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := Prod.ext_iff.1 h₂
          h₃.1 ▸ h₃.2 ▸ h₁⟩

theorem exists_image_iff (f : α → β) (x : Set α) (P : β → Prop) : (∃ a : f '' x, P a) ↔ ∃ a : x, P (f a) :=
  ⟨fun ⟨a, h⟩ => ⟨⟨_, a.Prop.some_spec.1⟩, a.Prop.some_spec.2.symm ▸ h⟩, fun ⟨a, h⟩ => ⟨⟨_, _, a.Prop, rfl⟩, h⟩⟩

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def imageFactorization (f : α → β) (s : Set α) : s → f '' s := fun p => ⟨f p.1, mem_image_of_mem f p.2⟩

theorem image_factorization_eq {f : α → β} {s : Set α} : Subtype.val ∘ imageFactorization f s = f ∘ Subtype.val :=
  funext fun p => rfl

theorem surjective_onto_image {f : α → β} {s : Set α} : Surjective (imageFactorization f s) := fun ⟨_, ⟨a, ha, rfl⟩⟩ =>
  ⟨⟨a, ha⟩, rfl⟩

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem image_perm {s : Set α} {σ : Equiv.Perm α} (hs : { a : α | σ a ≠ a } ⊆ s) : σ '' s = s := by
  ext i
  obtain hi | hi := eq_or_ne (σ i) i
  · refine' ⟨_, fun h => ⟨i, h, hi⟩⟩
    rintro ⟨j, hj, h⟩
    rwa [σ.injective (hi.trans h.symm)]
    
  · refine' iff_of_true ⟨σ.symm i, hs fun h => hi _, σ.apply_symm_apply _⟩ (hs hi)
    convert congr_arg σ h <;> exact (σ.apply_symm_apply _).symm
    

end Image

/-! ### Subsingleton -/


/-- A set `s` is a `subsingleton` if it has at most one element. -/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y

theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun x hx y hy => ht (hst hx) (hst hy)

theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun y => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp]
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun x => False.elim

@[simp]
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun x hx y hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl

theorem subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h

theorem subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.Subsingleton := fun b hb c hc =>
  (h _ hb).trans (h _ hc).symm

theorem subsingleton_iff_singleton {x} (hx : x ∈ s) : s.Subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩

theorem Subsingleton.eq_empty_or_singleton (hs : s.Subsingleton) : s = ∅ ∨ ∃ x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩

theorem Subsingleton.induction_on {p : Set α → Prop} (hs : s.Subsingleton) (he : p ∅) (h₁ : ∀ x, p {x}) : p s := by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts[he, h₁ _]

theorem subsingleton_univ [Subsingleton α] : (Univ : Set α).Subsingleton := fun x hx y hy => Subsingleton.elim x y

theorem subsingleton_of_univ_subsingleton (h : (Univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩

@[simp]
theorem subsingleton_univ_iff : (Univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩

theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : Set.Subsingleton s :=
  subsingleton_univ.anti (subset_univ s)

theorem subsingleton_is_top (α : Type _) [PartialOrder α] : Set.Subsingleton { x : α | IsTop x } := fun x hx y hy =>
  hx.IsMax.eq_of_le (hy x)

theorem subsingleton_is_bot (α : Type _) [PartialOrder α] : Set.Subsingleton { x : α | IsBot x } := fun x hx y hy =>
  hx.IsMin.eq_of_ge (hy x)

theorem exists_eq_singleton_iff_nonempty_subsingleton : (∃ a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton := by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
    
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty
    

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton := by
  constructor
  · refine' fun h => fun a ha b hb => _
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
    
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)
    

theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton → Subsingleton s :=
  s.subsingleton_coe.2

/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `subtype`, see `subtype.subsingleton`. -/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s := by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton

/-- The image of a subsingleton is a subsingleton. -/
theorem Subsingleton.image (hs : s.Subsingleton) (f : α → β) : (f '' s).Subsingleton :=
  fun _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩ => Hx ▸ Hy ▸ congr_arg f (hs hx hy)

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem Subsingleton.preimage {s : Set β} (hs : s.Subsingleton) {f : α → β} (hf : Function.Injective f) :
    (f ⁻¹' s).Subsingleton := fun a ha b hb => hf <| hs ha hb

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
theorem subsingleton_of_image {α β : Type _} {f : α → β} (hf : Function.Injective f) (s : Set α)
    (hs : (f '' s).Subsingleton) : s.Subsingleton :=
  (hs.Preimage hf).anti <| subset_preimage_image _ _

/-- If the preimage of a set under an surjective map is a subsingleton,
the set is a subsingleton. -/
theorem subsingleton_of_preimage {α β : Type _} {f : α → β} (hf : Function.Surjective f) (s : Set β)
    (hs : (f ⁻¹' s).Subsingleton) : s.Subsingleton := fun fx hx fy hy => by
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact congr_arg f (hs hx hy)

/-! ### Nontrivial -/


/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x y «expr ∈ » s) -/
/-- A set `s` is `nontrivial` if it has at least two distinct elements. -/
protected def Nontrivial (s : Set α) : Prop :=
  ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x ≠ y

theorem nontrivial_of_mem_mem_ne {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.Nontrivial :=
  ⟨x, hx, y, hy, hxy⟩

/-- Extract witnesses from s.nontrivial. This function might be used instead of case analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom. -/
protected noncomputable def Nontrivial.some (hs : s.Nontrivial) : α × α :=
  (hs.some, hs.some_spec.some_spec.some)

protected theorem Nontrivial.some_fst_mem (hs : s.Nontrivial) : hs.some.fst ∈ s :=
  hs.some_spec.some

protected theorem Nontrivial.some_snd_mem (hs : s.Nontrivial) : hs.some.snd ∈ s :=
  hs.some_spec.some_spec.some_spec.some

protected theorem Nontrivial.some_fst_ne_some_snd (hs : s.Nontrivial) : hs.some.fst ≠ hs.some.snd :=
  hs.some_spec.some_spec.some_spec.some_spec

theorem Nontrivial.mono (hs : s.Nontrivial) (hst : s ⊆ t) : t.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩

theorem nontrivial_pair {x y} (hxy : x ≠ y) : ({x, y} : Set α).Nontrivial :=
  ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩

theorem nontrivial_of_pair_subset {x y} (hxy : x ≠ y) (h : {x, y} ⊆ s) : s.Nontrivial :=
  (nontrivial_pair hxy).mono h

theorem Nontrivial.pair_subset (hs : s.Nontrivial) : ∃ (x y : _)(hab : x ≠ y), {x, y} ⊆ s :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, y, hxy, insert_subset.2 ⟨hx, singleton_subset_iff.2 hy⟩⟩

theorem nontrivial_iff_pair_subset : s.Nontrivial ↔ ∃ (x y : _)(hxy : x ≠ y), {x, y} ⊆ s :=
  ⟨Nontrivial.pair_subset, fun H =>
    let ⟨x, y, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩

theorem nontrivial_of_exists_ne {x} (hx : x ∈ s) (h : ∃ y ∈ s, y ≠ x) : s.Nontrivial :=
  let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩

theorem Nontrivial.exists_ne (hs : s.Nontrivial) (z) : ∃ x ∈ s, x ≠ z := by
  by_contra H
  push_neg  at H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx, H y hy] at hxy
  exact hxy rfl

theorem nontrivial_iff_exists_ne {x} (hx : x ∈ s) : s.Nontrivial ↔ ∃ y ∈ s, y ≠ x :=
  ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩

theorem nontrivial_of_lt [Preorder α] {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) : s.Nontrivial :=
  ⟨x, hx, y, hy, ne_of_lt hxy⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem nontrivial_of_exists_lt [Preorder α] (H : ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x < y) : s.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem Nontrivial.exists_lt [LinearOrder α] (hs : s.Nontrivial) : ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x < y :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:555:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem nontrivial_iff_exists_lt [LinearOrder α] : s.Nontrivial ↔ ∃ (x y : _)(_ : x ∈ s)(_ : y ∈ s), x < y :=
  ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩

protected theorem Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty :=
  let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩

protected theorem Nontrivial.ne_empty (hs : s.Nontrivial) : s ≠ ∅ :=
  hs.Nonempty.ne_empty

theorem Nontrivial.not_subset_empty (hs : s.Nontrivial) : ¬s ⊆ ∅ :=
  hs.Nonempty.not_subset_empty

@[simp]
theorem not_nontrivial_empty : ¬(∅ : Set α).Nontrivial := fun h => h.ne_empty rfl

@[simp]
theorem not_nontrivial_singleton {x} : ¬({x} : Set α).Nontrivial := fun H => by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  exact
    let ⟨y, hy, hya⟩ := H
    hya (mem_singleton_iff.1 hy)

theorem Nontrivial.ne_singleton {x} (hs : s.Nontrivial) : s ≠ {x} := fun H => by
  rw [H] at hs
  exact not_nontrivial_singleton hs

theorem Nontrivial.not_subset_singleton {x} (hs : s.Nontrivial) : ¬s ⊆ {x} :=
  (not_congr subset_singleton_iff_eq).2 (not_or_of_not hs.ne_empty hs.ne_singleton)

theorem nontrivial_univ [Nontrivial α] : (Univ : Set α).Nontrivial :=
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩

theorem nontrivial_of_univ_nontrivial (h : (Univ : Set α).Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩

@[simp]
theorem nontrivial_univ_iff : (Univ : Set α).Nontrivial ↔ Nontrivial α :=
  ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩

theorem nontrivial_of_nontrivial (hs : s.Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩

/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast]
theorem nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial := by
  simp_rw [← nontrivial_univ_iff, Set.Nontrivial, mem_univ, exists_true_left, SetCoe.exists, Subtype.mk_eq_mk]

alias nontrivial_coe_sort ↔ _ nontrivial.coe_sort

/-- A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `subtype`, see `subtype.nontrivial_iff_exists_ne`. -/
theorem nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α :=
  nontrivial_of_nontrivial <| nontrivial_coe_sort.1 hs

theorem nontrivial_mono {α : Type _} {s t : Set α} (hst : s ⊆ t) (hs : Nontrivial s) : Nontrivial t :=
  nontrivial.coe_sort <| (nontrivial_coe_sort.1 hs).mono hst

/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
theorem Nontrivial.preimage {s : Set β} (hs : s.Nontrivial) {f : α → β} (hf : Function.Surjective f) :
    (f ⁻¹' s).Nontrivial := by
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩
  rcases hf fx, hf fy with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

/-- The image of a nontrivial set under an injective map is nontrivial. -/
theorem Nontrivial.image (hs : s.Nontrivial) {f : α → β} (hf : Function.Injective f) : (f '' s).Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.Ne hxy⟩

/-- If the image of a set is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_image (f : α → β) (s : Set α) (hs : (f '' s).Nontrivial) : s.Nontrivial :=
  let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs
  ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
theorem nontrivial_of_preimage {f : α → β} (hf : Function.Injective f) (s : Set β) (hs : (f ⁻¹' s).Nontrivial) :
    s.Nontrivial :=
  (hs.Image hf).mono <| image_preimage_subset _ _

@[simp]
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall]

@[simp]
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm

alias not_nontrivial_iff ↔ _ subsingleton.not_nontrivial

alias not_subsingleton_iff ↔ _ nontrivial.not_subsingleton

theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm <| eq_univ_of_forall <| Classical.cases (by simp) (by simp)

section Preorder

variable [Preorder α] [Preorder β] (f : α → β)

/-! ### Monotonicity on singletons -/


protected theorem Subsingleton.monotone_on (h : s.Subsingleton) : MonotoneOn f s := fun a ha b hb _ =>
  (congr_arg _ (h ha hb)).le

protected theorem Subsingleton.antitone_on (h : s.Subsingleton) : AntitoneOn f s := fun a ha b hb _ =>
  (congr_arg _ (h hb ha)).le

protected theorem Subsingleton.strict_mono_on (h : s.Subsingleton) : StrictMonoOn f s := fun a ha b hb hlt =>
  (hlt.Ne (h ha hb)).elim

protected theorem Subsingleton.strict_anti_on (h : s.Subsingleton) : StrictAntiOn f s := fun a ha b hb hlt =>
  (hlt.Ne (h ha hb)).elim

@[simp]
theorem monotone_on_singleton : MonotoneOn f {a} :=
  subsingleton_singleton.MonotoneOn f

@[simp]
theorem antitone_on_singleton : AntitoneOn f {a} :=
  subsingleton_singleton.AntitoneOn f

@[simp]
theorem strict_mono_on_singleton : StrictMonoOn f {a} :=
  subsingleton_singleton.StrictMonoOn f

@[simp]
theorem strict_anti_on_singleton : StrictAntiOn f {a} :=
  subsingleton_singleton.StrictAntiOn f

end Preorder

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α}

open Function

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def Range (f : ι → α) : Set α :=
  { x | ∃ y, f y = x }

@[simp]
theorem mem_range {x : α} : x ∈ Range f ↔ ∃ y, f y = x :=
  Iff.rfl

@[simp]
theorem mem_range_self (i : ι) : f i ∈ Range f :=
  ⟨i, rfl⟩

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ Range f, p a) ↔ ∀ i, p (f i) := by simp

theorem forall_subtype_range_iff {p : Range f → Prop} : (∀ a : Range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun H i => H _, fun H ⟨y, i, hi⟩ => by
    subst hi
    apply H⟩

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ Range f, p a) ↔ ∃ i, p (f i) := by simp

theorem exists_range_iff' {p : α → Prop} : (∃ a, a ∈ Range f ∧ p a) ↔ ∃ i, p (f i) := by
  simpa only [exists_prop] using exists_range_iff

theorem exists_subtype_range_iff {p : Range f → Prop} : (∃ a : Range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun ⟨⟨a, i, hi⟩, ha⟩ => by
    subst a
    exact ⟨i, ha⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩

theorem range_iff_surjective : Range f = univ ↔ Surjective f :=
  eq_univ_iff_forall

alias range_iff_surjective ↔ _ _root_.function.surjective.range_eq

@[simp]
theorem image_univ {f : α → β} : f '' univ = Range f := by
  ext
  simp [image, range]

theorem image_subset_range (f : α → β) (s) : f '' s ⊆ Range f := by
  rw [← image_univ] <;> exact image_subset _ (subset_univ _)

theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f '' s) : x ∈ Range f :=
  image_subset_range f s h

theorem Nonempty.preimage' {s : Set β} (hs : s.Nonempty) {f : α → β} (hf : s ⊆ Set.Range f) : (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs
  let ⟨x, hx⟩ := hf hy
  ⟨x, Set.mem_preimage.2 <| hx.symm ▸ hy⟩

theorem range_comp (g : α → β) (f : ι → α) : Range (g ∘ f) = g '' Range f :=
  Subset.antisymm (forall_range_iff.mpr fun i => mem_image_of_mem g (mem_range_self _))
    (ball_image_iff.mpr <| forall_range_iff.mpr mem_range_self)

theorem range_subset_iff : Range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_range_iff

theorem range_eq_iff (f : α → β) (s : Set β) : Range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b := by
  rw [← range_subset_iff]
  exact le_antisymm_iff

theorem range_comp_subset_range (f : α → β) (g : β → γ) : Range (g ∘ f) ⊆ Range g := by
  rw [range_comp] <;> apply image_subset_range

theorem range_nonempty_iff_nonempty : (Range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨y, x, hxy⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩

theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (Range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h

@[simp]
theorem range_eq_empty_iff {f : ι → α} : Range f = ∅ ↔ IsEmpty ι := by
  rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]

theorem range_eq_empty [IsEmpty ι] (f : ι → α) : Range f = ∅ :=
  range_eq_empty_iff.2 ‹_›

instance [Nonempty ι] (f : ι → α) : Nonempty (Range f) :=
  (range_nonempty f).to_subtype

@[simp]
theorem image_union_image_compl_eq_range (f : α → β) : f '' s ∪ f '' sᶜ = Range f := by
  rw [← image_union, ← image_univ, ← union_compl_self]

theorem insert_image_compl_eq_range (f : α → β) (x : α) : insert (f x) (f '' {x}ᶜ) = Range f := by
  ext y
  rw [mem_range, mem_insert_iff, mem_image]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact ⟨x, h.symm⟩
      
    · exact ⟨x', h⟩
      
    
  · rintro ⟨x', h⟩
    by_cases hx:x' = x
    · left
      rw [← h, hx]
      
    · right
      refine' ⟨_, _, h⟩
      rw [mem_compl_singleton_iff]
      exact hx
      
    

theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f '' (f ⁻¹' t) = t ∩ Range f :=
  ext fun x =>
    ⟨fun ⟨x, hx, HEq⟩ => HEq ▸ ⟨hx, mem_range_self _⟩, fun ⟨hx, ⟨y, h_eq⟩⟩ =>
      h_eq ▸ mem_image_of_mem f <| show y ∈ f ⁻¹' t by simp [preimage, h_eq, hx]⟩

theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ Range f) : f '' (f ⁻¹' s) = s := by
  rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ Range f :=
  ⟨by
    intro h
    rw [← h]
    apply image_subset_range, image_preimage_eq_of_subset⟩

theorem subset_range_iff_exists_image_eq {f : α → β} {s : Set β} : s ⊆ Range f ↔ ∃ t, f '' t = s :=
  ⟨fun h => ⟨_, image_preimage_eq_iff.2 h⟩, fun ⟨t, ht⟩ => ht ▸ image_subset_range _ _⟩

theorem range_image (f : α → β) : Range (Image f) = 𝒫 Range f :=
  ext fun s => subset_range_iff_exists_image_eq.symm

theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ Range f) : f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  constructor
  · intro h x hx
    rcases hs hx with ⟨y, rfl⟩
    exact h hx
    
  intro h x
  apply h

theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ Range f) (ht : t ⊆ Range f) :
    f ⁻¹' s = f ⁻¹' t ↔ s = t := by
  constructor
  · intro h
    apply subset.antisymm
    rw [← preimage_subset_preimage_iff hs, h]
    rw [← preimage_subset_preimage_iff ht, h]
    
  rintro rfl
  rfl

@[simp]
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ Range f) = f ⁻¹' s :=
  Set.ext fun x => and_iff_left ⟨x, rfl⟩

@[simp]
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (Range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]

theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s := by
  rw [image_preimage_eq_inter_range, preimage_inter_range]

@[simp]
theorem range_id : Range (@id α) = univ :=
  range_iff_surjective.2 surjective_id

@[simp]
theorem range_id' : (Range fun x : α => x) = univ :=
  range_id

@[simp]
theorem _root_.prod.range_fst [Nonempty β] : Range (Prod.fst : α × β → α) = univ :=
  Prod.fst_surjective.range_eq

@[simp]
theorem _root_.prod.range_snd [Nonempty α] : Range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq

@[simp]
theorem range_eval {ι : Type _} {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
    Range (eval i : (∀ i, α i) → α i) = univ :=
  (surjective_eval i).range_eq

theorem isComplRangeInlRangeInr : IsCompl (range <| @Sum.inl α β) (Range Sum.inr) :=
  ⟨by
    rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩
    cc, by rintro (x | y) - <;> [left, right] <;> exact mem_range_self _⟩

@[simp]
theorem range_inl_union_range_inr : Range (Sum.inl : α → Sum α β) ∪ Range Sum.inr = univ :=
  isComplRangeInlRangeInr.sup_eq_top

@[simp]
theorem range_inl_inter_range_inr : Range (Sum.inl : α → Sum α β) ∩ Range Sum.inr = ∅ :=
  isComplRangeInlRangeInr.inf_eq_bot

@[simp]
theorem range_inr_union_range_inl : Range (Sum.inr : β → Sum α β) ∪ Range Sum.inl = univ :=
  isComplRangeInlRangeInr.symm.sup_eq_top

@[simp]
theorem range_inr_inter_range_inl : Range (Sum.inr : β → Sum α β) ∩ Range Sum.inl = ∅ :=
  isComplRangeInlRangeInr.symm.inf_eq_bot

@[simp]
theorem preimage_inl_image_inr (s : Set β) : Sum.inl ⁻¹' (@Sum.inr α β '' s) = ∅ := by
  ext
  simp

@[simp]
theorem preimage_inr_image_inl (s : Set α) : Sum.inr ⁻¹' (@Sum.inl α β '' s) = ∅ := by
  ext
  simp

@[simp]
theorem preimage_inl_range_inr : Sum.inl ⁻¹' Range (Sum.inr : β → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inl_image_inr]

@[simp]
theorem preimage_inr_range_inl : Sum.inr ⁻¹' Range (Sum.inl : α → Sum α β) = ∅ := by
  rw [← image_univ, preimage_inr_image_inl]

@[simp]
theorem compl_range_inl : Range (Sum.inl : α → Sum α β)ᶜ = Range (Sum.inr : β → Sum α β) :=
  IsCompl.compl_eq isComplRangeInlRangeInr

@[simp]
theorem compl_range_inr : Range (Sum.inr : β → Sum α β)ᶜ = Range (Sum.inl : α → Sum α β) :=
  IsCompl.compl_eq isComplRangeInlRangeInr.symm

theorem image_preimage_inl_union_image_preimage_inr (s : Set (Sum α β)) :
    Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) = s := by
  rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, ← inter_distrib_left, range_inl_union_range_inr,
    inter_univ]

@[simp]
theorem range_quot_mk (r : α → α → Prop) : Range (Quot.mk r) = univ :=
  (surjective_quot_mk r).range_eq

instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Set α) (Set β) ((· '' ·) c) fun s =>
      ∀ x ∈ s, p x where prf s hs := subset_range_iff_exists_image_eq.mp fun x hx => CanLift.prf _ (hs x hx)

@[simp]
theorem range_quotient_mk [Setoid α] : (Range fun x : α => ⟦x⟧) = univ :=
  range_quot_mk _

theorem range_const_subset {c : α} : (Range fun x : ι => c) ⊆ {c} :=
  range_subset_iff.2 fun x => rfl

@[simp]
theorem range_const : ∀ [Nonempty ι] {c : α}, (Range fun x : ι => c) = {c}
  | ⟨x⟩, c => (Subset.antisymm range_const_subset) fun y hy => (mem_singleton_iff.1 hy).symm ▸ mem_range_self x

theorem range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
    Range (Subtype.map f h) = coe ⁻¹' (f '' { x | p x }) := by
  ext ⟨x, hx⟩
  simp_rw [mem_preimage, mem_range, mem_image, Subtype.exists, Subtype.map, Subtype.coe_mk, mem_set_of, exists_prop]

theorem image_swap_eq_preimage_swap : Image (@Prod.swap α β) = Preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_left_inverse Prod.swap_right_inverse

theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ Range f :=
  Iff.rfl

theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ Range f :=
  not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.Not

theorem range_subset_singleton {f : ι → α} {x : α} : Range f ⊆ {x} ↔ f = const ι x := by
  simp [range_subset_iff, funext_iff, mem_singleton]

theorem image_compl_preimage {f : α → β} {s : Set β} : f '' (f ⁻¹' s)ᶜ = Range f \ s := by
  rw [compl_eq_univ_diff, image_diff_preimage, image_univ]

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def rangeFactorization (f : ι → β) : ι → Range f := fun i => ⟨f i, mem_range_self i⟩

theorem range_factorization_eq {f : ι → β} : Subtype.val ∘ rangeFactorization f = f :=
  funext fun i => rfl

@[simp]
theorem range_factorization_coe (f : ι → β) (a : ι) : (rangeFactorization f a : β) = f a :=
  rfl

@[simp]
theorem coe_comp_range_factorization (f : ι → β) : coe ∘ rangeFactorization f = f :=
  rfl

theorem surjective_onto_range : Surjective (rangeFactorization f) := fun ⟨_, ⟨i, rfl⟩⟩ => ⟨i, rfl⟩

theorem image_eq_range (f : α → β) (s : Set α) : f '' s = Range fun x : s => f x := by
  ext
  constructor
  rintro ⟨x, h1, h2⟩
  exact ⟨⟨x, h1⟩, h2⟩
  rintro ⟨⟨x, h1⟩, h2⟩
  exact ⟨x, h1, h2⟩

theorem _root_.sum.range_eq (f : Sum α β → γ) : Range f = Range (f ∘ Sum.inl) ∪ Range (f ∘ Sum.inr) :=
  ext fun x => Sum.exists

@[simp]
theorem Sum.elim_range (f : α → γ) (g : β → γ) : Range (Sum.elim f g) = Range f ∪ Range g :=
  Sum.range_eq _

theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} : Range (if p then f else g) ⊆ Range f ∪ Range g := by
  by_cases h:p
  · rw [if_pos h]
    exact subset_union_left _ _
    
  · rw [if_neg h]
    exact subset_union_right _ _
    

theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
    (Range fun x => if p x then f x else g x) ⊆ Range f ∪ Range g := by
  rw [range_subset_iff]
  intro x
  by_cases h:p x
  simp [if_pos h, mem_union, mem_range_self]
  simp [if_neg h, mem_union, mem_range_self]

@[simp]
theorem preimage_range (f : α → β) : f ⁻¹' Range f = univ :=
  eq_univ_of_forall mem_range_self

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
theorem range_unique [h : Unique ι] : Range f = {f default} := by
  ext x
  rw [mem_range]
  constructor
  · rintro ⟨i, hi⟩
    rw [h.uniq i] at hi
    exact hi ▸ mem_singleton _
    
  · exact fun h => ⟨default, h.symm⟩
    

theorem range_diff_image_subset (f : α → β) (s : Set α) : Range f \ f '' s ⊆ f '' sᶜ := fun y ⟨⟨x, h₁⟩, h₂⟩ =>
  ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

theorem range_diff_image {f : α → β} (H : Injective f) (s : Set α) : Range f \ f '' s = f '' sᶜ :=
  (Subset.antisymm (range_diff_image_subset f s)) fun y ⟨x, hx, hy⟩ =>
    hy ▸ ⟨mem_range_self _, fun ⟨x', hx', Eq⟩ => hx <| H Eq ▸ hx'⟩

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def rangeSplitting (f : α → β) : Range f → α := fun x => x.2.some

-- This can not be a `@[simp]` lemma because the head of the left hand side is a variable.
theorem apply_range_splitting (f : α → β) (x : Range f) : f (rangeSplitting f x) = x :=
  x.2.some_spec

@[simp]
theorem comp_range_splitting (f : α → β) : f ∘ rangeSplitting f = coe := by
  ext
  simp only [Function.comp_app]
  apply apply_range_splitting

-- When `f` is injective, see also `equiv.of_injective`.
theorem left_inverse_range_splitting (f : α → β) : LeftInverse (rangeFactorization f) (rangeSplitting f) := fun x => by
  ext
  simp only [range_factorization_coe]
  apply apply_range_splitting

theorem range_splitting_injective (f : α → β) : Injective (rangeSplitting f) :=
  (left_inverse_range_splitting f).Injective

theorem right_inverse_range_splitting {f : α → β} (h : Injective f) :
    RightInverse (rangeFactorization f) (rangeSplitting f) :=
  (left_inverse_range_splitting f).right_inverse_of_injective fun x y hxy => h <| Subtype.ext_iff.1 hxy

theorem preimage_range_splitting {f : α → β} (hf : Injective f) :
    Preimage (rangeSplitting f) = Image (rangeFactorization f) :=
  (image_eq_preimage_of_inverse (right_inverse_range_splitting hf) (left_inverse_range_splitting f)).symm

theorem isComplRangeSomeNone (α : Type _) : IsCompl (Range (some : α → Option α)) {none} :=
  ⟨fun x ⟨⟨a, ha⟩, (hn : x = none)⟩ => Option.some_ne_none _ (ha.trans hn), fun x hx =>
    Option.casesOn x (Or.inr rfl) fun x => Or.inl <| mem_range_self _⟩

@[simp]
theorem compl_range_some (α : Type _) : Range (some : α → Option α)ᶜ = {none} :=
  (isComplRangeSomeNone α).compl_eq

@[simp]
theorem range_some_inter_none (α : Type _) : Range (some : α → Option α) ∩ {none} = ∅ :=
  (isComplRangeSomeNone α).inf_eq_bot

@[simp]
theorem range_some_union_none (α : Type _) : Range (some : α → Option α) ∪ {none} = univ :=
  (isComplRangeSomeNone α).sup_eq_top

@[simp]
theorem insert_none_range_some (α : Type _) : insert none (Range (some : α → Option α)) = univ :=
  (isComplRangeSomeNone α).symm.sup_eq_top

end Range

end Set

open Set

namespace Function

variable {ι : Sort _} {α : Type _} {β : Type _} {f : α → β}

theorem Surjective.preimage_injective (hf : Surjective f) : Injective (Preimage f) := fun s t =>
  (preimage_eq_preimage hf).1

theorem Injective.preimage_image (hf : Injective f) (s : Set α) : f ⁻¹' (f '' s) = s :=
  preimage_image_eq s hf

theorem Injective.preimage_surjective (hf : Injective f) : Surjective (Preimage f) := by
  intro s
  use f '' s
  rw [hf.preimage_image]

theorem Injective.subsingleton_image_iff (hf : Injective f) {s : Set α} : (f '' s).Subsingleton ↔ s.Subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.Image f⟩

theorem Surjective.image_preimage (hf : Surjective f) (s : Set β) : f '' (f ⁻¹' s) = s :=
  image_preimage_eq s hf

theorem Surjective.image_surjective (hf : Surjective f) : Surjective (Image f) := by
  intro s
  use f ⁻¹' s
  rw [hf.image_preimage]

theorem Surjective.nonempty_preimage (hf : Surjective f) {s : Set β} : (f ⁻¹' s).Nonempty ↔ s.Nonempty := by
  rw [← nonempty_image_iff, hf.image_preimage]

theorem Injective.image_injective (hf : Injective f) : Injective (Image f) := by
  intro s t h
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, h]

theorem Surjective.preimage_subset_preimage_iff {s t : Set β} (hf : Surjective f) : f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t := by
  apply preimage_subset_preimage_iff
  rw [hf.range_eq]
  apply subset_univ

theorem Surjective.range_comp {ι' : Sort _} {f : ι → ι'} (hf : Surjective f) (g : ι' → α) : Range (g ∘ f) = Range g :=
  ext fun y => (@Surjective.exists _ _ _ hf fun x => g x = y).symm

theorem Injective.nonempty_apply_iff {f : Set α → Set β} (hf : Injective f) (h2 : f ∅ = ∅) {s : Set α} :
    (f s).Nonempty ↔ s.Nonempty := by rw [← ne_empty_iff_nonempty, ← h2, ← ne_empty_iff_nonempty, hf.ne_iff]

theorem Injective.mem_range_iff_exists_unique (hf : Injective f) {b : β} : b ∈ Range f ↔ ∃! a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun a' ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

theorem Injective.exists_unique_of_mem_range (hf : Injective f) {b : β} (hb : b ∈ Range f) : ∃! a, f a = b :=
  hf.mem_range_iff_exists_unique.mp hb

theorem Injective.compl_image_eq (hf : Injective f) (s : Set α) : (f '' s)ᶜ = f '' sᶜ ∪ Range fᶜ := by
  ext y
  rcases em (y ∈ range f) with (⟨x, rfl⟩ | hx)
  · simp [hf.eq_iff]
    
  · rw [mem_range, not_exists] at hx
    simp [hx]
    

theorem LeftInverse.image_image {g : β → α} (h : LeftInverse g f) (s : Set α) : g '' (f '' s) = s := by
  rw [← image_comp, h.comp_eq_id, image_id]

theorem LeftInverse.preimage_preimage {g : β → α} (h : LeftInverse g f) (s : Set α) : f ⁻¹' (g ⁻¹' s) = s := by
  rw [← preimage_comp, h.comp_eq_id, preimage_id]

end Function

open Function

theorem Option.injective_iff {α β} {f : Option α → β} :
    Injective f ↔ Injective (f ∘ some) ∧ f none ∉ Range (f ∘ some) := by
  simp only [mem_range, not_exists, (· ∘ ·)]
  refine' ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.Ne <| Option.some_ne_none _⟩, _⟩
  rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab
  exacts[rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]

/-! ### Image and preimage on subtypes -/


namespace Subtype

variable {α : Type _}

theorem coe_image {p : α → Prop} {s : Set (Subtype p)} : coe '' s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext fun a => ⟨fun ⟨⟨a', ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : coe '' { x : ↥s | ↑x ∈ t } = t := by
  ext x
  rw [Set.mem_image]
  exact ⟨fun ⟨x', hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

theorem range_coe {s : Set α} : Range (coe : s → α) = s := by
  rw [← Set.image_univ]
  simp [-Set.image_univ, coe_image]

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {s : Set α} : Range (Subtype.val : s → α) = s :=
  range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp]
theorem range_coe_subtype {p : α → Prop} : Range (coe : Subtype p → α) = { x | p x } :=
  range_coe

@[simp]
theorem coe_preimage_self (s : Set α) : (coe : s → α) ⁻¹' s = univ := by rw [← preimage_range (coe : s → α), range_coe]

theorem range_val_subtype {p : α → Prop} : Range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe

theorem coe_image_subset (s : Set α) (t : Set s) : coe '' t ⊆ s := fun x ⟨y, yt, yvaleq⟩ => by
  rw [← yvaleq] <;> exact y.property

theorem coe_image_univ (s : Set α) : (coe : s → α) '' Set.Univ = s :=
  image_univ.trans range_coe

@[simp]
theorem image_preimage_coe (s t : Set α) : (coe : s → α) '' (coe ⁻¹' t) = t ∩ s :=
  image_preimage_eq_inter_range.trans <| congr_arg _ range_coe

theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) '' (Subtype.val ⁻¹' t) = t ∩ s :=
  image_preimage_coe s t

theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} : (coe : s → α) ⁻¹' t = coe ⁻¹' u ↔ t ∩ s = u ∩ s := by
  rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]

@[simp]
theorem preimage_coe_inter_self (s t : Set α) : (coe : s → α) ⁻¹' (t ∩ s) = coe ⁻¹' t := by
  rw [preimage_coe_eq_preimage_coe_iff, inter_assoc, inter_self]

theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
    (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ t ∩ s = u ∩ s :=
  preimage_coe_eq_preimage_coe_iff

theorem exists_set_subtype {t : Set α} (p : Set α → Prop) : (∃ s : Set t, p (coe '' s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s := by
  constructor
  · rintro ⟨s, hs⟩
    refine' ⟨coe '' s, _, hs⟩
    convert image_subset_range _ _
    rw [range_coe]
    
  rintro ⟨s, hs₁, hs₂⟩
  refine' ⟨coe ⁻¹' s, _⟩
  rw [image_preimage_eq_of_subset]
  exact hs₂
  rw [range_coe]
  exact hs₁

theorem preimage_coe_nonempty {s t : Set α} : ((coe : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty := by
  rw [inter_comm, ← image_preimage_coe, nonempty_image_iff]

theorem preimage_coe_eq_empty {s t : Set α} : (coe : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ := by
  simp only [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

@[simp]
theorem preimage_coe_compl (s : Set α) : (coe : s → α) ⁻¹' sᶜ = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]
theorem preimage_coe_compl' (s : Set α) : (coe : sᶜ → α) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)

end Subtype

namespace Set

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/


section Inclusion

variable {α : Type _} {s t u : Set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion (h : s ⊆ t) : s → t := fun x : s => (⟨x, h x.2⟩ : t)

@[simp]
theorem inclusion_self (x : s) : inclusion Subset.rfl x = x := by
  cases x
  rfl

theorem inclusion_eq_id (h : s ⊆ s) : inclusion h = id :=
  funext inclusion_self

@[simp]
theorem inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl

theorem inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x := by
  cases x
  rfl

@[simp]
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x := by
  cases x
  rfl

@[simp]
theorem inclusion_comp_inclusion {α} {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
  funext (inclusion_inclusion hst htu)

@[simp]
theorem coe_inclusion (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl

theorem inclusion_injective (h : s ⊆ t) : Injective (inclusion h)
  | ⟨_, _⟩, ⟨_, _⟩ => Subtype.ext_iff_val.2 ∘ Subtype.ext_iff_val.1

@[simp]
theorem range_inclusion (h : s ⊆ t) : Range (inclusion h) = { x : t | (x : α) ∈ s } := by
  ext ⟨x, hx⟩
  simp [inclusion]

theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t} (h_surj : Function.Surjective (inclusion h)) : s = t := by
  rw [← range_iff_surjective, range_inclusion, eq_univ_iff_forall] at h_surj
  exact Set.Subset.antisymm h fun x hx => h_surj ⟨x, hx⟩

end Inclusion

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

@[simp]
theorem preimage_injective : Injective (Preimage f) ↔ Surjective f := by
  refine' ⟨fun h y => _, surjective.preimage_injective⟩
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).Nonempty := by
    rw [h.nonempty_apply_iff preimage_empty]
    apply singleton_nonempty
  exact ⟨x, hx⟩

@[simp]
theorem preimage_surjective : Surjective (Preimage f) ↔ Injective f := by
  refine' ⟨fun h x x' hx => _, injective.preimage_surjective⟩
  cases' h {x} with s hs
  have := mem_singleton x
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this

@[simp]
theorem image_surjective : Surjective (Image f) ↔ Surjective f := by
  refine' ⟨fun h y => _, surjective.image_surjective⟩
  cases' h {y} with s hs
  have := mem_singleton y
  rw [← hs] at this
  rcases this with ⟨x, h1x, h2x⟩
  exact ⟨x, h2x⟩

@[simp]
theorem image_injective : Injective (Image f) ↔ Injective f := by
  refine' ⟨fun h x x' hx => _, injective.image_injective⟩
  rw [← singleton_eq_singleton_iff]
  apply h
  rw [image_singleton, image_singleton, hx]

theorem preimage_eq_iff_eq_image {f : α → β} (hf : Bijective f) {s t} : f ⁻¹' s = t ↔ s = f '' t := by
  rw [← image_eq_image hf.1, hf.2.image_preimage]

theorem eq_preimage_iff_image_eq {f : α → β} (hf : Bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t := by
  rw [← image_eq_image hf.1, hf.2.image_preimage]

end ImagePreimage

/-!
### Images of binary and ternary functions

This section is very similar to `order.filter.n_ary`, `data.finset.n_ary`, `data.option.n_ary`.
Please keep them in sync.
-/


section NAryImage

variable {α α' β β' γ γ' δ δ' ε ε' : Type _} {f f' : α → β → γ} {g g' : α → β → γ → δ}

variable {s s' : Set α} {t t' : Set β} {u u' : Set γ} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}

/-- The image of a binary function `f : α → β → γ` as a function `set α → set β → set γ`.
  Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.
-/
def Image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ :=
  { c | ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c }

@[simp]
theorem mem_image2 : c ∈ Image2 f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c :=
  Iff.rfl

theorem mem_image2_of_mem (h1 : a ∈ s) (h2 : b ∈ t) : f a b ∈ Image2 f s t :=
  ⟨a, b, h1, h2, rfl⟩

theorem mem_image2_iff (hf : Injective2 f) : f a b ∈ Image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by
    rintro ⟨a', b', ha', hb', h⟩
    rcases hf h with ⟨rfl, rfl⟩
    exact ⟨ha', hb'⟩, fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
theorem image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : Image2 f s t ⊆ Image2 f s' t' := by
  rintro _ ⟨a, b, ha, hb, rfl⟩
  exact mem_image2_of_mem (hs ha) (ht hb)

theorem image2_subset_left (ht : t ⊆ t') : Image2 f s t ⊆ Image2 f s t' :=
  image2_subset Subset.rfl ht

theorem image2_subset_right (hs : s ⊆ s') : Image2 f s t ⊆ Image2 f s' t :=
  image2_subset hs Subset.rfl

theorem image_subset_image2_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ Image2 f s t :=
  ball_image_of_ball fun a ha => mem_image2_of_mem ha hb

theorem image_subset_image2_right (ha : a ∈ s) : f a '' t ⊆ Image2 f s t :=
  ball_image_of_ball fun b => mem_image2_of_mem ha

theorem forall_image2_iff {p : γ → Prop} : (∀ z ∈ Image2 f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) :=
  ⟨fun h x hx y hy => h _ ⟨x, y, hx, hy, rfl⟩, fun h z ⟨x, y, hx, hy, hz⟩ => hz ▸ h x hx y hy⟩

@[simp]
theorem image2_subset_iff {u : Set γ} : Image2 f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_image2_iff

theorem image2_union_left : Image2 f (s ∪ s') t = Image2 f s t ∪ Image2 f s' t := by
  ext c
  constructor
  · rintro ⟨a, b, h1a | h2a, hb, rfl⟩ <;> [left, right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
    
  · rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, _, ‹_›, rfl⟩ <;> simp [mem_union, *]
    

theorem image2_union_right : Image2 f s (t ∪ t') = Image2 f s t ∪ Image2 f s t' := by
  ext c
  constructor
  · rintro ⟨a, b, ha, h1b | h2b, rfl⟩ <;> [left, right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
    
  · rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, ‹_›, _, rfl⟩ <;> simp [mem_union, *]
    

@[simp]
theorem image2_empty_left : Image2 f ∅ t = ∅ :=
  ext <| by simp

@[simp]
theorem image2_empty_right : Image2 f s ∅ = ∅ :=
  ext <| by simp

theorem Nonempty.image2 : s.Nonempty → t.Nonempty → (Image2 f s t).Nonempty := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
  ⟨_, mem_image2_of_mem ha hb⟩

@[simp]
theorem image2_nonempty_iff : (Image2 f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun ⟨_, a, b, ha, hb, _⟩ => ⟨⟨a, ha⟩, b, hb⟩, fun h => h.1.Image2 h.2⟩

theorem Nonempty.of_image2_left (h : (Image2 f s t).Nonempty) : s.Nonempty :=
  (image2_nonempty_iff.1 h).1

theorem Nonempty.of_image2_right (h : (Image2 f s t).Nonempty) : t.Nonempty :=
  (image2_nonempty_iff.1 h).2

@[simp]
theorem image2_eq_empty_iff : Image2 f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp_rw [← not_nonempty_iff_eq_empty, image2_nonempty_iff, not_and_or]

theorem image2_inter_subset_left : Image2 f (s ∩ s') t ⊆ Image2 f s t ∩ Image2 f s' t := by
  rintro _ ⟨a, b, ⟨h1a, h2a⟩, hb, rfl⟩
  constructor <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩

theorem image2_inter_subset_right : Image2 f s (t ∩ t') ⊆ Image2 f s t ∩ Image2 f s t' := by
  rintro _ ⟨a, b, ha, ⟨h1b, h2b⟩, rfl⟩
  constructor <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩

@[simp]
theorem image2_singleton_left : Image2 f {a} t = f a '' t :=
  ext fun x => by simp

@[simp]
theorem image2_singleton_right : Image2 f s {b} = (fun a => f a b) '' s :=
  ext fun x => by simp

theorem image2_singleton : Image2 f {a} {b} = {f a b} := by simp

@[congr]
theorem image2_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : Image2 f s t = Image2 f' s t := by
  ext
  constructor <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> refine' ⟨a, b, ha, hb, by rw [h a ha b hb]⟩

/-- A common special case of `image2_congr` -/
theorem image2_congr' (h : ∀ a b, f a b = f' a b) : Image2 f s t = Image2 f' s t :=
  image2_congr fun a _ b _ => h a b

/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `set α → set β → set γ → set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def Image3 (g : α → β → γ → δ) (s : Set α) (t : Set β) (u : Set γ) : Set δ :=
  { d | ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d }

@[simp]
theorem mem_image3 : d ∈ Image3 g s t u ↔ ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
  Iff.rfl

theorem image3_mono (hs : s ⊆ s') (ht : t ⊆ t') (hu : u ⊆ u') : Image3 g s t u ⊆ Image3 g s' t' u' := fun x =>
  Exists₃Cat.imp fun a b c ⟨ha, hb, hc, hx⟩ => ⟨hs ha, ht hb, hu hc, hx⟩

@[congr]
theorem image3_congr (h : ∀ a ∈ s, ∀ b ∈ t, ∀ c ∈ u, g a b c = g' a b c) : Image3 g s t u = Image3 g' s t u := by
  ext x
  constructor <;> rintro ⟨a, b, c, ha, hb, hc, rfl⟩ <;> exact ⟨a, b, c, ha, hb, hc, by rw [h a ha b hb c hc]⟩

/-- A common special case of `image3_congr` -/
theorem image3_congr' (h : ∀ a b c, g a b c = g' a b c) : Image3 g s t u = Image3 g' s t u :=
  image3_congr fun a _ b _ c _ => h a b c

theorem image2_image2_left (f : δ → γ → ε) (g : α → β → δ) :
    Image2 f (Image2 g s t) u = Image3 (fun a b c => f (g a b) c) s t u := by
  ext
  constructor
  · rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
    refine' ⟨a, b, c, ha, hb, hc, rfl⟩
    
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine' ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
    

theorem image2_image2_right (f : α → δ → ε) (g : β → γ → δ) :
    Image2 f s (Image2 g t u) = Image3 (fun a b c => f a (g b c)) s t u := by
  ext
  constructor
  · rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
    refine' ⟨a, b, c, ha, hb, hc, rfl⟩
    
  · rintro ⟨a, b, c, ha, hb, hc, rfl⟩
    refine' ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
    

theorem image_image2 (f : α → β → γ) (g : γ → δ) : g '' Image2 f s t = Image2 (fun a b => g (f a b)) s t := by
  ext
  constructor
  · rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
    
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    

theorem image2_image_left (f : γ → β → δ) (g : α → γ) : Image2 f (g '' s) t = Image2 (fun a b => f (g a) b) s t := by
  ext
  constructor
  · rintro ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
    
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
    

theorem image2_image_right (f : α → γ → δ) (g : β → γ) : Image2 f s (g '' t) = Image2 (fun a b => f a (g b)) s t := by
  ext
  constructor
  · rintro ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
    refine' ⟨a, b, ha, hb, rfl⟩
    
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine' ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
    

theorem image2_swap (f : α → β → γ) (s : Set α) (t : Set β) : Image2 f s t = Image2 (fun a b => f b a) t s := by
  ext
  constructor <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> refine' ⟨b, a, hb, ha, rfl⟩

@[simp]
theorem image2_left (h : t.Nonempty) : Image2 (fun x y => x) s t = s := by simp [nonempty_def.mp h, ext_iff]

@[simp]
theorem image2_right (h : s.Nonempty) : Image2 (fun x y => y) s t = t := by simp [nonempty_def.mp h, ext_iff]

theorem image2_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) : Image2 f (Image2 g s t) u = Image2 f' s (Image2 g' t u) := by
  simp only [image2_image2_left, image2_image2_right, h_assoc]

theorem image2_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : Image2 f s t = Image2 g t s :=
  (image2_swap _ _ _).trans <| by simp_rw [h_comm]

theorem image2_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) : Image2 f s (Image2 g t u) = Image2 g' t (Image2 f' s u) := by
  rw [image2_swap f', image2_swap f]
  exact image2_assoc fun _ _ _ => h_left_comm _ _ _

theorem image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) : Image2 f (Image2 g s t) u = Image2 g' (Image2 f' s u) t :=
  by
  rw [image2_swap g, image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _

theorem image_image2_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) : (Image2 f s t).Image g = Image2 f' (s.Image g₁) (t.Image g₂) :=
  by simp_rw [image_image2, image2_image_left, image2_image_right, h_distrib]

/-- Symmetric statement to `set.image2_image_left_comm`. -/
theorem image_image2_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) : (Image2 f s t).Image g = Image2 f' (s.Image g') t :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']

/-- Symmetric statement to `set.image_image2_right_comm`. -/
theorem image_image2_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) : (Image2 f s t).Image g = Image2 f' s (t.Image g') :=
  (image_image2_distrib h_distrib).trans <| by rw [image_id']

/-- Symmetric statement to `set.image_image2_distrib_left`. -/
theorem image2_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) : Image2 f (s.Image g) t = (Image2 f' s t).Image g' :=
  (image_image2_distrib_left fun a b => (h_left_comm a b).symm).symm

/-- Symmetric statement to `set.image_image2_distrib_right`. -/
theorem image_image2_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) : Image2 f s (t.Image g) = (Image2 f' s t).Image g' :=
  (image_image2_distrib_right fun a b => (h_right_comm a b).symm).symm

/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image2_distrib_subset_left {f : α → δ → ε} {g : β → γ → δ} {f₁ : α → β → β'} {f₂ : α → γ → γ'}
    {g' : β' → γ' → ε} (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    Image2 f s (Image2 g t u) ⊆ Image2 g' (Image2 f₁ s t) (Image2 f₂ s u) := by
  rintro _ ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hb) (mem_image2_of_mem ha hc)

/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image2_distrib_subset_right {f : δ → γ → ε} {g : α → β → δ} {f₁ : α → γ → α'} {f₂ : β → γ → β'}
    {g' : α' → β' → ε} (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    Image2 f (Image2 g s t) u ⊆ Image2 g' (Image2 f₁ s u) (Image2 f₂ t u) := by
  rintro _ ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
  rw [h_distrib]
  exact mem_image2_of_mem (mem_image2_of_mem ha hc) (mem_image2_of_mem hb hc)

theorem image_image2_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (Image2 f s t).Image g = Image2 f' (t.Image g₁) (s.Image g₂) := by
  rw [image2_swap f]
  exact image_image2_distrib fun _ _ => h_antidistrib _ _

/-- Symmetric statement to `set.image2_image_left_anticomm`. -/
theorem image_image2_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) : (Image2 f s t).Image g = Image2 f' (t.Image g') s :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']

/-- Symmetric statement to `set.image_image2_right_anticomm`. -/
theorem image_image2_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) : (Image2 f s t).Image g = Image2 f' t (s.Image g') :=
  (image_image2_antidistrib h_antidistrib).trans <| by rw [image_id']

/-- Symmetric statement to `set.image_image2_antidistrib_left`. -/
theorem image2_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) : Image2 f (s.Image g) t = (Image2 f' t s).Image g' :=
  (image_image2_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm

/-- Symmetric statement to `set.image_image2_antidistrib_right`. -/
theorem image_image2_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) : Image2 f s (t.Image g) = (Image2 f' t s).Image g' :=
  (image_image2_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm

end NAryImage

end Set

namespace Subsingleton

variable {α : Type _} [Subsingleton α]

theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty → s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx

@[elab_as_elim]
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p Univ) (s) : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1

theorem mem_iff_nonempty {α : Type _} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩

end Subsingleton

/-! ### Decidability instances for sets -/


namespace Set

variable {α : Type u} (s t : Set α) (a : α)

instance decidableSdiff [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s \ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∉ t))

instance decidableInter [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∩ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∈ t))

instance decidableUnion [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∪ t) :=
  (by infer_instance : Decidable (a ∈ s ∨ a ∈ t))

instance decidableCompl [Decidable (a ∈ s)] : Decidable (a ∈ sᶜ) :=
  (by infer_instance : Decidable (a ∉ s))

instance decidableEmptyset : DecidablePred (· ∈ (∅ : Set α)) := fun _ => Decidable.isFalse (by simp)

instance decidableUniv : DecidablePred (· ∈ (Set.Univ : Set α)) := fun _ => Decidable.isTrue (by simp)

instance decidableSetOf (p : α → Prop) [Decidable (p a)] : Decidable (a ∈ { a | p a }) := by assumption

end Set

/-! ### Indicator function valued in bool -/


open Bool

namespace Set

variable {α : Type _} (s : Set α)

/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x ∈ s) (Classical.propDecidable _) true false

theorem mem_iff_bool_indicator (x : α) : x ∈ s ↔ s.boolIndicator x = tt := by
  unfold bool_indicator
  split_ifs <;> tauto

theorem not_mem_iff_bool_indicator (x : α) : x ∉ s ↔ s.boolIndicator x = ff := by
  unfold bool_indicator
  split_ifs <;> tauto

theorem preimage_bool_indicator_tt : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x => (s.mem_iff_bool_indicator x).symm

theorem preimage_bool_indicator_ff : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x => (s.not_mem_iff_bool_indicator x).symm

open Classical

theorem preimage_bool_indicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if tt ∈ t then s else ∅) ∪ if ff ∈ t then sᶜ else ∅ := by
  ext x
  dsimp [bool_indicator]
  split_ifs <;> tauto

theorem preimage_bool_indicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨ s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ :=
  by
  simp only [preimage_bool_indicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]

end Set

