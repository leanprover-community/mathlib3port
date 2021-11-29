import Mathbin.Logic.Unique 
import Mathbin.Order.BooleanAlgebra

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

* `strict_subset s₁ s₂ : Prop` : the predicate `s₁ ⊆ s₂` but `s₁ ≠ s₂`.

* `nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

* `s.prod t : set (α × β)` : the subset `s × t`.

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

run_cmd 
  do 
      let e ← tactic.get_env 
      tactic.set_env$ e.mk_protected `set.compl

theorem HasSubset.Subset.trans {α : Type _} [HasSubset α] [IsTrans α (· ⊆ ·)] {a b c : α} (h : a ⊆ b) (h' : b ⊆ c) :
  a ⊆ c :=
  trans h h'

theorem HasSubset.Subset.antisymm {α : Type _} [HasSubset α] [IsAntisymm α (· ⊆ ·)] {a b : α} (h : a ⊆ b) (h' : b ⊆ a) :
  a = b :=
  antisymm h h'

theorem HasSsubset.Ssubset.trans {α : Type _} [HasSsubset α] [IsTrans α (· ⊂ ·)] {a b c : α} (h : a ⊂ b) (h' : b ⊂ c) :
  a ⊂ c :=
  trans h h'

theorem HasSsubset.Ssubset.asymm {α : Type _} [HasSsubset α] [IsAsymm α (· ⊂ ·)] {a b : α} (h : a ⊂ b) : ¬b ⊂ a :=
  asymm h

namespace Set

variable {α : Type _}

instance : LE (Set α) :=
  ⟨· ⊆ ·⟩

instance : LT (Set α) :=
  ⟨fun s t => s ≤ t ∧ ¬t ≤ s⟩

instance {α : Type _} : BooleanAlgebra (Set α) :=
  { (inferInstance : BooleanAlgebra (α → Prop)) with sup := · ∪ ·, le := · ≤ ·, lt := · < ·, inf := · ∩ ·, bot := ∅,
    Compl := Set.Compl, top := univ, sdiff := · \ · }

@[simp]
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl

@[simp]
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl

@[simp]
theorem sup_eq_union : (·⊔· : Set α → Set α → Set α) = · ∪ · :=
  rfl

@[simp]
theorem inf_eq_inter : (·⊓· : Set α → Set α → Set α) = · ∩ · :=
  rfl

@[simp]
theorem le_eq_subset : (· ≤ · : Set α → Set α → Prop) = (· ⊆ ·) :=
  rfl

/-! `set.lt_eq_ssubset` is defined further down -/


@[simp]
theorem compl_eq_compl : Set.Compl = (HasCompl.compl : Set α → Set α) :=
  rfl

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Set α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

instance pi_set_coe.can_lift (ι : Type u) (α : ∀ i : ι, Type v) [ne : ∀ i, Nonempty (α i)] (s : Set ι) :
  CanLift (∀ i : s, α i) (∀ i, α i) :=
  { PiSubtype.canLift ι α s with coe := fun f i => f i }

instance pi_set_coe.can_lift' (ι : Type u) (α : Type v) [ne : Nonempty α] (s : Set ι) : CanLift (s → α) (ι → α) :=
  pi_set_coe.can_lift ι (fun _ => α) s

instance set_coe.can_lift (s : Set α) : CanLift α s :=
  { coe := coeₓ, cond := fun a => a ∈ s, prf := fun a ha => ⟨⟨a, ha⟩, rfl⟩ }

end Set

section SetCoe

variable {α : Type u}

theorem Set.set_coe_eq_subtype (s : Set α) : coeSortₓ.{u + 1, u + 2} s = { x // x ∈ s } :=
  rfl

@[simp]
theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ x h : x ∈ s, p ⟨x, h⟩ :=
  Subtype.forall

@[simp]
theorem SetCoe.exists {s : Set α} {p : s → Prop} : (∃ x : s, p x) ↔ ∃ (x : _)(h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists

theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} : (∃ (x : _)(h : x ∈ s), p x h) ↔ ∃ x : s, p x x.2 :=
  (@SetCoe.exists _ _$ fun x => p x.1 x.2).symm

theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} : (∀ x h : x ∈ s, p x h) ↔ ∀ x : s, p x x.2 :=
  (@SetCoe.forall _ _$ fun x => p x.1 x.2).symm

@[simp]
theorem set_coe_cast : ∀ {s t : Set α} H' : s = t H : @Eq (Type u) s t x : s, cast H x = ⟨x.1, H' ▸ x.2⟩
| s, _, rfl, _, ⟨x, h⟩ => rfl

theorem SetCoe.ext {s : Set α} {a b : s} : («expr↑ » a : α) = «expr↑ » b → a = b :=
  Subtype.eq

theorem SetCoe.ext_iff {s : Set α} {a b : s} : («expr↑ » a : α) = «expr↑ » b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl

end SetCoe

/-- See also `subtype.prop` -/
theorem Subtype.mem {α : Type _} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.prop

theorem Eq.subset {α} {s t : Set α} : s = t → s ⊆ t :=
  by 
    rintro rfl x hx 
    exact hx

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a : α} {s t : Set α}

instance : Inhabited (Set α) :=
  ⟨∅⟩

@[ext]
theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext fun x => propext (h x)

theorem ext_iff {s t : Set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
  ⟨fun h x =>
      by 
        rw [h],
    ext⟩

@[trans]
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx

/-! ### Lemmas about `mem` and `set_of` -/


@[simp]
theorem mem_set_of_eq {a : α} {p : α → Prop} : (a ∈ { a | p a }) = p a :=
  rfl

theorem nmem_set_of_eq {a : α} {P : α → Prop} : (a ∉ { a:α | P a }) = ¬P a :=
  rfl

@[simp]
theorem set_of_mem_eq {s : Set α} : { x | x ∈ s } = s :=
  rfl

theorem set_of_set {s : Set α} : SetOf s = s :=
  rfl

theorem set_of_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x :=
  Iff.rfl

theorem mem_def {a : α} {s : Set α} : a ∈ s ↔ s a :=
  Iff.rfl

instance decidable_set_of (p : α → Prop) [H : DecidablePred p] : DecidablePred (· ∈ { a | p a }) :=
  H

@[simp]
theorem set_of_subset_set_of {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl

@[simp]
theorem sep_set_of {p q : α → Prop} : { a∈{ a | p a } | q a } = { a | p a ∧ q a } :=
  rfl

theorem set_of_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl

theorem set_of_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl

/-! ### Lemmas about subsets -/


theorem subset_def {s t : Set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl

@[refl]
theorem subset.refl (a : Set α) : a ⊆ a :=
  fun x => id

theorem subset.rfl {s : Set α} : s ⊆ s :=
  subset.refl s

@[trans]
theorem subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c :=
  fun x h => bc (ab h)

@[trans]
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
  hx.symm ▸ h

theorem subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  Set.ext$ fun x => ⟨@h₁ _, @h₂ _⟩

theorem subset.antisymm_iff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨e.subset, e.symm.subset⟩, fun ⟨h₁, h₂⟩ => subset.antisymm h₁ h₂⟩

theorem eq_of_subset_of_subset {a b : Set α} : a ⊆ b → b ⊆ a → a = b :=
  subset.antisymm

theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
  @h _

theorem not_mem_subset (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt$ mem_of_subset_of_mem h

theorem not_subset : ¬s ⊆ t ↔ ∃ (a : _)(_ : a ∈ s), a ∉ t :=
  by 
    simp only [subset_def, not_forall]

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/


instance : HasSsubset (Set α) :=
  ⟨· < ·⟩

@[simp]
theorem lt_eq_ssubset : (· < · : Set α → Set α → Prop) = (· ⊂ ·) :=
  rfl

theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬t ⊆ s) :=
  rfl

theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h

theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : ∃ (x : _)(_ : x ∈ t), x ∉ s :=
  not_subset.1 h.2

theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne (Set α) _ s t

theorem ssubset_iff_of_subset {s t : Set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ (x : _)(_ : x ∈ t), x ∉ s :=
  ⟨exists_of_ssubset, fun ⟨x, hxt, hxs⟩ => ⟨h, fun h => hxs$ h hxt⟩⟩

theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  ⟨subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (subset.trans hs₂s₃ hs₃s₁)⟩

theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (subset.trans hs₃s₁ hs₁s₂)⟩

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
theorem nonempty_coe_sort (s : Set α) : Nonempty («expr↥ » s) ↔ s.nonempty :=
  nonempty_subtype

theorem nonempty_def : s.nonempty ↔ ∃ x, x ∈ s :=
  Iff.rfl

theorem nonempty_of_mem {x} (h : x ∈ s) : s.nonempty :=
  ⟨x, h⟩

theorem nonempty.not_subset_empty : s.nonempty → ¬s ⊆ ∅
| ⟨x, hx⟩, hs => hs hx

theorem nonempty.ne_empty : ∀ {s : Set α}, s.nonempty → s ≠ ∅
| _, ⟨x, hx⟩, rfl => hx

@[simp]
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty :=
  fun h => h.ne_empty rfl

/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected noncomputable def Nonempty.some (h : s.nonempty) : α :=
  Classical.some h

protected theorem nonempty.some_mem (h : s.nonempty) : h.some ∈ s :=
  Classical.some_spec h

theorem nonempty.mono (ht : s ⊆ t) (hs : s.nonempty) : t.nonempty :=
  hs.imp ht

theorem nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩

theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2

theorem nonempty.of_diff (h : (s \ t).Nonempty) : s.nonempty :=
  h.imp$ fun _ => And.left

theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.nonempty :=
  (nonempty_of_ssubset ht).of_diff

theorem nonempty.inl (hs : s.nonempty) : (s ∪ t).Nonempty :=
  hs.imp$ fun _ => Or.inl

theorem nonempty.inr (ht : t.nonempty) : (s ∪ t).Nonempty :=
  ht.imp$ fun _ => Or.inr

@[simp]
theorem union_nonempty : (s ∪ t).Nonempty ↔ s.nonempty ∨ t.nonempty :=
  exists_or_distrib

theorem nonempty.left (h : (s ∩ t).Nonempty) : s.nonempty :=
  h.imp$ fun _ => And.left

theorem nonempty.right (h : (s ∩ t).Nonempty) : t.nonempty :=
  h.imp$ fun _ => And.right

theorem nonempty_inter_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x : t, «expr↑ » x ∈ s :=
  ⟨fun ⟨x, xs, xt⟩ => ⟨⟨x, xt⟩, xs⟩, fun ⟨⟨x, xt⟩, xs⟩ => ⟨x, xs, xt⟩⟩

theorem nonempty_inter_iff_exists_left : (s ∩ t).Nonempty ↔ ∃ x : s, «expr↑ » x ∈ t :=
  ⟨fun ⟨x, xs, xt⟩ => ⟨⟨x, xs⟩, xt⟩, fun ⟨⟨x, xt⟩, xs⟩ => ⟨x, xt, xs⟩⟩

theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivialₓ⟩, fun ⟨x, _⟩ => ⟨x⟩⟩

@[simp]
theorem univ_nonempty : ∀ [h : Nonempty α], (univ : Set α).Nonempty
| ⟨x⟩ => ⟨x, trivialₓ⟩

theorem nonempty.to_subtype (h : s.nonempty) : Nonempty s :=
  nonempty_subtype.2 h

instance [Nonempty α] : Nonempty (Set.Univ : Set α) :=
  Set.univ_nonempty.to_subtype

@[simp]
theorem nonempty_insert (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, Or.inl rfl⟩

theorem nonempty_of_nonempty_subtype [Nonempty s] : s.nonempty :=
  nonempty_subtype.mp ‹_›

/-! ### Lemmas about the empty set -/


theorem empty_def : (∅ : Set α) = { x | False } :=
  rfl

@[simp]
theorem mem_empty_eq (x : α) : (x ∈ (∅ : Set α)) = False :=
  rfl

@[simp]
theorem set_of_false : { a:α | False } = ∅ :=
  rfl

@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  fun.

theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ s = ∅ :=
  (subset.antisymm_iff.trans$ and_iff_left (empty_subset _)).symm

theorem eq_empty_iff_forall_not_mem {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  subset_empty_iff.symm

theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ :=
  subset_empty_iff.1

theorem eq_empty_of_is_empty [IsEmpty α] (s : Set α) : s = ∅ :=
  eq_empty_of_subset_empty$ fun x hx => isEmptyElim x

/-- There is exactly one set of a type that is empty. -/
def unique_empty [IsEmpty α] : Unique (Set α) :=
  { default := ∅, uniq := eq_empty_of_is_empty }

theorem not_nonempty_iff_eq_empty {s : Set α} : ¬s.nonempty ↔ s = ∅ :=
  by 
    simp only [Set.Nonempty, eq_empty_iff_forall_not_mem, not_exists]

theorem empty_not_nonempty : ¬(∅ : Set α).Nonempty :=
  fun h => h.ne_empty rfl

theorem ne_empty_iff_nonempty : s ≠ ∅ ↔ s.nonempty :=
  not_iff_comm.1 not_nonempty_iff_eq_empty

theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.nonempty :=
  or_iff_not_imp_left.2 ne_empty_iff_nonempty.1

theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1$ e ▸ h

theorem ball_empty_iff {p : α → Prop} : (∀ x _ : x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro$ fun x => False.elim

instance (α : Type u) : IsEmpty.{u + 1} (∅ : Set α) :=
  ⟨fun x => x.2⟩

/-!

### Universal set.

In Lean `@univ α` (or `univ : set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


@[simp]
theorem set_of_true : { x:α | True } = univ :=
  rfl

@[simp]
theorem mem_univ (x : α) : x ∈ @univ α :=
  trivialₓ

@[simp]
theorem univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_not_mem.trans ⟨fun H => ⟨fun x => H x trivialₓ⟩, fun H x _ => @IsEmpty.false α H x⟩

theorem empty_ne_univ [Nonempty α] : (∅ : Set α) ≠ univ :=
  fun e => not_is_empty_of_nonempty α$ univ_eq_empty_iff.1 e.symm

@[simp]
theorem subset_univ (s : Set α) : s ⊆ univ :=
  fun x H => trivialₓ

theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ :=
  (subset.antisymm_iff.trans$ and_iff_right (subset_univ _)).symm

theorem eq_univ_of_univ_subset {s : Set α} : univ ⊆ s → s = univ :=
  univ_subset_iff.1

theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans$ forall_congrₓ$ fun x => imp_iff_right ⟨⟩

theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset$ hs ▸ h

theorem exists_mem_of_nonempty α : ∀ [Nonempty α], ∃ x : α, x ∈ (univ : Set α)
| ⟨x⟩ => ⟨x, trivialₓ⟩

instance univ_decidable : DecidablePred (· ∈ @Set.Univ α) :=
  fun x => is_true trivialₓ

theorem ne_univ_iff_exists_not_mem {α : Type _} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s :=
  by 
    rw [←not_forall, ←eq_univ_iff_forall]

theorem not_subset_iff_exists_mem_not_mem {α : Type _} {s t : Set α} : ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t :=
  by 
    simp [subset_def]

/-- `diagonal α` is the subset of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type _) : Set (α × α) :=
  { p | p.1 = p.2 }

@[simp]
theorem mem_diagonal {α : Type _} (x : α) : (x, x) ∈ diagonal α :=
  by 
    simp [diagonal]

/-! ### Lemmas about union -/


theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ } :=
  rfl

theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x ∈ a → x ∈ a ∪ b :=
  Or.inl

theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x ∈ b → x ∈ a ∪ b :=
  Or.inr

theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b :=
  H

theorem mem_union.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
  Or.elim H₁ H₂ H₃

theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  Iff.rfl

@[simp]
theorem mem_union_eq (x : α) (a b : Set α) : (x ∈ a ∪ b) = (x ∈ a ∨ x ∈ b) :=
  rfl

@[simp]
theorem union_self (a : Set α) : a ∪ a = a :=
  ext$ fun x => or_selfₓ _

@[simp]
theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  ext$ fun x => or_falseₓ _

@[simp]
theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  ext$ fun x => false_orₓ _

theorem union_comm (a b : Set α) : a ∪ b = b ∪ a :=
  ext$ fun x => Or.comm

theorem union_assoc (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext$ fun x => Or.assoc

instance union_is_assoc : IsAssociative (Set α) (· ∪ ·) :=
  ⟨union_assoc⟩

instance union_is_comm : IsCommutative (Set α) (· ∪ ·) :=
  ⟨union_comm⟩

theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext$ fun x => Or.left_comm

theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext$ fun x => Or.right_comm

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
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t :=
  fun x => Or.inl

@[simp]
theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t :=
  fun x => Or.inr

theorem union_subset {s t r : Set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
  fun x => Or.ndrec (@sr _) (@tr _)

@[simp]
theorem union_subset_iff {s t u : Set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (forall_congrₓ
        (by 
          exact fun x => or_imp_distrib)).trans
    forall_and_distrib

theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∪ t₁ ⊆ s₂ ∪ t₂ :=
  fun x => Or.imp (@h₁ _) (@h₂ _)

theorem union_subset_union_left {s₁ s₂ : Set α} t (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h subset.rfl

theorem union_subset_union_right s {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union subset.rfl h

theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  subset.trans h (subset_union_left t u)

theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  subset.trans h (subset_union_right t u)

@[simp]
theorem union_empty_iff {s t : Set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ :=
  by 
    simp only [←subset_empty_iff] <;> exact union_subset_iff

@[simp]
theorem union_univ {s : Set α} : s ∪ univ = univ :=
  sup_top_eq

@[simp]
theorem univ_union {s : Set α} : univ ∪ s = univ :=
  top_sup_eq

/-! ### Lemmas about intersection -/


theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ } :=
  rfl

theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  Iff.rfl

@[simp]
theorem mem_inter_eq (x : α) (a b : Set α) : (x ∈ a ∩ b) = (x ∈ a ∧ x ∈ b) :=
  rfl

theorem mem_inter {x : α} {a b : Set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
  ⟨ha, hb⟩

theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ a :=
  h.left

theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ b :=
  h.right

@[simp]
theorem inter_self (a : Set α) : a ∩ a = a :=
  ext$ fun x => and_selfₓ _

@[simp]
theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  ext$ fun x => and_falseₓ _

@[simp]
theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  ext$ fun x => false_andₓ _

theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a :=
  ext$ fun x => And.comm

theorem inter_assoc (a b c : Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext$ fun x => And.assoc

instance inter_is_assoc : IsAssociative (Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩

instance inter_is_comm : IsCommutative (Set α) (· ∩ ·) :=
  ⟨inter_comm⟩

theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext$ fun x => And.left_comm

theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext$ fun x => And.right_comm

@[simp]
theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s :=
  fun x => And.left

@[simp]
theorem inter_subset_right (s t : Set α) : s ∩ t ⊆ t :=
  fun x => And.right

theorem subset_inter {s t r : Set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
  fun x h => ⟨rs h, rt h⟩

@[simp]
theorem subset_inter_iff {s t r : Set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  (forall_congrₓ
        (by 
          exact fun x => imp_and_distrib)).trans
    forall_and_distrib

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

@[simp]
theorem inter_univ (a : Set α) : a ∩ univ = a :=
  inf_top_eq

@[simp]
theorem univ_inter (a : Set α) : univ ∩ a = a :=
  top_inf_eq

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
  fun x => And.imp (@h₁ _) (@h₂ _)

theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H subset.rfl

theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter subset.rfl H

theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right$ subset_union_left _ _

theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right$ subset_union_right _ _

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

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/


theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl

@[simp]
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s :=
  fun y => Or.inr

theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
  Or.inl rfl

theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr

theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
  id

theorem mem_of_mem_insert_of_ne {x a : α} {s : Set α} : x ∈ insert a s → x ≠ a → x ∈ s :=
  Or.resolve_left

@[simp]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl

@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s :=
  ext$ fun x => or_iff_right_of_imp$ fun e => e.symm ▸ h

theorem ne_insert_of_not_mem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t :=
  mt$ fun e => e.symm ▸ mem_insert _ _

theorem insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  by 
    simp only [subset_def, or_imp_distrib, forall_and_distrib, forall_eq, mem_insert_iff]

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t :=
  fun x => Or.imp_rightₓ (@h _)

theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t :=
  by 
    refine' ⟨fun h x hx => _, insert_subset_insert⟩
    rcases h (subset_insert _ _ hx) with (rfl | hxt)
    exacts[(ha hx).elim, hxt]

theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ (a : _)(_ : a ∉ s), insert a s ⊆ t :=
  by 
    simp only [insert_subset, exists_and_distrib_right, ssubset_def, not_subset]
    simp only [exists_prop, and_comm]

theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff_insert.2 ⟨a, h, subset.refl _⟩

theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) :=
  ext$ fun x => Or.left_comm

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
  ext$ fun x => Or.assoc

@[simp]
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
  ext$ fun x => Or.left_comm

theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

theorem insert_inter (x : α) (s t : Set α) : insert x (s ∩ t) = insert x s ∩ insert x t :=
  ext$ fun y => or_and_distrib_left

theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x) x (h : x ∈ s) :
  P x :=
  H _ (Or.inr h)

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a) x
  (h : x ∈ insert a s) : P x :=
  h.elim (fun e => e.symm ▸ ha) (H _)

theorem bex_insert_iff {P : α → Prop} {a : α} {s : Set α} :
  (∃ (x : _)(_ : x ∈ insert a s), P x) ↔ P a ∨ ∃ (x : _)(_ : x ∈ s), P x :=
  bex_or_left_distrib.trans$ or_congr_left bex_eq_left

theorem ball_insert_iff {P : α → Prop} {a : α} {s : Set α} : (∀ x _ : x ∈ insert a s, P x) ↔ P a ∧ ∀ x _ : x ∈ s, P x :=
  ball_or_left_distrib.trans$ and_congr_left' forall_eq

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
  ext$ fun x => eq_comm

@[simp]
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
  @rfl _ _

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h

@[simp]
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  ext_iff.trans eq_iff_eq_cancel_left

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
  H

theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) ∪ s :=
  rfl

@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _

theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _

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
theorem singleton_inter_nonempty : ({a} ∩ s).Nonempty ↔ a ∈ s :=
  by 
    simp only [Set.Nonempty, mem_inter_eq, mem_singleton_iff, exists_eq_left]

@[simp]
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s :=
  by 
    rw [inter_comm, singleton_inter_nonempty]

@[simp]
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans$ not_congr singleton_inter_nonempty

@[simp]
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s :=
  by 
    rw [inter_comm, singleton_inter_eq_empty]

theorem nmem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.nonempty :=
  ne_empty_iff_nonempty

instance unique_singleton (a : α) : Unique («expr↥ » ({a} : Set α)) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨x, h⟩ => Subtype.eq h⟩

theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x _ : x ∈ s, x = a :=
  subset.antisymm_iff.trans$ And.comm.trans$ and_congr_left' singleton_subset_iff

theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.nonempty ∧ ∀ x _ : x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans$ and_congr_left$ fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩

theorem exists_eq_singleton_iff_nonempty_unique_mem :
  (∃ a : α, s = {a}) ↔ s.nonempty ∧ ∀ a b _ : a ∈ s _ : b ∈ s, a = b :=
  by 
    refine' ⟨_, fun h => _⟩
    ·
      rintro ⟨a, rfl⟩
      refine' ⟨Set.singleton_nonempty a, fun b c hb hc => hb.trans hc.symm⟩
    ·
      obtain ⟨a, ha⟩ := h.1
      refine' ⟨a, set.eq_singleton_iff_unique_mem.mpr ⟨ha, fun b hb => h.2 b a hb ha⟩⟩

@[simp]
theorem default_coe_singleton (x : α) : default ({x} : Set α) = ⟨x, rfl⟩ :=
  rfl

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/


theorem mem_sep {s : Set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) : x ∈ { x∈s | p x } :=
  ⟨xs, px⟩

@[simp]
theorem sep_mem_eq {s t : Set α} : { x∈s | x ∈ t } = s ∩ t :=
  rfl

@[simp]
theorem mem_sep_eq {s : Set α} {p : α → Prop} {x : α} : (x ∈ { x∈s | p x }) = (x ∈ s ∧ p x) :=
  rfl

theorem mem_sep_iff {s : Set α} {p : α → Prop} {x : α} : x ∈ { x∈s | p x } ↔ x ∈ s ∧ p x :=
  Iff.rfl

theorem eq_sep_of_subset {s t : Set α} (h : s ⊆ t) : s = { x∈t | x ∈ s } :=
  (inter_eq_self_of_subset_right h).symm

@[simp]
theorem sep_subset (s : Set α) (p : α → Prop) : { x∈s | p x } ⊆ s :=
  fun x => And.left

theorem forall_not_of_sep_empty {s : Set α} {p : α → Prop} (H : { x∈s | p x } = ∅) x : x ∈ s → ¬p x :=
  not_and.1 (eq_empty_iff_forall_not_mem.1 H x : _)

@[simp]
theorem sep_univ {α} {p : α → Prop} : { a∈(univ : Set α) | p a } = { a | p a } :=
  univ_inter _

@[simp]
theorem sep_true : { a∈s | True } = s :=
  by 
    ext 
    simp 

@[simp]
theorem sep_false : { a∈s | False } = ∅ :=
  by 
    ext 
    simp 

theorem sep_inter_sep {p q : α → Prop} : { x∈s | p x } ∩ { x∈s | q x } = { x∈s | p x ∧ q x } :=
  by 
    ext 
    simpRw [mem_inter_iff, mem_sep_iff]
    rw [and_and_and_comm, and_selfₓ]

@[simp]
theorem subset_singleton_iff {α : Type _} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y _ : y ∈ s, y = x :=
  Iff.rfl

theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} :=
  by 
    obtain rfl | hs := s.eq_empty_or_nonempty 
    use ⟨fun _ => Or.inl rfl, fun _ => empty_subset _⟩
    simp [eq_singleton_iff_nonempty_unique_mem, hs, ne_empty_iff_nonempty.2 hs]

theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ :=
  by 
    rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_distrib_right, and_not_selfₓ, or_falseₓ,
      and_iff_left_iff_imp]
    rintro rfl 
    refine' ne_comm.1 (ne_empty_iff_nonempty.2 (singleton_nonempty _))

theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/-! ### Lemmas about complement -/


theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ «expr ᶜ» s :=
  h

theorem compl_set_of {α} (p : α → Prop) : «expr ᶜ» { a | p a } = { a | ¬p a } :=
  rfl

theorem not_mem_of_mem_compl {s : Set α} {x : α} (h : x ∈ «expr ᶜ» s) : x ∉ s :=
  h

@[simp]
theorem mem_compl_eq (s : Set α) (x : α) : (x ∈ «expr ᶜ» s) = (x ∉ s) :=
  rfl

theorem mem_compl_iff (s : Set α) (x : α) : x ∈ «expr ᶜ» s ↔ x ∉ s :=
  Iff.rfl

@[simp]
theorem inter_compl_self (s : Set α) : s ∩ «expr ᶜ» s = ∅ :=
  inf_compl_eq_bot

@[simp]
theorem compl_inter_self (s : Set α) : «expr ᶜ» s ∩ s = ∅ :=
  compl_inf_eq_bot

@[simp]
theorem compl_empty : «expr ᶜ» (∅ : Set α) = univ :=
  compl_bot

@[simp]
theorem compl_union (s t : Set α) : «expr ᶜ» (s ∪ t) = «expr ᶜ» s ∩ «expr ᶜ» t :=
  compl_sup

theorem compl_inter (s t : Set α) : «expr ᶜ» (s ∩ t) = «expr ᶜ» s ∪ «expr ᶜ» t :=
  compl_inf

@[simp]
theorem compl_univ : «expr ᶜ» (univ : Set α) = ∅ :=
  compl_top

@[simp]
theorem compl_empty_iff {s : Set α} : «expr ᶜ» s = ∅ ↔ s = univ :=
  compl_eq_bot

@[simp]
theorem compl_univ_iff {s : Set α} : «expr ᶜ» s = univ ↔ s = ∅ :=
  compl_eq_top

theorem nonempty_compl {s : Set α} : («expr ᶜ» s).Nonempty ↔ s ≠ univ :=
  ne_empty_iff_nonempty.symm.trans$ not_congr$ compl_empty_iff

theorem mem_compl_singleton_iff {a x : α} : x ∈ «expr ᶜ» ({a} : Set α) ↔ x ≠ a :=
  not_congr mem_singleton_iff

theorem compl_singleton_eq (a : α) : «expr ᶜ» ({a} : Set α) = { x | x ≠ a } :=
  ext$ fun x => mem_compl_singleton_iff

@[simp]
theorem compl_ne_eq_singleton (a : α) : «expr ᶜ» ({ x | x ≠ a } : Set α) = {a} :=
  by 
    ext 
    simp 

theorem union_eq_compl_compl_inter_compl (s t : Set α) : s ∪ t = «expr ᶜ» («expr ᶜ» s ∩ «expr ᶜ» t) :=
  ext$ fun x => or_iff_not_and_not

theorem inter_eq_compl_compl_union_compl (s t : Set α) : s ∩ t = «expr ᶜ» («expr ᶜ» s ∪ «expr ᶜ» t) :=
  ext$ fun x => and_iff_not_or_not

@[simp]
theorem union_compl_self (s : Set α) : s ∪ «expr ᶜ» s = univ :=
  eq_univ_iff_forall.2$ fun x => em _

@[simp]
theorem compl_union_self (s : Set α) : «expr ᶜ» s ∪ s = univ :=
  by 
    rw [union_comm, union_compl_self]

theorem compl_comp_compl : compl ∘ compl = @id (Set α) :=
  funext compl_compl

theorem compl_subset_comm {s t : Set α} : «expr ᶜ» s ⊆ t ↔ «expr ᶜ» t ⊆ s :=
  @compl_le_iff_compl_le _ s t _

@[simp]
theorem compl_subset_compl {s t : Set α} : «expr ᶜ» s ⊆ «expr ᶜ» t ↔ t ⊆ s :=
  @compl_le_compl_iff_le _ t s _

theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ «expr ᶜ» u ↔ s ∩ u ⊆ t :=
  (@is_compl_compl _ u _).le_sup_right_iff_inf_left_le

theorem compl_subset_iff_union {s t : Set α} : «expr ᶜ» s ⊆ t ↔ s ∪ t = univ :=
  Iff.symm$ eq_univ_iff_forall.trans$ forall_congrₓ$ fun a => or_iff_not_imp_left

theorem subset_compl_comm {s t : Set α} : s ⊆ «expr ᶜ» t ↔ t ⊆ «expr ᶜ» s :=
  forall_congrₓ$ fun a => imp_not_comm

theorem subset_compl_iff_disjoint {s t : Set α} : s ⊆ «expr ᶜ» t ↔ s ∩ t = ∅ :=
  Iff.trans (forall_congrₓ$ fun a => and_imp.symm) subset_empty_iff

theorem subset_compl_singleton_iff {a : α} {s : Set α} : s ⊆ «expr ᶜ» {a} ↔ a ∉ s :=
  subset_compl_comm.trans singleton_subset_iff

theorem inter_subset (a b c : Set α) : a ∩ b ⊆ c ↔ a ⊆ «expr ᶜ» b ∪ c :=
  forall_congrₓ$ fun x => and_imp.trans$ imp_congr_right$ fun _ => imp_iff_not_or

theorem inter_compl_nonempty_iff {s t : Set α} : (s ∩ «expr ᶜ» t).Nonempty ↔ ¬s ⊆ t :=
  (not_subset.trans$
      exists_congr$
        by 
          exact
            fun x =>
              by 
                simp [mem_compl]).symm

/-! ### Lemmas about set difference -/


theorem diff_eq (s t : Set α) : s \ t = s ∩ «expr ᶜ» t :=
  rfl

@[simp]
theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl

theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
  ⟨h1, h2⟩

theorem mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left

theorem not_mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right

theorem diff_eq_compl_inter {s t : Set α} : s \ t = «expr ᶜ» t ∩ s :=
  by 
    rw [diff_eq, inter_comm]

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

theorem inter_diff_assoc (a b c : Set α) : a ∩ b \ c = a ∩ (b \ c) :=
  inf_sdiff_assoc

@[simp]
theorem inter_diff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right

@[simp]
theorem inter_union_diff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t

@[simp]
theorem diff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s :=
  by 
    rw [union_comm]
    exact sup_inf_sdiff _ _

@[simp]
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ «expr ᶜ» t = s :=
  inter_union_diff _ _

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂ from sdiff_le_sdiff

theorem diff_subset_diff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
  sdiff_le_sdiff_right ‹s₁ ≤ s₂›

theorem diff_subset_diff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
  sdiff_le_sdiff_left ‹t ≤ u›

theorem compl_eq_univ_diff (s : Set α) : «expr ᶜ» s = univ \ s :=
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

theorem diff_diff {u : Set α} : s \ t \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left

theorem diff_diff_comm {s t u : Set α} : s \ t \ u = s \ u \ t :=
  sdiff_sdiff_comm

theorem diff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  show s \ t ≤ u ↔ s ≤ t ∪ u from sdiff_le_iff

theorem subset_diff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  show s ≤ s \ t ∪ t from le_sdiff_sup

theorem diff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  subset.antisymm (union_subset (diff_subset _ _) h) (subset_diff_union _ _)

@[simp]
theorem diff_singleton_subset_iff {x : α} {s t : Set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t :=
  by 
    rw [←union_singleton, union_comm]
    apply diff_subset_iff

theorem subset_diff_singleton {x : α} {s t : Set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
  subset_inter h$ subset_compl_comm.1$ singleton_subset_iff.2 hx

theorem subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) :=
  by 
    rw [←diff_singleton_subset_iff]

theorem diff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  show s \ t ≤ u ↔ s \ u ≤ t from sdiff_le_comm

theorem diff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

theorem diff_inter_diff {s t u : Set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm

theorem diff_compl : s \ «expr ᶜ» t = s ∩ t :=
  sdiff_compl

theorem diff_diff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem insert_diff_of_mem (s) (h : «expr ∈ »(a, t)) : «expr = »(«expr \ »(insert a s, t), «expr \ »(s, t)) :=
by { ext [] [] [],
  split; simp [] [] [] ["[", expr or_imp_distrib, ",", expr h, "]"] [] [] { contextual := tt } }

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_diff_of_not_mem
(s)
(h : «expr ∉ »(a, t)) : «expr = »(«expr \ »(insert a s, t), insert a «expr \ »(s, t)) :=
begin
  classical,
  ext [] [ident x] [],
  by_cases [expr h', ":", expr «expr ∈ »(x, t)],
  { have [] [":", expr «expr ≠ »(x, a)] [],
    { assume [binders (H)],
      rw [expr H] ["at", ident h'],
      exact [expr h h'] },
    simp [] [] [] ["[", expr h, ",", expr h', ",", expr this, "]"] [] [] },
  { simp [] [] [] ["[", expr h, ",", expr h', "]"] [] [] }
end

theorem insert_diff_self_of_not_mem {a : α} {s : Set α} (h : a ∉ s) : insert a s \ {a} = s :=
  by 
    ext 
    simp [and_iff_left_of_imp fun hx : x ∈ s => show x ≠ a from fun hxa => h$ hxa ▸ hx]

theorem insert_inter_of_mem {s₁ s₂ : Set α} {a : α} (h : a ∈ s₂) : insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  by 
    simp [Set.insert_inter, h]

theorem insert_inter_of_not_mem {s₁ s₂ : Set α} {a : α} (h : a ∉ s₂) : insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  by 
    ext x 
    simp only [mem_inter_iff, mem_insert_iff, mem_inter_eq, And.congr_left_iff, or_iff_right_iff_imp]
    cc

@[simp]
theorem union_diff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right

@[simp]
theorem diff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left

@[simp]
theorem diff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left

@[simp]
theorem diff_inter_self_eq_diff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right

@[simp]
theorem diff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left

@[simp]
theorem diff_eq_self {s t : Set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
  show s \ t = s ↔ t⊓s ≤ ⊥ from sdiff_eq_self_iff_disjoint

@[simp]
theorem diff_singleton_eq_self {a : α} {s : Set α} (h : a ∉ s) : s \ {a} = s :=
  diff_eq_self.2$
    by 
      simp [singleton_inter_eq_empty.2 h]

@[simp]
theorem insert_diff_singleton {a : α} {s : Set α} : insert a (s \ {a}) = insert a s :=
  by 
    simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp]
theorem diff_self {s : Set α} : s \ s = ∅ :=
  sdiff_self

theorem diff_diff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h

theorem mem_diff_singleton {x y : α} {s : Set α} : x ∈ s \ {y} ↔ x ∈ s ∧ x ≠ y :=
  Iff.rfl

theorem mem_diff_singleton_empty {s : Set α} {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.nonempty :=
  mem_diff_singleton.trans$ and_congr Iff.rfl ne_empty_iff_nonempty

theorem union_eq_diff_union_diff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

/-! ### Powerset -/


theorem mem_powerset {x s : Set α} (h : x ⊆ s) : x ∈ powerset s :=
  h

theorem subset_of_mem_powerset {x s : Set α} (h : x ∈ powerset s) : x ⊆ s :=
  h

@[simp]
theorem mem_powerset_iff (x s : Set α) : x ∈ powerset s ↔ x ⊆ s :=
  Iff.rfl

theorem powerset_inter (s t : Set α) : 𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext$ fun u => subset_inter_iff

@[simp]
theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  ⟨fun h => h (subset.refl s), fun h u hu => subset.trans hu h⟩

theorem monotone_powerset : Monotone (powerset : Set α → Set (Set α)) :=
  fun s t => powerset_mono.2

@[simp]
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, empty_subset s⟩

@[simp]
theorem powerset_empty : 𝒫(∅ : Set α) = {∅} :=
  ext$ fun s => subset_empty_iff

@[simp]
theorem powerset_univ : 𝒫(univ : Set α) = univ :=
  eq_univ_of_forall subset_univ

/-! ### If-then-else for sets -/


/-- `ite` for sets: `set.ite t s s' ∩ t = s ∩ t`, `set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t

@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t :=
  by 
    rw [Set.Ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]

@[simp]
theorem ite_compl (t s s' : Set α) : («expr ᶜ» t).ite s s' = t.ite s' s :=
  by 
    rw [Set.Ite, Set.Ite, diff_compl, union_comm, diff_eq]

@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ «expr ᶜ» t = s' ∩ «expr ᶜ» t :=
  by 
    rw [←ite_compl, ite_inter_self]

@[simp]
theorem ite_diff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'

@[simp]
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_diff _ _

@[simp]
theorem ite_left (s t : Set α) : s.ite s t = s ∪ t :=
  by 
    simp [Set.Ite]

@[simp]
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s :=
  by 
    simp [Set.Ite]

@[simp]
theorem ite_empty (s s' : Set α) : Set.Ite ∅ s s' = s' :=
  by 
    simp [Set.Ite]

@[simp]
theorem ite_univ (s s' : Set α) : Set.Ite univ s s' = s :=
  by 
    simp [Set.Ite]

@[simp]
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t :=
  by 
    simp [Set.Ite]

@[simp]
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t :=
  by 
    simp [Set.Ite]

theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') : t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (inter_subset_inter_left _ h')

theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union (inter_subset_left _ _) (diff_subset _ _)

theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ (inter_subset_left _ _) (inter_subset_right _ _)

theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) : t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' :=
  by 
    ext x 
    finish [Set.Ite, iff_def]

theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s :=
  by 
    rw [ite_inter_inter, ite_same]

theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) : t.ite s₁ s₂ ∩ s = s₁ ∩ s :=
  by 
    rw [←ite_inter, ←h, ite_same]

theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' :=
  by 
    simp only [subset_def, ←forall_and_distrib]
    refine' forall_congrₓ fun x => _ 
    byCases' hx : x ∈ t <;> simp [Set.Ite]

/-! ### Inverse image -/


/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : Set β) : Set α :=
  { x | f x ∈ s }

infixl:80 " ⁻¹' " => preimage

section Preimage

variable {f : α → β} {g : β → γ}

@[simp]
theorem preimage_empty : f ⁻¹' ∅ = ∅ :=
  rfl

@[simp]
theorem mem_preimage {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s :=
  Iff.rfl

theorem preimage_congr {f g : α → β} {s : Set β} (h : ∀ x : α, f x = g x) : f ⁻¹' s = g ⁻¹' s :=
  by 
    congr with x 
    applyAssumption

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t :=
  fun x hx => h hx

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
theorem preimage_compl {s : Set β} : f ⁻¹' «expr ᶜ» s = «expr ᶜ» (f ⁻¹' s) :=
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
theorem preimage_id {s : Set α} : id ⁻¹' s = s :=
  rfl

@[simp]
theorem preimage_id' {s : Set α} : (fun x => x) ⁻¹' s = s :=
  rfl

@[simp]
theorem preimage_const_of_mem {b : β} {s : Set β} (h : b ∈ s) : (fun x : α => b) ⁻¹' s = univ :=
  eq_univ_of_forall$ fun x => h

@[simp]
theorem preimage_const_of_not_mem {b : β} {s : Set β} (h : b ∉ s) : (fun x : α => b) ⁻¹' s = ∅ :=
  eq_empty_of_subset_empty$ fun x hx => h hx

theorem preimage_const (b : β) (s : Set β) [Decidable (b ∈ s)] : (fun x : α => b) ⁻¹' s = if b ∈ s then univ else ∅ :=
  by 
    splitIfs with hb hb 
    exacts[preimage_const_of_mem hb, preimage_const_of_not_mem hb]

theorem preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s) :=
  rfl

theorem preimage_preimage {g : β → γ} {f : α → β} {s : Set γ} : f ⁻¹' (g ⁻¹' s) = (fun x => g (f x)) ⁻¹' s :=
  preimage_comp.symm

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : Set (Subtype p)} {t : Set α} :
  s = Subtype.val ⁻¹' t ↔ ∀ x h : p x, (⟨x, h⟩ : Subtype p) ∈ s ↔ x ∈ t :=
  ⟨fun s_eq x h =>
      by 
        rw [s_eq]
        simp ,
    fun h =>
      ext$
        fun ⟨x, hx⟩ =>
          by 
            simp [h]⟩

theorem preimage_coe_coe_diagonal {α : Type _} (s : Set α) : Prod.map coeₓ coeₓ ⁻¹' diagonal α = diagonal s :=
  by 
    ext ⟨⟨x, x_in⟩, ⟨y, y_in⟩⟩
    simp [Set.Diagonal]

end Preimage

/-! ### Image of a set under a function -/


section Image

infixl:80 " '' " => image

theorem mem_image_iff_bex {f : α → β} {s : Set α} {y : β} : y ∈ f '' s ↔ ∃ (x : _)(_ : x ∈ s), f x = y :=
  bex_def.symm

theorem mem_image_eq (f : α → β) (s : Set α) (y : β) : (y ∈ f '' s) = ∃ x, x ∈ s ∧ f x = y :=
  rfl

@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y :=
  Iff.rfl

theorem image_eta (f : α → β) : f '' s = (fun x => f x) '' s :=
  rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩

theorem _root_.function.injective.mem_set_image {f : α → β} (hf : injective f) {s : Set α} {a : α} :
  f a ∈ f '' s ↔ a ∈ s :=
  ⟨fun ⟨b, hb, Eq⟩ => hf Eq ▸ hb, mem_image_of_mem f⟩

theorem ball_image_iff {f : α → β} {s : Set α} {p : β → Prop} : (∀ y _ : y ∈ f '' s, p y) ↔ ∀ x _ : x ∈ s, p (f x) :=
  by 
    simp 

theorem ball_image_of_ball {f : α → β} {s : Set α} {p : β → Prop} (h : ∀ x _ : x ∈ s, p (f x)) :
  ∀ y _ : y ∈ f '' s, p y :=
  ball_image_iff.2 h

theorem bex_image_iff {f : α → β} {s : Set α} {p : β → Prop} :
  (∃ (y : _)(_ : y ∈ f '' s), p y) ↔ ∃ (x : _)(_ : x ∈ s), p (f x) :=
  by 
    simp 

theorem mem_image_elim {f : α → β} {s : Set α} {C : β → Prop} (h : ∀ x : α, x ∈ s → C (f x)) :
  ∀ {y : β}, y ∈ f '' s → C y
| _, ⟨a, a_in, rfl⟩ => h a a_in

theorem mem_image_elim_on {f : α → β} {s : Set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
  (h : ∀ x : α, x ∈ s → C (f x)) : C y :=
  mem_image_elim h h_y

@[congr]
theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a _ : a ∈ s, f a = g a) : f '' s = g '' s :=
  by 
    safe [ext_iff, iff_def]

/-- A common special case of `image_congr` -/
theorem image_congr' {f g : α → β} {s : Set α} (h : ∀ x : α, f x = g x) : f '' s = g '' s :=
  image_congr fun x _ => h x

theorem image_comp (f : β → γ) (g : α → β) (a : Set α) : f ∘ g '' a = f '' (g '' a) :=
  subset.antisymm (ball_image_of_ball$ fun a ha => mem_image_of_mem _$ mem_image_of_mem _ ha)
    (ball_image_of_ball$ ball_image_of_ball$ fun a ha => mem_image_of_mem _ ha)

/-- A variant of `image_comp`, useful for rewriting -/
theorem image_image (g : β → γ) (f : α → β) (s : Set α) : g '' (f '' s) = (fun x => g (f x)) '' s :=
  (image_comp g f s).symm

/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : Set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
  by 
    finish [subset_def, mem_image_eq]

theorem image_union (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t :=
  ext$
    fun x =>
      ⟨by 
          rintro ⟨a, h | h, rfl⟩ <;> [left, right] <;> exact ⟨_, h, rfl⟩,
        by 
          rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩) <;> refine' ⟨_, _, rfl⟩ <;> [left, right] <;> exact h⟩

@[simp]
theorem image_empty (f : α → β) : f '' ∅ = ∅ :=
  by 
    ext 
    simp 

theorem image_inter_subset (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  subset_inter (image_subset _$ inter_subset_left _ _) (image_subset _$ inter_subset_right _ _)

theorem image_inter_on {f : α → β} {s t : Set α} (h : ∀ x _ : x ∈ t, ∀ y _ : y ∈ s, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
  subset.antisymm
    (fun b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩ =>
      have  : a₂ = a₁ :=
        h _ ha₂ _ ha₁
          (by 
            simp )
      ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
    (image_inter_subset _ _ _)

theorem image_inter {f : α → β} {s t : Set α} (H : injective f) : f '' s ∩ f '' t = f '' (s ∩ t) :=
  image_inter_on fun x _ y _ h => H h

theorem image_univ_of_surjective {ι : Type _} {f : ι → β} (H : surjective f) : f '' univ = univ :=
  eq_univ_of_forall$
    by 
      simpa [image]

@[simp]
theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
  by 
    ext 
    simp [image, eq_comm]

@[simp]
theorem nonempty.image_const {s : Set α} (hs : s.nonempty) (a : β) : (fun _ => a) '' s = {a} :=
  ext$
    fun x =>
      ⟨fun ⟨y, _, h⟩ => h ▸ mem_singleton _, fun h => (eq_of_mem_singleton h).symm ▸ hs.imp fun y hy => ⟨hy, rfl⟩⟩

@[simp]
theorem image_eq_empty {α β} {f : α → β} {s : Set α} : f '' s = ∅ ↔ s = ∅ :=
  by 
    simp only [eq_empty_iff_forall_not_mem]
    exact ⟨fun H a ha => H _ ⟨_, ha, rfl⟩, fun H b ⟨_, ha, _⟩ => H _ ha⟩

theorem mem_compl_image (t : Set α) (S : Set (Set α)) : t ∈ compl '' S ↔ «expr ᶜ» t ∈ S :=
  by 
    suffices  : ∀ x, «expr ᶜ» x = t ↔ «expr ᶜ» t = x
    ·
      simp [this]
    intro x 
    split  <;>
      ·
        intro e 
        subst e 
        simp 

/-- A variant of `image_id` -/
@[simp]
theorem image_id' (s : Set α) : (fun x => x) '' s = s :=
  by 
    ext 
    simp 

theorem image_id (s : Set α) : id '' s = s :=
  by 
    simp 

theorem compl_compl_image (S : Set (Set α)) : compl '' (compl '' S) = S :=
  by 
    rw [←image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : Set α} : f '' insert a s = insert (f a) (f '' s) :=
  by 
    ext 
    simp [and_or_distrib_left, exists_or_distrib, eq_comm, or_comm, and_comm]

theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} :=
  by 
    simp only [image_insert_eq, image_singleton]

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α} (I : left_inverse g f) (s : Set α) :
  f '' s ⊆ g ⁻¹' s :=
  fun b ⟨a, h, e⟩ => e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α} (I : left_inverse g f) (s : Set β) :
  f ⁻¹' s ⊆ g '' s :=
  fun b h => ⟨f b, h, I b⟩

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α} (h₁ : left_inverse g f) (h₂ : RightInverse g f) :
  image f = preimage g :=
  funext$ fun s => subset.antisymm (image_subset_preimage_of_inverse h₁ s) (preimage_subset_image_of_inverse h₂ s)

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : Set α} (h₁ : left_inverse g f)
  (h₂ : RightInverse g f) : b ∈ f '' s ↔ g b ∈ s :=
  by 
    rw [image_eq_preimage_of_inverse h₁ h₂] <;> rfl

theorem image_compl_subset {f : α → β} {s : Set α} (H : injective f) : f '' «expr ᶜ» s ⊆ «expr ᶜ» (f '' s) :=
  subset_compl_iff_disjoint.2$
    by 
      simp [image_inter H]

theorem subset_image_compl {f : α → β} {s : Set α} (H : surjective f) : «expr ᶜ» (f '' s) ⊆ f '' «expr ᶜ» s :=
  compl_subset_iff_union.2$
    by 
      rw [←image_union]
      simp [image_univ_of_surjective H]

theorem image_compl_eq {f : α → β} {s : Set α} (H : bijective f) : f '' «expr ᶜ» s = «expr ᶜ» (f '' s) :=
  subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

theorem subset_image_diff (f : α → β) (s t : Set α) : f '' s \ f '' t ⊆ f '' (s \ t) :=
  by 
    rw [diff_subset_iff, ←image_union, union_diff_self]
    exact image_subset f (subset_union_right t s)

theorem image_diff {f : α → β} (hf : injective f) (s t : Set α) : f '' (s \ t) = f '' s \ f '' t :=
  subset.antisymm (subset.trans (image_inter_subset _ _ _)$ inter_subset_inter_right _$ image_compl_subset hf)
    (subset_image_diff f s t)

theorem nonempty.image (f : α → β) {s : Set α} : s.nonempty → (f '' s).Nonempty
| ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩

theorem nonempty.of_image {f : α → β} {s : Set α} : (f '' s).Nonempty → s.nonempty
| ⟨y, x, hx, _⟩ => ⟨x, hx⟩

@[simp]
theorem nonempty_image_iff {f : α → β} {s : Set α} : (f '' s).Nonempty ↔ s.nonempty :=
  ⟨nonempty.of_image, fun h => h.image f⟩

theorem nonempty.preimage {s : Set β} (hs : s.nonempty) {f : α → β} (hf : surjective f) : (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs 
  let ⟨x, hx⟩ := hf y
  ⟨x, mem_preimage.2$ hx.symm ▸ hy⟩

instance (f : α → β) (s : Set α) [Nonempty s] : Nonempty (f '' s) :=
  (Set.Nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp]
theorem image_subset_iff {s : Set α} {t : Set β} {f : α → β} : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  ball_image_iff

theorem image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s :=
  image_subset_iff.2 (subset.refl _)

theorem subset_preimage_image (f : α → β) (s : Set α) : s ⊆ f ⁻¹' (f '' s) :=
  fun x => mem_image_of_mem f

theorem preimage_image_eq {f : α → β} (s : Set α) (h : injective f) : f ⁻¹' (f '' s) = s :=
  subset.antisymm (fun x ⟨y, hy, e⟩ => h e ▸ hy) (subset_preimage_image f s)

theorem image_preimage_eq {f : α → β} (s : Set β) (h : surjective f) : f '' (f ⁻¹' s) = s :=
  subset.antisymm (image_preimage_subset f s)
    fun x hx =>
      let ⟨y, e⟩ := h x
      ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩

theorem preimage_eq_preimage {f : β → α} (hf : surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  Iff.intro
    (fun eq =>
      by 
        rw [←image_preimage_eq s hf, ←image_preimage_eq t hf, Eq])
    fun eq => Eq ▸ rfl

theorem image_inter_preimage (f : α → β) (s : Set α) (t : Set β) : f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
  by 
    apply subset.antisymm
    ·
      calc f '' (s ∩ f ⁻¹' t) ⊆ f '' s ∩ f '' (f ⁻¹' t) := image_inter_subset _ _ _ _ ⊆ f '' s ∩ t :=
        inter_subset_inter_right _ (image_preimage_subset f t)
    ·
      rintro _ ⟨⟨x, h', rfl⟩, h⟩
      exact ⟨x, ⟨h', h⟩, rfl⟩

theorem image_preimage_inter (f : α → β) (s : Set α) (t : Set β) : f '' (f ⁻¹' t ∩ s) = t ∩ f '' s :=
  by 
    simp only [inter_comm, image_inter_preimage]

@[simp]
theorem image_inter_nonempty_iff {f : α → β} {s : Set α} {t : Set β} : (f '' s ∩ t).Nonempty ↔ (s ∩ f ⁻¹' t).Nonempty :=
  by 
    rw [←image_inter_preimage, nonempty_image_iff]

theorem image_diff_preimage {f : α → β} {s : Set α} {t : Set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
  by 
    simpRw [diff_eq, ←preimage_compl, image_inter_preimage]

theorem compl_image : image (compl : Set α → Set α) = preimage compl :=
  image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : Set α → Prop} : compl '' { s | p s } = { s | p («expr ᶜ» s) } :=
  congr_funₓ compl_image p

theorem inter_preimage_subset (s : Set α) (t : Set β) (f : α → β) : s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) :=
  fun x h => ⟨mem_image_of_mem _ h.left, h.right⟩

theorem union_preimage_subset (s : Set α) (t : Set β) (f : α → β) : s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) :=
  fun x h => Or.elim h (fun l => Or.inl$ mem_image_of_mem _ l) fun r => Or.inr r

theorem subset_image_union (f : α → β) (s : Set α) (t : Set β) : f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
  image_subset_iff.2 (union_preimage_subset _ _ _)

theorem preimage_subset_iff {A : Set α} {B : Set β} {f : α → β} : f ⁻¹' B ⊆ A ↔ ∀ a : α, f a ∈ B → a ∈ A :=
  Iff.rfl

theorem image_eq_image {f : α → β} (hf : injective f) : f '' s = f '' t ↔ s = t :=
  Iff.symm$
    (Iff.intro fun eq => Eq ▸ rfl)$
      fun eq =>
        by 
          rw [←preimage_image_eq s hf, ←preimage_image_eq t hf, Eq]

theorem image_subset_image_iff {f : α → β} (hf : injective f) : f '' s ⊆ f '' t ↔ s ⊆ t :=
  by 
    refine' Iff.symm$ Iff.intro (image_subset f)$ fun h => _ 
    rw [←preimage_image_eq s hf, ←preimage_image_eq t hf]
    exact preimage_mono h

theorem prod_quotient_preimage_eq_image [s : Setoidₓ α] (g : Quotientₓ s → β) {h : α → β} (Hh : h = g ∘ Quotientₓ.mk)
  (r : Set (β × β)) :
  { x:Quotientₓ s × Quotientₓ s | (g x.1, g x.2) ∈ r } =
    (fun a : α × α => («expr⟦ ⟧» a.1, «expr⟦ ⟧» a.2)) '' ((fun a : α × α => (h a.1, h a.2)) ⁻¹' r) :=
  Hh.symm ▸
    Set.ext
      fun ⟨a₁, a₂⟩ =>
        ⟨Quotientₓ.induction_on₂ a₁ a₂ fun a₁ a₂ h => ⟨(a₁, a₂), h, rfl⟩,
          fun ⟨⟨b₁, b₂⟩, h₁, h₂⟩ =>
            show (g a₁, g a₂) ∈ r from
              have h₃ : «expr⟦ ⟧» b₁ = a₁ ∧ «expr⟦ ⟧» b₂ = a₂ := Prod.ext_iff.1 h₂ 
              h₃.1 ▸ h₃.2 ▸ h₁⟩

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def image_factorization (f : α → β) (s : Set α) : s → f '' s :=
  fun p => ⟨f p.1, mem_image_of_mem f p.2⟩

theorem image_factorization_eq {f : α → β} {s : Set α} : Subtype.val ∘ image_factorization f s = f ∘ Subtype.val :=
  funext$ fun p => rfl

theorem surjective_onto_image {f : α → β} {s : Set α} : surjective (image_factorization f s) :=
  fun ⟨_, ⟨a, ha, rfl⟩⟩ => ⟨⟨a, ha⟩, rfl⟩

end Image

/-! ### Subsingleton -/


/-- A set `s` is a `subsingleton`, if it has at most one element. -/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ hx : x ∈ s ⦃y⦄ hy : y ∈ s, x = y

theorem subsingleton.mono (ht : t.subsingleton) (hst : s ⊆ t) : s.subsingleton :=
  fun x hx y hy => ht (hst hx) (hst hy)

theorem subsingleton.image (hs : s.subsingleton) (f : α → β) : (f '' s).Subsingleton :=
  fun _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩ => Hx ▸ Hy ▸ congr_argₓ f (hs hx hy)

theorem subsingleton.eq_singleton_of_mem (hs : s.subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext$ fun y => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp]
theorem subsingleton_empty : (∅ : Set α).Subsingleton :=
  fun x => False.elim

@[simp]
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton :=
  fun x hx y hy => (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl

theorem subsingleton_iff_singleton {x} (hx : x ∈ s) : s.subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩

theorem subsingleton.eq_empty_or_singleton (hs : s.subsingleton) : s = ∅ ∨ ∃ x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩

theorem subsingleton.induction_on {p : Set α → Prop} (hs : s.subsingleton) (he : p ∅) (h₁ : ∀ x, p {x}) : p s :=
  by 
    rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
    exacts[he, h₁ _]

theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton :=
  fun x hx y hy => Subsingleton.elimₓ x y

theorem subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩

@[simp]
theorem subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩

theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : Set.Subsingleton s :=
  subsingleton.mono subsingleton_univ (subset_univ s)

theorem subsingleton_is_top (α : Type _) [PartialOrderₓ α] : Set.Subsingleton { x:α | IsTop x } :=
  fun x hx y hy => hx.unique (hy x)

theorem subsingleton_is_bot (α : Type _) [PartialOrderₓ α] : Set.Subsingleton { x:α | IsBot x } :=
  fun x hx y hy => hx.unique (hy x)

/-- `s`, coerced to a type, is a subsingleton type if and only if `s`
is a subsingleton set. -/
@[simp, normCast]
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.subsingleton :=
  by 
    split 
    ·
      refine' fun h => fun a ha b hb => _ 
      exact SetCoe.ext_iff.2 (@Subsingleton.elimₓ s h ⟨a, ha⟩ ⟨b, hb⟩)
    ·
      exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem subsingleton.preimage {s : Set β} (hs : s.subsingleton) {f : α → β} (hf : Function.Injective f) :
  (f ⁻¹' s).Subsingleton :=
  fun a ha b hb => hf$ hs ha hb

/-- `s` is a subsingleton, if its image of an injective function is. -/
theorem subsingleton_of_image {α β : Type _} {f : α → β} (hf : Function.Injective f) (s : Set α)
  (hs : (f '' s).Subsingleton) : s.subsingleton :=
  (hs.preimage hf).mono$ subset_preimage_image _ _

theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm$
    eq_univ_of_forall$
      Classical.cases
        (by 
          simp )
        (by 
          simp )

/-! ### Lemmas about range of a function. -/


section Range

variable {f : ι → α}

open Function

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : Set α :=
  { x | ∃ y, f y = x }

@[simp]
theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x :=
  Iff.rfl

@[simp]
theorem mem_range_self (i : ι) : f i ∈ range f :=
  ⟨i, rfl⟩

theorem forall_range_iff {p : α → Prop} : (∀ a _ : a ∈ range f, p a) ↔ ∀ i, p (f i) :=
  by 
    simp 

theorem forall_subtype_range_iff {p : range f → Prop} : (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun H i => H _,
    fun H ⟨y, i, hi⟩ =>
      by 
        subst hi 
        apply H⟩

theorem exists_range_iff {p : α → Prop} : (∃ (a : _)(_ : a ∈ range f), p a) ↔ ∃ i, p (f i) :=
  by 
    simp 

theorem exists_range_iff' {p : α → Prop} : (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) :=
  by 
    simpa only [exists_prop] using exists_range_iff

theorem exists_subtype_range_iff {p : range f → Prop} : (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ :=
  ⟨fun ⟨⟨a, i, hi⟩, ha⟩ =>
      by 
        subst a 
        exact ⟨i, ha⟩,
    fun ⟨i, hi⟩ => ⟨_, hi⟩⟩

theorem range_iff_surjective : range f = univ ↔ surjective f :=
  eq_univ_iff_forall

alias range_iff_surjective ↔ _ Function.Surjective.range_eq

@[simp]
theorem range_id : range (@id α) = univ :=
  range_iff_surjective.2 surjective_id

@[simp]
theorem _root_.prod.range_fst [Nonempty β] : range (Prod.fst : α × β → α) = univ :=
  Prod.fst_surjectiveₓ.range_eq

@[simp]
theorem _root_.prod.range_snd [Nonempty α] : range (Prod.snd : α × β → β) = univ :=
  Prod.snd_surjective.range_eq

@[simp]
theorem range_eval {ι : Type _} {α : ι → Sort _} [∀ i, Nonempty (α i)] (i : ι) :
  range (eval i : (∀ i, α i) → α i) = univ :=
  (surjective_eval i).range_eq

theorem is_compl_range_inl_range_inr : IsCompl (range$ @Sum.inl α β) (range Sum.inr) :=
  ⟨by 
      rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩
      cc,
    by 
      rintro (x | y) - <;> [left, right] <;> exact mem_range_self _⟩

@[simp]
theorem range_inl_union_range_inr : range (Sum.inl : α → Sum α β) ∪ range Sum.inr = univ :=
  is_compl_range_inl_range_inr.sup_eq_top

@[simp]
theorem range_inl_inter_range_inr : range (Sum.inl : α → Sum α β) ∩ range Sum.inr = ∅ :=
  is_compl_range_inl_range_inr.inf_eq_bot

@[simp]
theorem range_inr_union_range_inl : range (Sum.inr : β → Sum α β) ∪ range Sum.inl = univ :=
  is_compl_range_inl_range_inr.symm.sup_eq_top

@[simp]
theorem range_inr_inter_range_inl : range (Sum.inr : β → Sum α β) ∩ range Sum.inl = ∅ :=
  is_compl_range_inl_range_inr.symm.inf_eq_bot

@[simp]
theorem preimage_inl_range_inr : Sum.inl ⁻¹' range (Sum.inr : β → Sum α β) = ∅ :=
  by 
    ext 
    simp 

@[simp]
theorem preimage_inr_range_inl : Sum.inr ⁻¹' range (Sum.inl : α → Sum α β) = ∅ :=
  by 
    ext 
    simp 

@[simp]
theorem range_quot_mk (r : α → α → Prop) : range (Quot.mk r) = univ :=
  (surjective_quot_mk r).range_eq

@[simp]
theorem image_univ {f : α → β} : f '' univ = range f :=
  by 
    ext 
    simp [image, range]

theorem image_subset_range (f : α → β) s : f '' s ⊆ range f :=
  by 
    rw [←image_univ] <;> exact image_subset _ (subset_univ _)

theorem mem_range_of_mem_image (f : α → β) s {x : β} (h : x ∈ f '' s) : x ∈ range f :=
  image_subset_range f s h

theorem nonempty.preimage' {s : Set β} (hs : s.nonempty) {f : α → β} (hf : s ⊆ Set.Range f) : (f ⁻¹' s).Nonempty :=
  let ⟨y, hy⟩ := hs 
  let ⟨x, hx⟩ := hf hy
  ⟨x, Set.mem_preimage.2$ hx.symm ▸ hy⟩

theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g '' range f :=
  subset.antisymm (forall_range_iff.mpr$ fun i => mem_image_of_mem g (mem_range_self _))
    (ball_image_iff.mpr$ forall_range_iff.mpr mem_range_self)

theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
  forall_range_iff

theorem range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g :=
  by 
    rw [range_comp] <;> apply image_subset_range

theorem range_nonempty_iff_nonempty : (range f).Nonempty ↔ Nonempty ι :=
  ⟨fun ⟨y, x, hxy⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨f x, mem_range_self x⟩⟩

theorem range_nonempty [h : Nonempty ι] (f : ι → α) : (range f).Nonempty :=
  range_nonempty_iff_nonempty.2 h

@[simp]
theorem range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ IsEmpty ι :=
  by 
    rw [←not_nonempty_iff, ←range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]

theorem range_eq_empty [IsEmpty ι] (f : ι → α) : range f = ∅ :=
  range_eq_empty_iff.2 ‹_›

instance [Nonempty ι] (f : ι → α) : Nonempty (range f) :=
  (range_nonempty f).to_subtype

@[simp]
theorem image_union_image_compl_eq_range (f : α → β) : f '' s ∪ f '' «expr ᶜ» s = range f :=
  by 
    rw [←image_union, ←image_univ, ←union_compl_self]

theorem image_preimage_eq_inter_range {f : α → β} {t : Set β} : f '' (f ⁻¹' t) = t ∩ range f :=
  ext$
    fun x =>
      ⟨fun ⟨x, hx, HEq⟩ => HEq ▸ ⟨hx, mem_range_self _⟩,
        fun ⟨hx, ⟨y, h_eq⟩⟩ =>
          h_eq ▸ mem_image_of_mem f$
            show y ∈ f ⁻¹' t by 
              simp [preimage, h_eq, hx]⟩

theorem image_preimage_eq_of_subset {f : α → β} {s : Set β} (hs : s ⊆ range f) : f '' (f ⁻¹' s) = s :=
  by 
    rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

instance set.can_lift [CanLift α β] : CanLift (Set α) (Set β) :=
  { coe := fun s => CanLift.coe '' s, cond := fun s => ∀ x _ : x ∈ s, CanLift.Cond β x,
    prf := fun s hs => ⟨CanLift.coe ⁻¹' s, image_preimage_eq_of_subset$ fun x hx => CanLift.prf _ (hs x hx)⟩ }

theorem image_preimage_eq_iff {f : α → β} {s : Set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ range f :=
  ⟨by 
      intro h 
      rw [←h]
      apply image_subset_range,
    image_preimage_eq_of_subset⟩

theorem preimage_subset_preimage_iff {s t : Set α} {f : β → α} (hs : s ⊆ range f) : f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
  by 
    split 
    ·
      intro h x hx 
      rcases hs hx with ⟨y, rfl⟩
      exact h hx 
    intro h x 
    apply h

theorem preimage_eq_preimage' {s t : Set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
  f ⁻¹' s = f ⁻¹' t ↔ s = t :=
  by 
    split 
    ·
      intro h 
      apply subset.antisymm 
      rw [←preimage_subset_preimage_iff hs, h]
      rw [←preimage_subset_preimage_iff ht, h]
    rintro rfl 
    rfl

@[simp]
theorem preimage_inter_range {f : α → β} {s : Set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
  Set.ext$ fun x => and_iff_left ⟨x, rfl⟩

@[simp]
theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s :=
  by 
    rw [inter_comm, preimage_inter_range]

theorem preimage_image_preimage {f : α → β} {s : Set β} : f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s :=
  by 
    rw [image_preimage_eq_inter_range, preimage_inter_range]

@[simp]
theorem quot_mk_range_eq [Setoidₓ α] : (range fun x : α => «expr⟦ ⟧» x) = univ :=
  range_iff_surjective.2 Quot.exists_rep

theorem range_const_subset {c : α} : (range fun x : ι => c) ⊆ {c} :=
  range_subset_iff.2$ fun x => rfl

@[simp]
theorem range_const : ∀ [Nonempty ι] {c : α}, (range fun x : ι => c) = {c}
| ⟨x⟩, c => subset.antisymm range_const_subset$ fun y hy => (mem_singleton_iff.1 hy).symm ▸ mem_range_self x

theorem diagonal_eq_range {α : Type _} : diagonal α = range fun x => (x, x) :=
  by 
    ext ⟨x, y⟩
    simp [diagonal, eq_comm]

theorem preimage_singleton_nonempty {f : α → β} {y : β} : (f ⁻¹' {y}).Nonempty ↔ y ∈ range f :=
  Iff.rfl

theorem preimage_singleton_eq_empty {f : α → β} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
  not_nonempty_iff_eq_empty.symm.trans$ not_congr preimage_singleton_nonempty

theorem range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x :=
  by 
    simp [range_subset_iff, funext_iff, mem_singleton]

theorem image_compl_preimage {f : α → β} {s : Set β} : f '' «expr ᶜ» (f ⁻¹' s) = range f \ s :=
  by 
    rw [compl_eq_univ_diff, image_diff_preimage, image_univ]

@[simp]
theorem range_sigma_mk {β : α → Type _} (a : α) : range (Sigma.mk a : β a → Σa, β a) = Sigma.fst ⁻¹' {a} :=
  by 
    apply subset.antisymm
    ·
      rintro _ ⟨b, rfl⟩
      simp 
    ·
      rintro ⟨x, y⟩ (rfl | _)
      exact mem_range_self y

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def range_factorization (f : ι → β) : ι → range f :=
  fun i => ⟨f i, mem_range_self i⟩

theorem range_factorization_eq {f : ι → β} : Subtype.val ∘ range_factorization f = f :=
  funext$ fun i => rfl

@[simp]
theorem range_factorization_coe (f : ι → β) (a : ι) : (range_factorization f a : β) = f a :=
  rfl

@[simp]
theorem coe_comp_range_factorization (f : ι → β) : coeₓ ∘ range_factorization f = f :=
  rfl

theorem surjective_onto_range : surjective (range_factorization f) :=
  fun ⟨_, ⟨i, rfl⟩⟩ => ⟨i, rfl⟩

theorem image_eq_range (f : α → β) (s : Set α) : f '' s = range fun x : s => f x :=
  by 
    ext 
    split 
    rintro ⟨x, h1, h2⟩
    exact ⟨⟨x, h1⟩, h2⟩
    rintro ⟨⟨x, h1⟩, h2⟩
    exact ⟨x, h1, h2⟩

@[simp]
theorem sum.elim_range {α β γ : Type _} (f : α → γ) (g : β → γ) : range (Sum.elim f g) = range f ∪ range g :=
  by 
    simp [Set.ext_iff, mem_range]

theorem range_ite_subset' {p : Prop} [Decidable p] {f g : α → β} : range (if p then f else g) ⊆ range f ∪ range g :=
  by 
    byCases' h : p
    ·
      rw [if_pos h]
      exact subset_union_left _ _
    ·
      rw [if_neg h]
      exact subset_union_right _ _

theorem range_ite_subset {p : α → Prop} [DecidablePred p] {f g : α → β} :
  (range fun x => if p x then f x else g x) ⊆ range f ∪ range g :=
  by 
    rw [range_subset_iff]
    intro x 
    byCases' h : p x 
    simp [if_pos h, mem_union, mem_range_self]
    simp [if_neg h, mem_union, mem_range_self]

@[simp]
theorem preimage_range (f : α → β) : f ⁻¹' range f = univ :=
  eq_univ_of_forall mem_range_self

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
theorem range_unique [h : Unique ι] : range f = {f$ default ι} :=
  by 
    ext x 
    rw [mem_range]
    split 
    ·
      rintro ⟨i, hi⟩
      rw [h.uniq i] at hi 
      exact hi ▸ mem_singleton _
    ·
      exact fun h => ⟨default ι, h.symm⟩

theorem range_diff_image_subset (f : α → β) (s : Set α) : range f \ f '' s ⊆ f '' «expr ᶜ» s :=
  fun y ⟨⟨x, h₁⟩, h₂⟩ => ⟨x, fun h => h₂ ⟨x, h, h₁⟩, h₁⟩

theorem range_diff_image {f : α → β} (H : injective f) (s : Set α) : range f \ f '' s = f '' «expr ᶜ» s :=
  subset.antisymm (range_diff_image_subset f s)$
    fun y ⟨x, hx, hy⟩ => hy ▸ ⟨mem_range_self _, fun ⟨x', hx', Eq⟩ => hx$ H Eq ▸ hx'⟩

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def range_splitting (f : α → β) : range f → α :=
  fun x => x.2.some

theorem apply_range_splitting (f : α → β) (x : range f) : f (range_splitting f x) = x :=
  x.2.some_spec

attribute [irreducible] range_splitting

@[simp]
theorem comp_range_splitting (f : α → β) : f ∘ range_splitting f = coeₓ :=
  by 
    ext 
    simp only [Function.comp_app]
    apply apply_range_splitting

theorem left_inverse_range_splitting (f : α → β) : left_inverse (range_factorization f) (range_splitting f) :=
  fun x =>
    by 
      ext 
      simp only [range_factorization_coe]
      apply apply_range_splitting

theorem range_splitting_injective (f : α → β) : injective (range_splitting f) :=
  (left_inverse_range_splitting f).Injective

theorem right_inverse_range_splitting {f : α → β} (h : injective f) :
  RightInverse (range_factorization f) (range_splitting f) :=
  (left_inverse_range_splitting f).right_inverse_of_injective$ fun x y hxy => h$ Subtype.ext_iff.1 hxy

theorem preimage_range_splitting {f : α → β} (hf : injective f) :
  preimage (range_splitting f) = image (range_factorization f) :=
  (image_eq_preimage_of_inverse (right_inverse_range_splitting hf) (left_inverse_range_splitting f)).symm

theorem is_compl_range_some_none (α : Type _) : IsCompl (range (some : α → Option α)) {none} :=
  ⟨fun x ⟨⟨a, ha⟩, (hn : x = none)⟩ => Option.some_ne_none _ (ha.trans hn),
    fun x hx => Option.casesOn x (Or.inr rfl) fun x => Or.inl$ mem_range_self _⟩

@[simp]
theorem compl_range_some (α : Type _) : «expr ᶜ» (range (some : α → Option α)) = {none} :=
  (is_compl_range_some_none α).compl_eq

@[simp]
theorem range_some_inter_none (α : Type _) : range (some : α → Option α) ∩ {none} = ∅ :=
  (is_compl_range_some_none α).inf_eq_bot

@[simp]
theorem range_some_union_none (α : Type _) : range (some : α → Option α) ∪ {none} = univ :=
  (is_compl_range_some_none α).sup_eq_top

end Range

end Set

open Set

namespace Function

variable {ι : Sort _} {α : Type _} {β : Type _} {f : α → β}

theorem surjective.preimage_injective (hf : surjective f) : injective (preimage f) :=
  fun s t => (preimage_eq_preimage hf).1

theorem injective.preimage_image (hf : injective f) (s : Set α) : f ⁻¹' (f '' s) = s :=
  preimage_image_eq s hf

theorem injective.preimage_surjective (hf : injective f) : surjective (preimage f) :=
  by 
    intro s 
    use f '' s 
    rw [hf.preimage_image]

theorem injective.subsingleton_image_iff (hf : injective f) {s : Set α} : (f '' s).Subsingleton ↔ s.subsingleton :=
  ⟨subsingleton_of_image hf s, fun h => h.image f⟩

theorem surjective.image_preimage (hf : surjective f) (s : Set β) : f '' (f ⁻¹' s) = s :=
  image_preimage_eq s hf

theorem surjective.image_surjective (hf : surjective f) : surjective (image f) :=
  by 
    intro s 
    use f ⁻¹' s 
    rw [hf.image_preimage]

theorem surjective.nonempty_preimage (hf : surjective f) {s : Set β} : (f ⁻¹' s).Nonempty ↔ s.nonempty :=
  by 
    rw [←nonempty_image_iff, hf.image_preimage]

theorem injective.image_injective (hf : injective f) : injective (image f) :=
  by 
    intro s t h 
    rw [←preimage_image_eq s hf, ←preimage_image_eq t hf, h]

theorem surjective.preimage_subset_preimage_iff {s t : Set β} (hf : surjective f) : f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
  by 
    apply preimage_subset_preimage_iff 
    rw [hf.range_eq]
    apply subset_univ

theorem surjective.range_comp {ι' : Sort _} {f : ι → ι'} (hf : surjective f) (g : ι' → α) : range (g ∘ f) = range g :=
  ext$ fun y => (@surjective.exists _ _ _ hf fun x => g x = y).symm

theorem injective.nonempty_apply_iff {f : Set α → Set β} (hf : injective f) (h2 : f ∅ = ∅) {s : Set α} :
  (f s).Nonempty ↔ s.nonempty :=
  by 
    rw [←ne_empty_iff_nonempty, ←h2, ←ne_empty_iff_nonempty, hf.ne_iff]

theorem injective.mem_range_iff_exists_unique (hf : injective f) {b : β} : b ∈ range f ↔ ∃!a, f a = b :=
  ⟨fun ⟨a, h⟩ => ⟨a, h, fun a' ha => hf (ha.trans h.symm)⟩, ExistsUnique.exists⟩

theorem injective.exists_unique_of_mem_range (hf : injective f) {b : β} (hb : b ∈ range f) : ∃!a, f a = b :=
  hf.mem_range_iff_exists_unique.mp hb

theorem injective.compl_image_eq (hf : injective f) (s : Set α) :
  «expr ᶜ» (f '' s) = f '' «expr ᶜ» s ∪ «expr ᶜ» (range f) :=
  by 
    ext y 
    rcases em (y ∈ range f) with (⟨x, rfl⟩ | hx)
    ·
      simp [hf.eq_iff]
    ·
      rw [mem_range, not_exists] at hx 
      simp [hx]

theorem left_inverse.image_image {g : β → α} (h : left_inverse g f) (s : Set α) : g '' (f '' s) = s :=
  by 
    rw [←image_comp, h.comp_eq_id, image_id]

theorem left_inverse.preimage_preimage {g : β → α} (h : left_inverse g f) (s : Set α) : f ⁻¹' (g ⁻¹' s) = s :=
  by 
    rw [←preimage_comp, h.comp_eq_id, preimage_id]

end Function

open Function

theorem Option.injective_iff {α β} {f : Option α → β} :
  injective f ↔ injective (f ∘ some) ∧ f none ∉ range (f ∘ some) :=
  by 
    simp only [mem_range, not_exists, · ∘ ·]
    refine' ⟨fun hf => ⟨hf.comp (Option.some_injective _), fun x => hf.ne$ Option.some_ne_none _⟩, _⟩
    rintro ⟨h_some, h_none⟩ (_ | a) (_ | b) hab 
    exacts[rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_argₓ some (h_some hab)]

/-! ### Image and preimage on subtypes -/


namespace Subtype

variable {α : Type _}

theorem coe_image {p : α → Prop} {s : Set (Subtype p)} : coeₓ '' s = { x | ∃ h : p x, (⟨x, h⟩ : Subtype p) ∈ s } :=
  Set.ext$ fun a => ⟨fun ⟨⟨a', ha'⟩, in_s, h_eq⟩ => h_eq ▸ ⟨ha', in_s⟩, fun ⟨ha, in_s⟩ => ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp]
theorem coe_image_of_subset {s t : Set α} (h : t ⊆ s) : coeₓ '' { x:«expr↥ » s | «expr↑ » x ∈ t } = t :=
  by 
    ext x 
    rw [Set.mem_image]
    exact ⟨fun ⟨x', hx', hx⟩ => hx ▸ hx', fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩⟩

theorem range_coe {s : Set α} : range (coeₓ : s → α) = s :=
  by 
    rw [←Set.image_univ]
    simp [-Set.image_univ, coe_image]

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
theorem range_val {s : Set α} : range (Subtype.val : s → α) = s :=
  range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp]
theorem range_coe_subtype {p : α → Prop} : range (coeₓ : Subtype p → α) = { x | p x } :=
  range_coe

@[simp]
theorem coe_preimage_self (s : Set α) : (coeₓ : s → α) ⁻¹' s = univ :=
  by 
    rw [←preimage_range (coeₓ : s → α), range_coe]

theorem range_val_subtype {p : α → Prop} : range (Subtype.val : Subtype p → α) = { x | p x } :=
  range_coe

theorem coe_image_subset (s : Set α) (t : Set s) : coeₓ '' t ⊆ s :=
  fun x ⟨y, yt, yvaleq⟩ =>
    by 
      rw [←yvaleq] <;> exact y.property

theorem coe_image_univ (s : Set α) : (coeₓ : s → α) '' Set.Univ = s :=
  image_univ.trans range_coe

@[simp]
theorem image_preimage_coe (s t : Set α) : (coeₓ : s → α) '' (coeₓ ⁻¹' t) = t ∩ s :=
  image_preimage_eq_inter_range.trans$ congr_argₓ _ range_coe

theorem image_preimage_val (s t : Set α) : (Subtype.val : s → α) '' (Subtype.val ⁻¹' t) = t ∩ s :=
  image_preimage_coe s t

theorem preimage_coe_eq_preimage_coe_iff {s t u : Set α} : (coeₓ : s → α) ⁻¹' t = coeₓ ⁻¹' u ↔ t ∩ s = u ∩ s :=
  by 
    rw [←image_preimage_coe, ←image_preimage_coe]
    split 
    ·
      intro h 
      rw [h]
    intro h 
    exact coe_injective.image_injective h

theorem preimage_val_eq_preimage_val_iff (s t u : Set α) :
  (Subtype.val : s → α) ⁻¹' t = Subtype.val ⁻¹' u ↔ t ∩ s = u ∩ s :=
  preimage_coe_eq_preimage_coe_iff

theorem exists_set_subtype {t : Set α} (p : Set α → Prop) : (∃ s : Set t, p (coeₓ '' s)) ↔ ∃ s : Set α, s ⊆ t ∧ p s :=
  by 
    split 
    ·
      rintro ⟨s, hs⟩
      refine' ⟨coeₓ '' s, _, hs⟩
      convert image_subset_range _ _ 
      rw [range_coe]
    rintro ⟨s, hs₁, hs₂⟩
    refine' ⟨coeₓ ⁻¹' s, _⟩
    rw [image_preimage_eq_of_subset]
    exact hs₂ 
    rw [range_coe]
    exact hs₁

theorem preimage_coe_nonempty {s t : Set α} : ((coeₓ : s → α) ⁻¹' t).Nonempty ↔ (s ∩ t).Nonempty :=
  by 
    rw [inter_comm, ←image_preimage_coe, nonempty_image_iff]

theorem preimage_coe_eq_empty {s t : Set α} : (coeₓ : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ :=
  by 
    simp only [←not_nonempty_iff_eq_empty, preimage_coe_nonempty]

@[simp]
theorem preimage_coe_compl (s : Set α) : (coeₓ : s → α) ⁻¹' «expr ᶜ» s = ∅ :=
  preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp]
theorem preimage_coe_compl' (s : Set α) : (coeₓ : «expr ᶜ» s → α) ⁻¹' s = ∅ :=
  preimage_coe_eq_empty.2 (compl_inter_self s)

end Subtype

namespace Set

/-! ### Lemmas about cartesian product of sets -/


section Prod

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β}

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def Prod (s : Set α) (t : Set β) : Set (α × β) :=
  { p | p.1 ∈ s ∧ p.2 ∈ t }

theorem prod_eq (s : Set α) (t : Set β) : s.prod t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t :=
  rfl

theorem mem_prod_eq {p : α × β} : (p ∈ s.prod t) = (p.1 ∈ s ∧ p.2 ∈ t) :=
  rfl

@[simp]
theorem mem_prod {p : α × β} : p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl

@[simp]
theorem prod_mk_mem_set_prod_eq {a : α} {b : β} : ((a, b) ∈ s.prod t) = (a ∈ s ∧ b ∈ t) :=
  rfl

theorem mk_mem_prod {a : α} {b : β} (a_in : a ∈ s) (b_in : b ∈ t) : (a, b) ∈ s.prod t :=
  ⟨a_in, b_in⟩

theorem prod_mono {s₁ s₂ : Set α} {t₁ t₂ : Set β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.prod t₁ ⊆ s₂.prod t₂ :=
  fun x ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩

theorem prod_subset_iff {P : Set (α × β)} : s.prod t ⊆ P ↔ ∀ x _ : x ∈ s y _ : y ∈ t, (x, y) ∈ P :=
  ⟨fun h _ xin _ yin => h (mk_mem_prod xin yin), fun h ⟨_, _⟩ pin => h _ pin.1 _ pin.2⟩

theorem forall_prod_set {p : α × β → Prop} : (∀ x _ : x ∈ s.prod t, p x) ↔ ∀ x _ : x ∈ s y _ : y ∈ t, p (x, y) :=
  prod_subset_iff

theorem exists_prod_set {p : α × β → Prop} :
  (∃ (x : _)(_ : x ∈ s.prod t), p x) ↔ ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ t), p (x, y) :=
  by 
    simp [and_assoc]

@[simp]
theorem prod_empty : s.prod ∅ = (∅ : Set (α × β)) :=
  by 
    ext 
    simp 

@[simp]
theorem empty_prod : Set.Prod ∅ t = (∅ : Set (α × β)) :=
  by 
    ext 
    simp 

@[simp]
theorem univ_prod_univ : (@univ α).Prod (@univ β) = univ :=
  by 
    ext ⟨x, y⟩
    simp 

theorem univ_prod {t : Set β} : Set.Prod (univ : Set α) t = Prod.snd ⁻¹' t :=
  by 
    simp [prod_eq]

theorem prod_univ {s : Set α} : Set.Prod s (univ : Set β) = Prod.fst ⁻¹' s :=
  by 
    simp [prod_eq]

@[simp]
theorem singleton_prod {a : α} : Set.Prod {a} t = Prod.mk a '' t :=
  by 
    ext ⟨x, y⟩
    simp [And.left_comm, eq_comm]

@[simp]
theorem prod_singleton {b : β} : s.prod {b} = (fun a => (a, b)) '' s :=
  by 
    ext ⟨x, y⟩
    simp [And.left_comm, eq_comm]

theorem singleton_prod_singleton {a : α} {b : β} : Set.Prod {a} {b} = ({(a, b)} : Set (α × β)) :=
  by 
    simp 

@[simp]
theorem union_prod : (s₁ ∪ s₂).Prod t = s₁.prod t ∪ s₂.prod t :=
  by 
    ext ⟨x, y⟩
    simp [or_and_distrib_right]

@[simp]
theorem prod_union : s.prod (t₁ ∪ t₂) = s.prod t₁ ∪ s.prod t₂ :=
  by 
    ext ⟨x, y⟩
    simp [and_or_distrib_left]

theorem prod_inter_prod : s₁.prod t₁ ∩ s₂.prod t₂ = (s₁ ∩ s₂).Prod (t₁ ∩ t₂) :=
  by 
    ext ⟨x, y⟩
    simp [and_assoc, And.left_comm]

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_prod {a : α} : «expr = »((insert a s).prod t, «expr ∪ »(«expr '' »(prod.mk a, t), s.prod t)) :=
by { ext [] ["⟨", ident x, ",", ident y, "⟩"] [],
  simp [] [] [] ["[", expr image, ",", expr iff_def, ",", expr or_imp_distrib, ",", expr imp.swap, "]"] [] [] { contextual := tt } }

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_insert {b : β} : «expr = »(s.prod (insert b t), «expr ∪ »(«expr '' »(λ a, (a, b), s), s.prod t)) :=
by { ext [] ["⟨", ident x, ",", ident y, "⟩"] [],
  simp [] [] [] ["[", expr image, ",", expr iff_def, ",", expr or_imp_distrib, ",", expr imp.swap, "]"] [] [] { contextual := tt } }

theorem prod_preimage_eq {f : γ → α} {g : δ → β} : (f ⁻¹' s).Prod (g ⁻¹' t) = (fun p => (f p.1, g p.2)) ⁻¹' s.prod t :=
  rfl

theorem prod_preimage_left {f : γ → α} : (f ⁻¹' s).Prod t = (fun p => (f p.1, p.2)) ⁻¹' s.prod t :=
  rfl

theorem prod_preimage_right {g : δ → β} : s.prod (g ⁻¹' t) = (fun p => (p.1, g p.2)) ⁻¹' s.prod t :=
  rfl

theorem preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : Set β) (t : Set δ) :
  Prod.map f g ⁻¹' s.prod t = (f ⁻¹' s).Prod (g ⁻¹' t) :=
  rfl

theorem mk_preimage_prod (f : γ → α) (g : γ → β) : (fun x => (f x, g x)) ⁻¹' s.prod t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

@[simp]
theorem mk_preimage_prod_left {y : β} (h : y ∈ t) : (fun x => (x, y)) ⁻¹' s.prod t = s :=
  by 
    ext x 
    simp [h]

@[simp]
theorem mk_preimage_prod_right {x : α} (h : x ∈ s) : Prod.mk x ⁻¹' s.prod t = t :=
  by 
    ext y 
    simp [h]

@[simp]
theorem mk_preimage_prod_left_eq_empty {y : β} (hy : y ∉ t) : (fun x => (x, y)) ⁻¹' s.prod t = ∅ :=
  by 
    ext z 
    simp [hy]

@[simp]
theorem mk_preimage_prod_right_eq_empty {x : α} (hx : x ∉ s) : Prod.mk x ⁻¹' s.prod t = ∅ :=
  by 
    ext z 
    simp [hx]

theorem mk_preimage_prod_left_eq_if {y : β} [DecidablePred (· ∈ t)] :
  (fun x => (x, y)) ⁻¹' s.prod t = if y ∈ t then s else ∅ :=
  by 
    splitIfs <;> simp [h]

theorem mk_preimage_prod_right_eq_if {x : α} [DecidablePred (· ∈ s)] :
  Prod.mk x ⁻¹' s.prod t = if x ∈ s then t else ∅ :=
  by 
    splitIfs <;> simp [h]

theorem mk_preimage_prod_left_fn_eq_if {y : β} [DecidablePred (· ∈ t)] (f : γ → α) :
  (fun x => (f x, y)) ⁻¹' s.prod t = if y ∈ t then f ⁻¹' s else ∅ :=
  by 
    rw [←mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]

theorem mk_preimage_prod_right_fn_eq_if {x : α} [DecidablePred (· ∈ s)] (g : δ → β) :
  (fun y => (x, g y)) ⁻¹' s.prod t = if x ∈ s then g ⁻¹' t else ∅ :=
  by 
    rw [←mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]

theorem image_swap_eq_preimage_swap : image (@Prod.swap α β) = preimage Prod.swap :=
  image_eq_preimage_of_inverse Prod.swap_left_inverseₓ Prod.swap_right_inverseₓ

theorem preimage_swap_prod {s : Set α} {t : Set β} : Prod.swap ⁻¹' t.prod s = s.prod t :=
  by 
    ext ⟨x, y⟩
    simp [and_comm]

theorem image_swap_prod : Prod.swap '' t.prod s = s.prod t :=
  by 
    rw [image_swap_eq_preimage_swap, preimage_swap_prod]

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
  (m₁ '' s).Prod (m₂ '' t) = image (fun p : α × β => (m₁ p.1, m₂ p.2)) (s.prod t) :=
  ext$
    by 
      simp [-exists_and_distrib_right, exists_and_distrib_right.symm, And.left_comm, And.assoc, And.comm]

theorem prod_range_range_eq {α β γ δ} {m₁ : α → γ} {m₂ : β → δ} :
  (range m₁).Prod (range m₂) = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext$
    by 
      simp [range]

@[simp]
theorem range_prod_map {α β γ δ} {m₁ : α → γ} {m₂ : β → δ} : range (Prod.map m₁ m₂) = (range m₁).Prod (range m₂) :=
  prod_range_range_eq.symm

theorem prod_range_univ_eq {α β γ} {m₁ : α → γ} :
  (range m₁).Prod (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
  ext$
    by 
      simp [range]

theorem prod_univ_range_eq {α β δ} {m₂ : β → δ} :
  (univ : Set α).Prod (range m₂) = range fun p : α × β => (p.1, m₂ p.2) :=
  ext$
    by 
      simp [range]

theorem range_pair_subset {α β γ : Type _} (f : α → β) (g : α → γ) :
  (range fun x => (f x, g x)) ⊆ (range f).Prod (range g) :=
  have  : (fun x => (f x, g x)) = Prod.map f g ∘ fun x => (x, x) := funext fun x => rfl 
  by 
    rw [this, ←range_prod_map]
    apply range_comp_subset_range

theorem nonempty.prod : s.nonempty → t.nonempty → (s.prod t).Nonempty
| ⟨x, hx⟩, ⟨y, hy⟩ => ⟨(x, y), ⟨hx, hy⟩⟩

theorem nonempty.fst : (s.prod t).Nonempty → s.nonempty
| ⟨p, hp⟩ => ⟨p.1, hp.1⟩

theorem nonempty.snd : (s.prod t).Nonempty → t.nonempty
| ⟨p, hp⟩ => ⟨p.2, hp.2⟩

theorem prod_nonempty_iff : (s.prod t).Nonempty ↔ s.nonempty ∧ t.nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => nonempty.prod h.1 h.2⟩

theorem prod_eq_empty_iff : s.prod t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  by 
    simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_distrib]

theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} : s.prod t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W :=
  by 
    simp [subset_def]

theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s.prod t ⊆ s :=
  fun _ h =>
    let ⟨_, ⟨h₂, _⟩, h₁⟩ := (Set.mem_image _ _ _).1 h 
    h₁ ▸ h₂

theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s.prod t ⊆ Prod.fst ⁻¹' s :=
  image_subset_iff.1 (fst_image_prod_subset s t)

theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.nonempty) : Prod.fst '' s.prod t = s :=
  Set.Subset.antisymm (fst_image_prod_subset _ _)$
    fun y y_in =>
      let ⟨x, x_in⟩ := ht
      ⟨(y, x), ⟨y_in, x_in⟩, rfl⟩

theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s.prod t ⊆ t :=
  fun _ h =>
    let ⟨_, ⟨_, h₂⟩, h₁⟩ := (Set.mem_image _ _ _).1 h 
    h₁ ▸ h₂

theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s.prod t ⊆ Prod.snd ⁻¹' t :=
  image_subset_iff.1 (snd_image_prod_subset s t)

theorem snd_image_prod {s : Set α} (hs : s.nonempty) (t : Set β) : Prod.snd '' s.prod t = t :=
  Set.Subset.antisymm (snd_image_prod_subset _ _)$
    fun y y_in =>
      let ⟨x, x_in⟩ := hs
      ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

theorem prod_diff_prod : s.prod t \ s₁.prod t₁ = s.prod (t \ t₁) ∪ (s \ s₁).Prod t :=
  by 
    ext x 
    byCases' h₁ : x.1 ∈ s₁ <;> byCases' h₂ : x.2 ∈ t₁ <;> simp 

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
theorem prod_subset_prod_iff : «expr ↔ »(«expr ⊆ »(s.prod t, s₁.prod t₁), «expr ∨ »(«expr ∧ »(«expr ⊆ »(s, s₁), «expr ⊆ »(t, t₁)), «expr ∨ »(«expr = »(s, «expr∅»()), «expr = »(t, «expr∅»())))) :=
begin
  classical,
  cases [expr (s.prod t).eq_empty_or_nonempty] ["with", ident h, ident h],
  { simp [] [] [] ["[", expr h, ",", expr prod_eq_empty_iff.1 h, "]"] [] [] },
  { have [ident st] [":", expr «expr ∧ »(s.nonempty, t.nonempty)] [],
    by rwa ["[", expr prod_nonempty_iff, "]"] ["at", ident h],
    split,
    { assume [binders (H : «expr ⊆ »(s.prod t, s₁.prod t₁))],
      have [ident h'] [":", expr «expr ∧ »(s₁.nonempty, t₁.nonempty)] [":=", expr prod_nonempty_iff.1 (h.mono H)],
      refine [expr or.inl ⟨_, _⟩],
      show [expr «expr ⊆ »(s, s₁)],
      { have [] [] [":=", expr image_subset (prod.fst : «expr × »(α, β) → α) H],
        rwa ["[", expr fst_image_prod _ st.2, ",", expr fst_image_prod _ h'.2, "]"] ["at", ident this] },
      show [expr «expr ⊆ »(t, t₁)],
      { have [] [] [":=", expr image_subset (prod.snd : «expr × »(α, β) → β) H],
        rwa ["[", expr snd_image_prod st.1, ",", expr snd_image_prod h'.1, "]"] ["at", ident this] } },
    { assume [binders (H)],
      simp [] [] ["only"] ["[", expr st.1.ne_empty, ",", expr st.2.ne_empty, ",", expr or_false, "]"] [] ["at", ident H],
      exact [expr prod_mono H.1 H.2] } }
end

end Prod

/-! ### Lemmas about set-indexed products of sets -/


section Pi

variable {ι : Type _} {α : ι → Type _} {s s₁ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)}

/-- Given an index set `ι` and a family of sets `t : Π i, set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `t a`
whenever `a ∈ s`. -/
def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) :=
  { f | ∀ i _ : i ∈ s, f i ∈ t i }

@[simp]
theorem mem_pi {f : ∀ i, α i} : f ∈ s.pi t ↔ ∀ i _ : i ∈ s, f i ∈ t i :=
  by 
    rfl

@[simp]
theorem mem_univ_pi {f : ∀ i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i :=
  by 
    simp 

@[simp]
theorem empty_pi (s : ∀ i, Set (α i)) : pi ∅ s = univ :=
  by 
    ext 
    simp [pi]

@[simp]
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall$ fun f i hi => mem_univ _

theorem pi_mono (h : ∀ i _ : i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ :=
  fun x hx i hi => h i hi$ hx i hi

theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
  ext$
    fun x =>
      by 
        simp only [forall_and_distrib, mem_pi, mem_inter_eq]

theorem pi_congr (h : s = s₁) (h' : ∀ i _ : i ∈ s, t i = t₁ i) : pi s t = pi s₁ t₁ :=
  h ▸ (ext$ fun x => forall_congrₓ$ fun i => forall_congrₓ$ fun hi => h' i hi ▸ Iff.rfl)

theorem pi_eq_empty {i : ι} (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
  by 
    ext f 
    simp only [mem_empty_eq, not_forall, iff_falseₓ, mem_pi, not_imp]
    exact
      ⟨i, hs,
        by 
          simp [ht]⟩

theorem univ_pi_eq_empty {i : ι} (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht

theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i :=
  by 
    simp [Classical.skolem, Set.Nonempty]

theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ ∀ i, (t i).Nonempty :=
  by 
    simp [Classical.skolem, Set.Nonempty]

theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, (α i → False) ∨ i ∈ s ∧ t i = ∅ :=
  by 
    rw [←not_nonempty_iff_eq_empty, pi_nonempty_iff]
    pushNeg 
    apply exists_congr 
    intro i 
    split 
    ·
      intro h 
      byCases' hα : Nonempty (α i)
      ·
        cases' hα with x 
        refine'
          Or.inr
            ⟨(h x).1,
              by 
                simp [eq_empty_iff_forall_not_mem, h]⟩
      ·
        exact Or.inl fun x => hα ⟨x⟩
    ·
      rintro (h | h) x 
      exfalso 
      exact h x 
      simp [h]

theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ :=
  by 
    simp [←not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp]
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun i => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2$ h.elim$ fun x => ⟨x, rfl⟩

@[simp]
theorem range_dcomp {β : ι → Type _} (f : ∀ i, α i → β i) :
  (range fun g : ∀ i, α i => fun i => f i (g i)) = pi univ fun i => range (f i) :=
  by 
    apply subset.antisymm
    ·
      rintro _ ⟨x, rfl⟩ i -
      exact ⟨x i, rfl⟩
    ·
      intro x hx 
      choose y hy using hx 
      exact ⟨fun i => y i trivialₓ, funext$ fun i => hy i trivialₓ⟩

@[simp]
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) : pi (insert i s) t = eval i ⁻¹' t i ∩ pi s t :=
  by 
    ext 
    simp [pi, or_imp_distrib, forall_and_distrib]

@[simp]
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = eval i ⁻¹' t i :=
  by 
    ext 
    simp [pi]

theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t

theorem pi_if {p : ι → Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : ∀ i, Set (α i)) :
  (pi s fun i => if p i then t₁ i else t₂ i) = pi { i∈s | p i } t₁ ∩ pi { i∈s | ¬p i } t₂ :=
  by 
    ext f 
    split 
    ·
      intro h 
      split  <;>
        ·
          rintro i ⟨his, hpi⟩
          simpa [*] using h i
    ·
      rintro ⟨ht₁, ht₂⟩ i his 
      byCases' p i <;> simp_all 

theorem union_pi : (s ∪ s₁).pi t = s.pi t ∩ s₁.pi t :=
  by 
    simp [pi, or_imp_distrib, forall_and_distrib, set_of_and]

@[simp]
theorem pi_inter_compl (s : Set ι) : pi s t ∩ pi («expr ᶜ» s) t = pi univ t :=
  by 
    rw [←union_pi, union_compl_self]

theorem pi_update_of_not_mem [DecidableEq ι] {β : ∀ i, Type _} {i : ι} (hi : i ∉ s) (f : ∀ j, α j) (a : α i)
  (t : ∀ j, α j → Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  pi_congr rfl$
    fun j hj =>
      by 
        rw [update_noteq]
        exact fun h => hi (h ▸ hj)

theorem pi_update_of_mem [DecidableEq ι] {β : ∀ i, Type _} {i : ι} (hi : i ∈ s) (f : ∀ j, α j) (a : α i)
  (t : ∀ j, α j → Set (β j)) :
  (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) :=
    by 
      rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
    by 
      rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem]
      simp 
    

theorem univ_pi_update [DecidableEq ι] {β : ∀ i, Type _} (i : ι) (f : ∀ j, α j) (a : α i) (t : ∀ j, α j → Set (β j)) :
  (pi univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ pi («expr ᶜ» {i}) fun j => t j (f j) :=
  by 
    rw [compl_eq_univ_diff, ←pi_update_of_mem (mem_univ _)]

theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
  pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s :=
  by 
    rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]

open_locale Classical

theorem eval_image_pi {i : ι} (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  by 
    ext x 
    rcases ht with ⟨f, hf⟩
    split 
    ·
      rintro ⟨g, hg, rfl⟩
      exact hg i hs
    ·
      intro hg 
      refine'
        ⟨update f i x, _,
          by 
            simp ⟩
      intro j hj 
      byCases' hji : j = i
      ·
        subst hji 
        simp [hg]
      ·
        rw [mem_pi] at hf 
        simp [hji, hf, hj]

@[simp]
theorem eval_image_univ_pi {i : ι} (ht : (pi univ t).Nonempty) : (fun f : ∀ i, α i => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht

theorem eval_preimage {ι} {α : ι → Type _} {i : ι} {s : Set (α i)} :
  eval i ⁻¹' s = pi univ (update (fun i => univ) i s) :=
  by 
    ext x 
    simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]

theorem eval_preimage' {ι} {α : ι → Type _} {i : ι} {s : Set (α i)} :
  eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) :=
  by 
    ext 
    simp 

theorem update_preimage_pi {i : ι} {f : ∀ i, α i} (hi : i ∈ s) (hf : ∀ j _ : j ∈ s, j ≠ i → f j ∈ t j) :
  update f i ⁻¹' s.pi t = t i :=
  by 
    ext x 
    split 
    ·
      intro h 
      convert h i hi 
      simp 
    ·
      intro hx j hj 
      byCases' h : j = i
      ·
        cases h 
        simpa
      ·
        rw [update_noteq h]
        exact hf j hj h

theorem update_preimage_univ_pi {i : ι} {f : ∀ i, α i} (hf : ∀ j _ : j ≠ i, f j ∈ t j) :
  update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j

theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ pi s fun i => eval i '' u :=
  fun f hf i hi => ⟨f, hf, rfl⟩

theorem univ_pi_ite (s : Set ι) (t : ∀ i, Set (α i)) : (pi univ fun i => if i ∈ s then t i else univ) = s.pi t :=
  by 
    ext 
    simpRw [mem_univ_pi]
    apply forall_congrₓ 
    intro i 
    splitIfs <;> simp [h]

end Pi

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/


section Inclusion

variable {α : Type _}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion {s t : Set α} (h : s ⊆ t) : s → t :=
  fun x : s => (⟨x, h x.2⟩ : t)

@[simp]
theorem inclusion_self {s : Set α} (x : s) : inclusion (Set.Subset.refl _) x = x :=
  by 
    cases x 
    rfl

@[simp]
theorem inclusion_right {s t : Set α} (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x :=
  by 
    cases x 
    rfl

@[simp]
theorem inclusion_inclusion {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
  inclusion htu (inclusion hst x) = inclusion (Set.Subset.trans hst htu) x :=
  by 
    cases x 
    rfl

@[simp]
theorem coe_inclusion {s t : Set α} (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl

theorem inclusion_injective {s t : Set α} (h : s ⊆ t) : Function.Injective (inclusion h)
| ⟨_, _⟩, ⟨_, _⟩ => Subtype.ext_iff_val.2 ∘ Subtype.ext_iff_val.1

@[simp]
theorem range_inclusion {s t : Set α} (h : s ⊆ t) : range (inclusion h) = { x:t | (x : α) ∈ s } :=
  by 
    ext ⟨x, hx⟩
    simp [inclusion]

theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t} (h_surj : Function.Surjective (inclusion h)) : s = t :=
  by 
    rw [←range_iff_surjective, range_inclusion, eq_univ_iff_forall] at h_surj 
    exact Set.Subset.antisymm h fun x hx => h_surj ⟨x, hx⟩

end Inclusion

/-! ### Injectivity and surjectivity lemmas for image and preimage -/


section ImagePreimage

variable {α : Type u} {β : Type v} {f : α → β}

@[simp]
theorem preimage_injective : injective (preimage f) ↔ surjective f :=
  by 
    refine' ⟨fun h y => _, surjective.preimage_injective⟩
    obtain ⟨x, hx⟩ : (f ⁻¹' {y}).Nonempty
    ·
      rw [h.nonempty_apply_iff preimage_empty]
      apply singleton_nonempty 
    exact ⟨x, hx⟩

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem preimage_surjective : «expr ↔ »(surjective (preimage f), injective f) :=
begin
  refine [expr ⟨λ h x x' hx, _, injective.preimage_surjective⟩],
  cases [expr h {x}] ["with", ident s, ident hs],
  have [] [] [":=", expr mem_singleton x],
  rwa ["[", "<-", expr hs, ",", expr mem_preimage, ",", expr hx, ",", "<-", expr mem_preimage, ",", expr hs, ",", expr mem_singleton_iff, ",", expr eq_comm, "]"] ["at", ident this]
end

-- error in Data.Set.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem image_surjective : «expr ↔ »(surjective (image f), surjective f) :=
begin
  refine [expr ⟨λ h y, _, surjective.image_surjective⟩],
  cases [expr h {y}] ["with", ident s, ident hs],
  have [] [] [":=", expr mem_singleton y],
  rw ["[", "<-", expr hs, "]"] ["at", ident this],
  rcases [expr this, "with", "⟨", ident x, ",", ident h1x, ",", ident h2x, "⟩"],
  exact [expr ⟨x, h2x⟩]
end

@[simp]
theorem image_injective : injective (image f) ↔ injective f :=
  by 
    refine' ⟨fun h x x' hx => _, injective.image_injective⟩
    rw [←singleton_eq_singleton_iff]
    apply h 
    rw [image_singleton, image_singleton, hx]

theorem preimage_eq_iff_eq_image {f : α → β} (hf : bijective f) {s t} : f ⁻¹' s = t ↔ s = f '' t :=
  by 
    rw [←image_eq_image hf.1, hf.2.image_preimage]

theorem eq_preimage_iff_image_eq {f : α → β} (hf : bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t :=
  by 
    rw [←image_eq_image hf.1, hf.2.image_preimage]

end ImagePreimage

/-! ### Lemmas about images of binary and ternary functions -/


section NAryImage

variable {α β γ δ ε : Type _} {f f' : α → β → γ} {g g' : α → β → γ → δ}

variable {s s' : Set α} {t t' : Set β} {u u' : Set γ} {a a' : α} {b b' : β} {c c' : γ} {d d' : δ}

/-- The image of a binary function `f : α → β → γ` as a function `set α → set β → set γ`.
  Mathematically this should be thought of as the image of the corresponding function `α × β → γ`.
-/
def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ :=
  { c | ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c }

theorem mem_image2_eq : (c ∈ image2 f s t) = ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c :=
  rfl

@[simp]
theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c :=
  Iff.rfl

theorem mem_image2_of_mem (h1 : a ∈ s) (h2 : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, b, h1, h2, rfl⟩

theorem mem_image2_iff (hf : injective2 f) : f a b ∈ image2 f s t ↔ a ∈ s ∧ b ∈ t :=
  ⟨by 
      rintro ⟨a', b', ha', hb', h⟩
      rcases hf h with ⟨rfl, rfl⟩
      exact ⟨ha', hb'⟩,
    fun ⟨ha, hb⟩ => mem_image2_of_mem ha hb⟩

/-- image2 is monotone with respect to `⊆`. -/
theorem image2_subset (hs : s ⊆ s') (ht : t ⊆ t') : image2 f s t ⊆ image2 f s' t' :=
  by 
    rintro _ ⟨a, b, ha, hb, rfl⟩
    exact mem_image2_of_mem (hs ha) (ht hb)

theorem forall_image2_iff {p : γ → Prop} : (∀ z _ : z ∈ image2 f s t, p z) ↔ ∀ x _ : x ∈ s y _ : y ∈ t, p (f x y) :=
  ⟨fun h x hx y hy => h _ ⟨x, y, hx, hy, rfl⟩, fun h z ⟨x, y, hx, hy, hz⟩ => hz ▸ h x hx y hy⟩

@[simp]
theorem image2_subset_iff {u : Set γ} : image2 f s t ⊆ u ↔ ∀ x _ : x ∈ s y _ : y ∈ t, f x y ∈ u :=
  forall_image2_iff

theorem image2_union_left : image2 f (s ∪ s') t = image2 f s t ∪ image2 f s' t :=
  by 
    ext c 
    split 
    ·
      rintro ⟨a, b, h1a | h2a, hb, rfl⟩ <;> [left, right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
    ·
      rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, _, ‹_›, rfl⟩ <;> simp [mem_union]

theorem image2_union_right : image2 f s (t ∪ t') = image2 f s t ∪ image2 f s t' :=
  by 
    ext c 
    split 
    ·
      rintro ⟨a, b, ha, h1b | h2b, rfl⟩ <;> [left, right] <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩
    ·
      rintro (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> refine' ⟨_, _, ‹_›, _, rfl⟩ <;> simp [mem_union]

@[simp]
theorem image2_empty_left : image2 f ∅ t = ∅ :=
  ext$
    by 
      simp 

@[simp]
theorem image2_empty_right : image2 f s ∅ = ∅ :=
  ext$
    by 
      simp 

theorem image2_inter_subset_left : image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t :=
  by 
    rintro _ ⟨a, b, ⟨h1a, h2a⟩, hb, rfl⟩
    split  <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩

theorem image2_inter_subset_right : image2 f s (t ∩ t') ⊆ image2 f s t ∩ image2 f s t' :=
  by 
    rintro _ ⟨a, b, ha, ⟨h1b, h2b⟩, rfl⟩
    split  <;> exact ⟨_, _, ‹_›, ‹_›, rfl⟩

@[simp]
theorem image2_singleton_left : image2 f {a} t = f a '' t :=
  ext$
    fun x =>
      by 
        simp 

@[simp]
theorem image2_singleton_right : image2 f s {b} = (fun a => f a b) '' s :=
  ext$
    fun x =>
      by 
        simp 

theorem image2_singleton : image2 f {a} {b} = {f a b} :=
  by 
    simp 

@[congr]
theorem image2_congr (h : ∀ a _ : a ∈ s b _ : b ∈ t, f a b = f' a b) : image2 f s t = image2 f' s t :=
  by 
    ext 
    split  <;>
      rintro ⟨a, b, ha, hb, rfl⟩ <;>
        refine'
          ⟨a, b, ha, hb,
            by 
              rw [h a ha b hb]⟩

/-- A common special case of `image2_congr` -/
theorem image2_congr' (h : ∀ a b, f a b = f' a b) : image2 f s t = image2 f' s t :=
  image2_congr fun a _ b _ => h a b

/-- The image of a ternary function `f : α → β → γ → δ` as a function
  `set α → set β → set γ → set δ`. Mathematically this should be thought of as the image of the
  corresponding function `α × β × γ → δ`.
-/
def image3 (g : α → β → γ → δ) (s : Set α) (t : Set β) (u : Set γ) : Set δ :=
  { d | ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d }

@[simp]
theorem mem_image3 : d ∈ image3 g s t u ↔ ∃ a b c, a ∈ s ∧ b ∈ t ∧ c ∈ u ∧ g a b c = d :=
  Iff.rfl

@[congr]
theorem image3_congr (h : ∀ a _ : a ∈ s b _ : b ∈ t c _ : c ∈ u, g a b c = g' a b c) :
  image3 g s t u = image3 g' s t u :=
  by 
    ext x 
    split  <;>
      rintro ⟨a, b, c, ha, hb, hc, rfl⟩ <;>
        exact
          ⟨a, b, c, ha, hb, hc,
            by 
              rw [h a ha b hb c hc]⟩

/-- A common special case of `image3_congr` -/
theorem image3_congr' (h : ∀ a b c, g a b c = g' a b c) : image3 g s t u = image3 g' s t u :=
  image3_congr fun a _ b _ c _ => h a b c

theorem image2_image2_left (f : δ → γ → ε) (g : α → β → δ) :
  image2 f (image2 g s t) u = image3 (fun a b c => f (g a b) c) s t u :=
  by 
    ext 
    split 
    ·
      rintro ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩
      refine' ⟨a, b, c, ha, hb, hc, rfl⟩
    ·
      rintro ⟨a, b, c, ha, hb, hc, rfl⟩
      refine' ⟨_, c, ⟨a, b, ha, hb, rfl⟩, hc, rfl⟩

theorem image2_image2_right (f : α → δ → ε) (g : β → γ → δ) :
  image2 f s (image2 g t u) = image3 (fun a b c => f a (g b c)) s t u :=
  by 
    ext 
    split 
    ·
      rintro ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩
      refine' ⟨a, b, c, ha, hb, hc, rfl⟩
    ·
      rintro ⟨a, b, c, ha, hb, hc, rfl⟩
      refine' ⟨a, _, ha, ⟨b, c, hb, hc, rfl⟩, rfl⟩

theorem image2_assoc {ε'} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
  (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) : image2 f (image2 g s t) u = image2 f' s (image2 g' t u) :=
  by 
    simp only [image2_image2_left, image2_image2_right, h_assoc]

theorem image_image2 (f : α → β → γ) (g : γ → δ) : g '' image2 f s t = image2 (fun a b => g (f a b)) s t :=
  by 
    ext 
    split 
    ·
      rintro ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩
      refine' ⟨a, b, ha, hb, rfl⟩
    ·
      rintro ⟨a, b, ha, hb, rfl⟩
      refine' ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩

theorem image2_image_left (f : γ → β → δ) (g : α → γ) : image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t :=
  by 
    ext 
    split 
    ·
      rintro ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩
      refine' ⟨a, b, ha, hb, rfl⟩
    ·
      rintro ⟨a, b, ha, hb, rfl⟩
      refine' ⟨_, b, ⟨a, ha, rfl⟩, hb, rfl⟩

theorem image2_image_right (f : α → γ → δ) (g : β → γ) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t :=
  by 
    ext 
    split 
    ·
      rintro ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩
      refine' ⟨a, b, ha, hb, rfl⟩
    ·
      rintro ⟨a, b, ha, hb, rfl⟩
      refine' ⟨a, _, ha, ⟨b, hb, rfl⟩, rfl⟩

theorem image2_swap (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = image2 (fun a b => f b a) t s :=
  by 
    ext 
    split  <;> rintro ⟨a, b, ha, hb, rfl⟩ <;> refine' ⟨b, a, hb, ha, rfl⟩

@[simp]
theorem image2_left (h : t.nonempty) : image2 (fun x y => x) s t = s :=
  by 
    simp [nonempty_def.mp h, ext_iff]

@[simp]
theorem image2_right (h : s.nonempty) : image2 (fun x y => y) s t = t :=
  by 
    simp [nonempty_def.mp h, ext_iff]

@[simp]
theorem image_prod (f : α → β → γ) : (fun x : α × β => f x.1 x.2) '' s.prod t = image2 f s t :=
  Set.ext$
    fun a =>
      ⟨by 
          rintro ⟨_, _, rfl⟩
          exact ⟨_, _, (mem_prod.mp ‹_›).1, (mem_prod.mp ‹_›).2, rfl⟩,
        by 
          rintro ⟨_, _, _, _, rfl⟩
          exact ⟨(_, _), mem_prod.mpr ⟨‹_›, ‹_›⟩, rfl⟩⟩

theorem nonempty.image2 (hs : s.nonempty) (ht : t.nonempty) : (image2 f s t).Nonempty :=
  by 
    cases' hs with a ha 
    cases' ht with b hb 
    exact ⟨f a b, ⟨a, b, ha, hb, rfl⟩⟩

end NAryImage

end Set

namespace Subsingleton

variable {α : Type _} [Subsingleton α]

theorem eq_univ_of_nonempty {s : Set α} : s.nonempty → s = univ :=
  fun ⟨x, hx⟩ => eq_univ_of_forall$ fun y => Subsingleton.elimₓ x y ▸ hx

@[elab_as_eliminator]
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p univ) s : p s :=
  (s.eq_empty_or_nonempty.elim fun h => h.symm ▸ h0)$ fun h => (eq_univ_of_nonempty h).symm ▸ h1

theorem mem_iff_nonempty {α : Type _} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elimₓ y x ▸ hy⟩

end Subsingleton

