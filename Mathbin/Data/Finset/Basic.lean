import Mathbin.Data.Int.Basic 
import Mathbin.Data.Multiset.FinsetOps 
import Mathbin.Tactic.Apply 
import Mathbin.Tactic.Monotonicity.Default 
import Mathbin.Tactic.NthRewrite.Default

/-!
# Finite sets

Terms of type `finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `finset α` is defined as a structure with 2 fields:

  1. `val` is a `multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `list` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

  1. `∑ i in (s : finset α), f i`;
  2. `∏ i in (s : finset α), f i`.

Lean refers to these operations as `big_operator`s.
More information can be found in `algebra.big_operators.basic`.

Finsets are directly used to define fintypes in Lean.
A `fintype α` instance for a type `α` consists of
a universal `finset α` containing every term of `α`, called `univ`. See `data.fintype.basic`.
There is also `univ'`, the noncomputable partner to `univ`,
which is defined to be `α` as a finset if `α` is finite,
and the empty finset otherwise. See `data.fintype.basic`.

## Main declarations

### Main definitions

* `finset`: Defines a type for the finite subsets of `α`.
  Constructing a `finset` requires two pieces of data: `val`, a `multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `finset.has_mem`: Defines membership `a ∈ (s : finset α)`.
* `finset.has_coe`: Provides a coercion `s : finset α` to `s : set α`.
* `finset.has_coe_to_sort`: Coerce `s : finset α` to the type of all `x ∈ s`.
* `finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `finset α`,
  then it holds for the finset obtained by inserting a new element.
* `finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.
* `finset.card`: `card s : ℕ` returns the cardinalilty of `s : finset α`.
  The API for `card`'s interaction with operations on finsets is extensive.
  TODO: The noncomputable sister `fincard` is about to be added into mathlib.

### Finset constructions

* `singleton`: Denoted by `{a}`; the finset consisting of one element.
* `finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.
* `finset.attach`: Given `s : finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `finset.filter`: Given a predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`order.lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and `⊤` is
called `top` with `⊤ = univ`.

* `finset.subset`: Lots of API about lattices, otherwise behaves exactly as one would expect.
* `finset.union`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `finset.sup`/`finset.bUnion` for finite unions.
* `finset.inter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  See `finset.inf` for finite intersections.
* `finset.disj_union`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disj_union t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.

### Operations on two or more finsets

* `finset.insert` and `finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.
* `finset.union`: see "The lattice structure on subsets of finsets"
* `finset.inter`: see "The lattice structure on subsets of finsets"
* `finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `finset.sdiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `finset.product`: Given finsets of `α` and `β`, defines finsets of `α × β`.
  For arbitrary dependent products, see `data.finset.pi`.
* `finset.sigma`: Given finsets of `α` and `β`, defines finsets of the dependent sum type `Σ α, β`
* `finset.bUnion`: Finite unions of finsets; given an indexing function `f : α → finset β` and a
  `s : finset α`, `s.bUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.
* `finset.bInter`: TODO: Implemement finite intersections.

### Maps constructed using finsets

* `finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function which is equal
  to `f` on `s` and `g` on the complement.

### Predicates on finsets

* `disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `finset.nonempty`: A finset is nonempty if it has elements.
  This is equivalent to saying `s ≠ ∅`. TODO: Decide on the simp normal form.

### Equivalences between finsets

* The `data.equiv` files describe a general type of equivalence, so look in there for any lemmas.
  There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/


open Multiset Subtype Nat Function

universe u

variable{α : Type _}{β : Type _}{γ : Type _}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset(α : Type _) where 
  val : Multiset α 
  Nodup : nodup val

namespace Finset

theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t
| ⟨s, _⟩, ⟨t, _⟩, rfl => rfl

@[simp]
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  ⟨eq_of_veq, congr_argₓ _⟩

@[simp]
theorem erase_dup_eq_self [DecidableEq α] (s : Finset α) : erase_dup s.1 = s.1 :=
  s.2.eraseDup

instance has_decidable_eq [DecidableEq α] : DecidableEq (Finset α)
| s₁, s₂ => decidableOfIff _ val_inj

/-! ### membership -/


instance  : HasMem α (Finset α) :=
  ⟨fun a s => a ∈ s.1⟩

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl

@[simp]
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl

instance decidable_mem [h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _

/-! ### set coercion -/


/-- Convert a finset to a set in the natural way. -/
instance  : CoeTₓ (Finset α) (Set α) :=
  ⟨fun s => { x | x ∈ s }⟩

@[simp, normCast]
theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem set_of_mem {α} {s : Finset α} : { a | a ∈ s } = s :=
  rfl

@[simp]
theorem coe_mem {s : Finset α} (x : (s : Set α)) : «expr↑ » x ∈ s :=
  x.2

@[simp]
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _

instance decidable_mem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ (s : Set α)) :=
  s.decidable_mem _

/-! ### extensionality -/


theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
  val_inj.symm.trans$ nodup_ext s₁.2 s₂.2

@[ext]
theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  ext_iff.2

@[simp, normCast]
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  Set.ext_iff.trans ext_iff.symm

theorem coe_injective {α} : injective (coeₓ : Finset α → Set α) :=
  fun s t => coe_inj.1

/-! ### type coercion -/


/-- Coercion from a finset to the corresponding subtype. -/
instance  {α : Type u} : CoeSort (Finset α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

instance pi_finset_coe.can_lift (ι : Type _) (α : ∀ (i : ι), Type _) [ne : ∀ i, Nonempty (α i)] (s : Finset ι) :
  CanLift (∀ (i : s), α i) (∀ i, α i) :=
  { PiSubtype.canLift ι α (· ∈ s) with coe := fun f i => f i }

instance pi_finset_coe.can_lift' (ι α : Type _) [ne : Nonempty α] (s : Finset ι) : CanLift (s → α) (ι → α) :=
  pi_finset_coe.can_lift ι (fun _ => α) s

instance finset_coe.can_lift (s : Finset α) : CanLift α s :=
  { coe := coeₓ, cond := fun a => a ∈ s, prf := fun a ha => ⟨⟨a, ha⟩, rfl⟩ }

@[simp, normCast]
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl

/-! ### subset -/


instance  : HasSubset (Finset α) :=
  ⟨fun s₁ s₂ => ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂⟩

theorem subset_def {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ s₁.1 ⊆ s₂.1 :=
  Iff.rfl

@[simp]
theorem subset.refl (s : Finset α) : s ⊆ s :=
  subset.refl _

theorem subset_of_eq {s t : Finset α} (h : s = t) : s ⊆ t :=
  h ▸ subset.refl _

theorem subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  subset.trans

theorem superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ :=
  fun h' h => subset.trans h h'

attribute [local trans] subset.trans superset.trans

theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  mem_of_subset

theorem subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext$ fun a => ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl

@[simp, normCast]
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊆ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl

@[simp]
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ :=
  le_iff_subset s₁.2

instance  : HasSsubset (Finset α) :=
  ⟨fun a b => a ⊆ b ∧ ¬b ⊆ a⟩

instance  : PartialOrderₓ (Finset α) :=
  { le := · ⊆ ·, lt := · ⊂ ·, le_refl := subset.refl, le_trans := @subset.trans _, le_antisymm := @subset.antisymm _ }

/-- Coercion to `set α` as an `order_embedding`. -/
def coe_emb : Finset α ↪o Set α :=
  ⟨⟨coeₓ, coe_injective⟩, fun s t => coe_subset⟩

@[simp]
theorem coe_coe_emb : «expr⇑ » (coe_emb : Finset α ↪o Set α) = coeₓ :=
  rfl

theorem subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iffₓ

theorem not_subset (s t : Finset α) : ¬s ⊆ t ↔ ∃ (x : _)(_ : x ∈ s), ¬x ∈ t :=
  by 
    simp only [←Finset.coe_subset, Set.not_subset, exists_prop, Finset.mem_coe]

@[simp]
theorem le_eq_subset : (· ≤ · : Finset α → Finset α → Prop) = (· ⊆ ·) :=
  rfl

@[simp]
theorem lt_eq_subset : (· < · : Finset α → Finset α → Prop) = (· ⊂ ·) :=
  rfl

theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl

theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl

@[simp, normCast]
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
  show (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁ by 
    simp only [Set.ssubset_def, Finset.coe_subset]

@[simp]
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff$ not_congr val_le_iff

theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne _ _ s t

theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ (x : _)(_ : x ∈ s₂), x ∉ s₁ :=
  Set.ssubset_iff_of_subset h

theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : ∃ (x : _)(_ : x ∈ s₂), x ∉ s₁ :=
  Set.exists_of_ssubset h

/-! ### Nonempty -/


/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Finset α) : Prop :=
  ∃ x : α, x ∈ s

@[simp, normCast]
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.nonempty :=
  Iff.rfl

@[simp]
theorem nonempty_coe_sort (s : Finset α) : Nonempty («expr↥ » s) ↔ s.nonempty :=
  nonempty_subtype

alias coe_nonempty ↔ _ Finset.Nonempty.to_set

theorem nonempty.bex {s : Finset α} (h : s.nonempty) : ∃ x : α, x ∈ s :=
  h

theorem nonempty.mono {s t : Finset α} (hst : s ⊆ t) (hs : s.nonempty) : t.nonempty :=
  Set.Nonempty.mono hst hs

theorem nonempty.forall_const {s : Finset α} (h : s.nonempty) {p : Prop} : (∀ x (_ : x ∈ s), p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h x hx => h⟩

/-! ### empty -/


/-- The empty finset -/
protected def Empty : Finset α :=
  ⟨0, nodup_zero⟩

instance  : HasEmptyc (Finset α) :=
  ⟨Finset.empty⟩

instance inhabited_finset : Inhabited (Finset α) :=
  ⟨∅⟩

@[simp]
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl

@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : Finset α) :=
  id

@[simp]
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty :=
  fun ⟨x, hx⟩ => not_mem_empty x hx

@[simp]
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl

theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ≠ ∅ :=
  fun e => not_mem_empty a$ e ▸ h

theorem nonempty.ne_empty {s : Finset α} (h : s.nonempty) : s ≠ ∅ :=
  Exists.elim h$ fun a => ne_empty_of_mem

@[simp]
theorem empty_subset (s : Finset α) : ∅ ⊆ s :=
  zero_subset _

theorem eq_empty_of_forall_not_mem {s : Finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_not_mem H)

theorem eq_empty_iff_forall_not_mem {s : Finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
  ⟨by 
      rintro rfl x <;> exact id,
    fun h => eq_empty_of_forall_not_mem h⟩

@[simp]
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅

theorem subset_empty {s : Finset α} : s ⊆ ∅ ↔ s = ∅ :=
  subset_zero.trans val_eq_zero

@[simp]
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ :=
  fun h =>
    let ⟨x, he, hs⟩ := exists_of_ssubset h 
    he

theorem nonempty_of_ne_empty {s : Finset α} (h : s ≠ ∅) : s.nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_empty {s : Finset α} : s.nonempty ↔ s ≠ ∅ :=
  ⟨nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp]
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.nonempty ↔ s = ∅ :=
  by 
    rw [nonempty_iff_ne_empty]
    exact not_not

theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.nonempty :=
  Classical.by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, normCast]
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ :=
  rfl

@[simp, normCast]
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ :=
  by 
    rw [←coe_empty, coe_inj]

/-- A `finset` for an empty type is empty. -/
theorem eq_empty_of_is_empty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_not_mem isEmptyElim

/-! ### singleton -/


/--
`{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance  : HasSingleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  mem_singleton

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Finset α)) : x = y :=
  mem_singleton.1 h

theorem not_mem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a ≠ b :=
  not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : Finset α) :=
  Or.inl rfl

theorem singleton_injective : injective (singleton : α → Finset α) :=
  fun a b h => mem_singleton.1 (h ▸ mem_singleton_self _)

theorem singleton_inj {a b : α} : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff

@[simp]
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩

@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Finset α) ≠ ∅ :=
  (singleton_nonempty a).ne_empty

@[simp, normCast]
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} :=
  by 
    ext 
    simp 

@[simp, normCast]
theorem coe_eq_singleton {α : Type _} {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} :=
  by 
    rw [←Finset.coe_singleton, Finset.coe_inj]

theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x (_ : x ∈ s), x = a :=
  by 
    split  <;> intro t 
    rw [t]
    refine' ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
    ext 
    rw [Finset.mem_singleton]
    refine' ⟨t.right _, fun r => r.symm ▸ t.left⟩

theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} : s = {a} ↔ s.nonempty ∧ ∀ x (_ : x ∈ s), x = a :=
  by 
    split 
    ·
      intro h 
      subst h 
      simp 
    ·
      rintro ⟨hne, h_uniq⟩
      rw [eq_singleton_iff_unique_mem]
      refine' ⟨_, h_uniq⟩
      rw [←h_uniq hne.some hne.some_spec]
      apply hne.some_spec

theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃!a, a ∈ s :=
  by 
    simp only [eq_singleton_iff_unique_mem, ExistsUnique]

theorem singleton_subset_set_iff {s : Set α} {a : α} : «expr↑ » ({a} : Finset α) ⊆ s ↔ a ∈ s :=
  by 
    rw [coe_singleton, Set.singleton_subset_iff]

@[simp]
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff

@[simp]
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} :=
  by 
    split 
    ·
      intro hs 
      apply Or.imp_rightₓ _ s.eq_empty_or_nonempty 
      rintro ⟨t, ht⟩
      apply subset.antisymm hs 
      rwa [singleton_subset_iff, ←mem_singleton.1 (hs ht)]
    rintro (rfl | rfl)
    ·
      exact empty_subset _ 
    exact subset.refl _

@[simp]
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ :=
  by 
    rw [←coe_ssubset, coe_singleton, Set.ssubset_singleton_iff, coe_eq_empty]

theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/-! ### cons -/


/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint. -/
def cons {α} (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, Multiset.nodup_cons.2 ⟨h, s.2⟩⟩

@[simp]
theorem mem_cons {a s h b} : b ∈ @cons α a s h ↔ b = a ∨ b ∈ s :=
  by 
    rcases s with ⟨⟨s⟩⟩ <;> apply List.mem_cons_iffₓ

@[simp]
theorem cons_val {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl

@[simp]
theorem mk_cons {a : α} {s : Multiset α} (h : (a ::ₘ s).Nodup) :
  (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (Multiset.nodup_cons.1 h).2⟩ (Multiset.nodup_cons.1 h).1 :=
  rfl

@[simp]
theorem nonempty_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 (Or.inl rfl)⟩

@[simp]
theorem nonempty_mk_coe : ∀ {l : List α} {hl}, (⟨«expr↑ » l, hl⟩ : Finset α).Nonempty ↔ l ≠ []
| [], hl =>
  by 
    simp 
| a :: l, hl =>
  by 
    simp [←Multiset.cons_coe]

@[simp]
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a s :=
  by 
    ext 
    simp 

@[simp]
theorem cons_subset_cons {a s hs t ht} : @cons α a s hs ⊆ cons a t ht ↔ s ⊆ t :=
  by 
    rwa [←coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]

/-! ### disjoint union -/


/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disj_union {α} (s t : Finset α) (h : ∀ a (_ : a ∈ s), a ∉ t) : Finset α :=
  ⟨s.1+t.1, Multiset.nodup_add.2 ⟨s.2, t.2, h⟩⟩

@[simp]
theorem mem_disj_union {α s t h a} : a ∈ @disj_union α s t h ↔ a ∈ s ∨ a ∈ t :=
  by 
    rcases s with ⟨⟨s⟩⟩ <;> rcases t with ⟨⟨t⟩⟩ <;> apply List.mem_appendₓ

/-! ### insert -/


section DecidableEq

variable[DecidableEq α]

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance  : HasInsert α (Finset α) :=
  ⟨fun a s => ⟨_, nodup_ndinsert a s.2⟩⟩

theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, nodup_ndinsert a s.2⟩ :=
  rfl

@[simp]
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl

theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = erase_dup (a ::ₘ s.1) :=
  by 
    rw [erase_dup_cons, erase_dup_eq_self] <;> rfl

theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 :=
  by 
    rw [insert_val, ndinsert_of_not_mem h]

@[simp]
theorem mem_insert {a b : α} {s : Finset α} : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert

theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1

theorem mem_insert_of_mem {a b : α} {s : Finset α} (h : a ∈ s) : a ∈ insert b s :=
  mem_ndinsert_of_mem h

theorem mem_of_mem_insert_of_ne {a b : α} {s : Finset α} (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  (mem_insert.1 h).resolve_left

@[simp]
theorem cons_eq_insert {α} [DecidableEq α] a s h : @cons α a s h = insert a s :=
  ext$
    fun a =>
      by 
        simp 

@[simp, normCast]
theorem coe_insert (a : α) (s : Finset α) : «expr↑ » (insert a s) = (insert a s : Set α) :=
  Set.ext$
    fun x =>
      by 
        simp only [mem_coe, mem_insert, Set.mem_insert_iff]

theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) :=
  by 
    simp 

instance  : IsLawfulSingleton α (Finset α) :=
  ⟨fun a =>
      by 
        ext 
        simp ⟩

@[simp]
theorem insert_eq_of_mem {a : α} {s : Finset α} (h : a ∈ s) : insert a s = s :=
  eq_of_veq$ ndinsert_of_mem h

@[simp]
theorem insert_singleton_self_eq (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem$ mem_singleton_self _

theorem insert.comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  ext$
    fun x =>
      by 
        simp only [mem_insert, Or.left_comm]

theorem insert_singleton_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  by 
    ext 
    simp [Or.comm]

@[simp]
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s :=
  ext$
    fun x =>
      by 
        simp only [mem_insert, or.assoc.symm, or_selfₓ]

@[simp]
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩

@[simp]
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s ≠ ∅ :=
  (insert_nonempty a s).ne_empty

section 

/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/


instance  {α : Type u} [DecidableEq α] (i : α) (s : Finset α) : Nonempty.{u + 1} ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

end 

theorem ne_insert_of_not_mem (s t : Finset α) {a : α} (h : a ∉ s) : s ≠ insert a t :=
  by 
    contrapose! h 
    simp [h]

theorem insert_subset {a : α} {s t : Finset α} : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  by 
    simp only [subset_iff, mem_insert, forall_eq, or_imp_distrib, forall_and_distrib]

theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s :=
  fun b => mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
  insert_subset.2 ⟨mem_insert_self _ _, subset.trans h (subset_insert _ _)⟩

theorem ssubset_iff {s t : Finset α} : s ⊂ t ↔ ∃ (a : _)(_ : a ∉ s), insert a s ⊆ t :=
  by 
    exactModCast @Set.ssubset_iff_insert α s t

theorem ssubset_insert {s : Finset α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, subset.refl _⟩

@[elab_as_eliminator]
theorem cons_induction {α : Type _} {p : Finset α → Prop} (h₁ : p ∅)
  (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
| ⟨s, nd⟩ =>
  Multiset.induction_on s (fun _ => h₁)
    (fun a s IH nd =>
      by 
        cases' nodup_cons.1 nd with m nd' 
        rw [←(eq_of_veq _ : cons a (Finset.mk s _) m = ⟨a ::ₘ s, nd⟩)]
        ·
          exact
            h₂
              (by 
                exact m)
              (IH nd')
        ·
          rw [cons_val])
    nd

@[elab_as_eliminator]
theorem cons_induction_on {α : Type _} {p : Finset α → Prop} (s : Finset α) (h₁ : p ∅)
  (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
  cons_induction h₁ h₂ s

@[elab_as_eliminator]
protected theorem induction {α : Type _} {p : Finset α → Prop} [DecidableEq α] (h₁ : p ∅)
  (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
  cons_induction h₁$ fun a s ha => (s.cons_eq_insert a ha).symm ▸ h₂ ha

/--
To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_eliminator]
protected theorem induction_on {α : Type _} {p : Finset α → Prop} [DecidableEq α] (s : Finset α) (h₁ : p ∅)
  (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
  Finset.induction h₁ h₂ s

/--
To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
@[elab_as_eliminator]
theorem induction_on' {α : Type _} {p : Finset α → Prop} [DecidableEq α] (S : Finset α) (h₁ : p ∅)
  (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
  @Finset.induction_on α (fun T => T ⊆ S → p T) _ S (fun _ => h₁)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset.1 hs 
      h₂ hS sS has (hqs sS))
    (Finset.Subset.refl S)

/-- To prove a proposition about a nonempty `s : finset α`, it suffices to show it holds for all
singletons and that if it holds for `t : finset α`, then it also holds for the `finset` obtained by
inserting an element in `t`. -/
@[elab_as_eliminator]
theorem nonempty.cons_induction {α : Type _} {s : Finset α} (hs : s.nonempty) {p : Finset α → Prop} (h₀ : ∀ a, p {a})
  (h₁ : ∀ ⦃a⦄ s (h : a ∉ s), p s → p (Finset.cons a s h)) : p s :=
  by 
    induction' s using Finset.cons_induction with a t ha h
    ·
      exact (not_nonempty_empty hs).elim 
    obtain rfl | ht := t.eq_empty_or_nonempty
    ·
      exact h₀ a
    ·
      exact h₁ t ha (h ht)

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtype_insert_equiv_option
{t : finset α}
{x : α}
(h : «expr ∉ »(x, t)) : «expr ≃ »({i // «expr ∈ »(i, insert x t)}, option {i // «expr ∈ »(i, t)}) :=
begin
  refine [expr { to_fun := λ
     y, if h : «expr = »(«expr↑ »(y), x) then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩,
     inv_fun := λ y, «expr $ »(y.elim ⟨x, mem_insert_self _ _⟩, λ z, ⟨z, mem_insert_of_mem z.2⟩),
     .. }],
  { intro [ident y],
    by_cases [expr h, ":", expr «expr = »(«expr↑ »(y), x)],
    simp [] [] ["only"] ["[", expr subtype.ext_iff, ",", expr h, ",", expr option.elim, ",", expr dif_pos, ",", expr subtype.coe_mk, "]"] [] [],
    simp [] [] ["only"] ["[", expr h, ",", expr option.elim, ",", expr dif_neg, ",", expr not_false_iff, ",", expr subtype.coe_eta, ",", expr subtype.coe_mk, "]"] [] [] },
  { rintro ["(", "_", "|", ident y, ")"],
    simp [] [] ["only"] ["[", expr option.elim, ",", expr dif_pos, ",", expr subtype.coe_mk, "]"] [] [],
    have [] [":", expr «expr ≠ »(«expr↑ »(y), x)] [],
    { rintro ["⟨", "⟩"],
      exact [expr h y.2] },
    simp [] [] ["only"] ["[", expr this, ",", expr option.elim, ",", expr subtype.eta, ",", expr dif_neg, ",", expr not_false_iff, ",", expr subtype.coe_eta, ",", expr subtype.coe_mk, "]"] [] [] }
end

/-! ### union -/


/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance  : HasUnion (Finset α) :=
  ⟨fun s₁ s₂ => ⟨_, nodup_ndunion s₁.1 s₂.2⟩⟩

theorem union_val_nd (s₁ s₂ : Finset α) : (s₁ ∪ s₂).1 = ndunion s₁.1 s₂.1 :=
  rfl

@[simp]
theorem union_val (s₁ s₂ : Finset α) : (s₁ ∪ s₂).1 = s₁.1 ∪ s₂.1 :=
  ndunion_eq_union s₁.2

@[simp]
theorem mem_union {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_ndunion

@[simp]
theorem disj_union_eq_union {α} [DecidableEq α] s t h : @disj_union α s t h = s ∪ t :=
  ext$
    fun a =>
      by 
        simp 

theorem mem_union_left {a : α} {s₁ : Finset α} (s₂ : Finset α) (h : a ∈ s₁) : a ∈ s₁ ∪ s₂ :=
  mem_union.2$ Or.inl h

theorem mem_union_right {a : α} {s₂ : Finset α} (s₁ : Finset α) (h : a ∈ s₂) : a ∈ s₁ ∪ s₂ :=
  mem_union.2$ Or.inr h

theorem forall_mem_union {s₁ s₂ : Finset α} {p : α → Prop} :
  (∀ ab (_ : ab ∈ s₁ ∪ s₂), p ab) ↔ (∀ a (_ : a ∈ s₁), p a) ∧ ∀ b (_ : b ∈ s₂), p b :=
  ⟨fun h => ⟨fun a => h a ∘ mem_union_left _, fun b => h b ∘ mem_union_right _⟩,
    fun h ab hab => (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩

theorem not_mem_union {a : α} {s₁ s₂ : Finset α} : a ∉ s₁ ∪ s₂ ↔ a ∉ s₁ ∧ a ∉ s₂ :=
  by 
    rw [mem_union, not_or_distrib]

@[simp, normCast]
theorem coe_union (s₁ s₂ : Finset α) : «expr↑ » (s₁ ∪ s₂) = (s₁ ∪ s₂ : Set α) :=
  Set.ext$ fun x => mem_union

theorem union_subset {s₁ s₂ s₃ : Finset α} (h₁ : s₁ ⊆ s₃) (h₂ : s₂ ⊆ s₃) : s₁ ∪ s₂ ⊆ s₃ :=
  val_le_iff.1 (ndunion_le.2 ⟨h₁, val_le_iff.2 h₂⟩)

theorem subset_union_left (s₁ s₂ : Finset α) : s₁ ⊆ s₁ ∪ s₂ :=
  fun x => mem_union_left _

theorem subset_union_right (s₁ s₂ : Finset α) : s₂ ⊆ s₁ ∪ s₂ :=
  fun x => mem_union_right _

theorem union_subset_union {s₁ t₁ s₂ t₂ : Finset α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∪ s₂ ⊆ t₁ ∪ t₂ :=
  by 
    intro x hx 
    rw [Finset.mem_union] at hx⊢
    tauto

theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
  ext$
    fun x =>
      by 
        simp only [mem_union, or_comm]

instance  : IsCommutative (Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  ext$
    fun x =>
      by 
        simp only [mem_union, or_assoc]

instance  : IsAssociative (Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

@[simp]
theorem union_idempotent (s : Finset α) : s ∪ s = s :=
  ext$ fun _ => mem_union.trans$ or_selfₓ _

instance  : IsIdempotent (Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩

theorem union_subset_left {s₁ s₂ s₃ : Finset α} (h : s₁ ∪ s₂ ⊆ s₃) : s₁ ⊆ s₃ :=
  subset.trans (subset_union_left _ _) h

theorem union_subset_right {s₁ s₂ s₃ : Finset α} (h : s₁ ∪ s₂ ⊆ s₃) : s₂ ⊆ s₃ :=
  subset.trans (subset_union_right _ _) h

theorem union_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext$
    fun _ =>
      by 
        simp only [mem_union, Or.left_comm]

theorem union_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext$
    fun x =>
      by 
        simp only [mem_union, or_assoc, or_comm (x ∈ s₂)]

theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s

@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext$ fun x => mem_union.trans$ or_falseₓ _

@[simp]
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext$ fun x => mem_union.trans$ false_orₓ _

theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl

@[simp]
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) :=
  by 
    simp only [insert_eq, union_assoc]

@[simp]
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) :=
  by 
    simp only [insert_eq, union_left_comm]

theorem insert_union_distrib (a : α) (s t : Finset α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
  by 
    simp only [insert_union, union_insert, insert_idem]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem union_eq_left_iff_subset {s t : finset α} : «expr ↔ »(«expr = »(«expr ∪ »(s, t), s), «expr ⊆ »(t, s)) :=
begin
  split,
  { assume [binders (h)],
    have [] [":", expr «expr ⊆ »(t, «expr ∪ »(s, t))] [":=", expr subset_union_right _ _],
    rwa [expr h] ["at", ident this] },
  { assume [binders (h)],
    exact [expr subset.antisymm (union_subset (subset.refl _) h) (subset_union_left _ _)] }
end

@[simp]
theorem left_eq_union_iff_subset {s t : Finset α} : s = s ∪ t ↔ t ⊆ s :=
  by 
    rw [←union_eq_left_iff_subset, eq_comm]

@[simp]
theorem union_eq_right_iff_subset {s t : Finset α} : t ∪ s = s ↔ t ⊆ s :=
  by 
    rw [union_comm, union_eq_left_iff_subset]

@[simp]
theorem right_eq_union_iff_subset {s t : Finset α} : s = t ∪ s ↔ t ⊆ s :=
  by 
    rw [←union_eq_right_iff_subset, eq_comm]

/--
To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union (P : Finset α → Finset α → Prop) (symm : ∀ {a b}, P a b → P b a) (empty_right : ∀ {a}, P a ∅)
  (singletons : ∀ {a b}, P {a} {b}) (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) : ∀ a b, P a b :=
  by 
    intro a b 
    refine' Finset.induction_on b empty_right fun x s xs hi => symm _ 
    rw [Finset.insert_eq]
    apply union_of _ (symm hi)
    refine' Finset.induction_on a empty_right fun a t ta hi => symm _ 
    rw [Finset.insert_eq]
    exact union_of singletons (symm hi)

theorem exists_mem_subset_of_subset_bUnion_of_directed_on {α ι : Type _} {f : ι → Set α} {c : Set ι} {a : ι}
  (hac : a ∈ c) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α}
  (hs : (s : Set α) ⊆ ⋃(i : _)(_ : i ∈ c), f i) : ∃ (i : _)(_ : i ∈ c), (s : Set α) ⊆ f i :=
  by 
    classical 
    revert hs 
    apply s.induction_on
    ·
      intros 
      use a, hac 
      simp 
    ·
      intro b t hbt htc hbtc 
      obtain ⟨i : ι, hic : i ∈ c, hti : (t : Set α) ⊆ f i⟩ := htc (Set.Subset.trans (t.subset_insert b) hbtc)
      obtain ⟨j, hjc, hbj⟩ : ∃ (j : _)(_ : j ∈ c), b ∈ f j
      ·
        simpa [Set.mem_bUnion_iff] using hbtc (t.mem_insert_self b)
      rcases hc j hjc i hic with ⟨k, hkc, hk, hk'⟩
      use k, hkc 
      rw [coe_insert, Set.insert_subset]
      exact ⟨hk hbj, trans hti hk'⟩

/-! ### inter -/


/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance  : HasInter (Finset α) :=
  ⟨fun s₁ s₂ => ⟨_, nodup_ndinter s₂.1 s₁.2⟩⟩

theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl

@[simp]
theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
  ndinter_eq_inter s₁.2

@[simp]
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  and_imp.1 mem_inter.2

theorem inter_subset_left (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₁ :=
  fun a => mem_of_mem_inter_left

theorem inter_subset_right (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₂ :=
  fun a => mem_of_mem_inter_right

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem subset_inter {s₁ s₂ s₃ : finset α} : «expr ⊆ »(s₁, s₂) → «expr ⊆ »(s₁, s₃) → «expr ⊆ »(s₁, «expr ∩ »(s₂, s₃)) :=
by simp [] [] ["only"] ["[", expr subset_iff, ",", expr mem_inter, "]"] [] [] { contextual := tt }; intros []; split; trivial

@[simp, normCast]
theorem coe_inter (s₁ s₂ : Finset α) : «expr↑ » (s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext$ fun _ => mem_inter

@[simp]
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s :=
  by 
    rw [←coe_inj, coe_inter, coe_union, Set.union_inter_cancel_left]

@[simp]
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t :=
  by 
    rw [←coe_inj, coe_inter, coe_union, Set.union_inter_cancel_right]

theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
  ext$
    fun _ =>
      by 
        simp only [mem_inter, and_comm]

@[simp]
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
  ext$
    fun _ =>
      by 
        simp only [mem_inter, and_assoc]

theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext$
    fun _ =>
      by 
        simp only [mem_inter, And.left_comm]

theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext$
    fun _ =>
      by 
        simp only [mem_inter, And.right_comm]

@[simp]
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext$ fun _ => mem_inter.trans$ and_selfₓ _

@[simp]
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext$ fun _ => mem_inter.trans$ and_falseₓ _

@[simp]
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext$ fun _ => mem_inter.trans$ false_andₓ _

@[simp]
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s :=
  by 
    rw [inter_comm, union_inter_cancel_right]

@[simp]
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) : insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext$
    fun x =>
      have  : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ :=
        or_iff_right_of_imp$
          by 
            rintro rfl <;> exact h 
      by 
        simp only [mem_inter, mem_insert, or_and_distrib_left, this]

@[simp]
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) : s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
  by 
    rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]
theorem insert_inter_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) : insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext$
    fun x =>
      have  : ¬(x = a ∧ x ∈ s₂) :=
        by 
          rintro ⟨rfl, H⟩ <;> exact h H 
      by 
        simp only [mem_inter, mem_insert, or_and_distrib_right, this, false_orₓ]

@[simp]
theorem inter_insert_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) : s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
  by 
    rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp]
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅by 
    rw [insert_inter_of_mem H, empty_inter]

@[simp]
theorem singleton_inter_of_not_mem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_not_mem$
    by 
      simp only [mem_inter, mem_singleton] <;> rintro x ⟨rfl, h⟩ <;> exact H h

@[simp]
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} :=
  by 
    rw [inter_comm, singleton_inter_of_mem h]

@[simp]
theorem inter_singleton_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ :=
  by 
    rw [inter_comm, singleton_inter_of_not_mem h]

@[mono]
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
  by 
    intro a a_in 
    rw [Finset.mem_inter] at a_in⊢
    exact ⟨h a_in.1, h' a_in.2⟩

theorem inter_subset_inter_right {x y s : Finset α} (h : x ⊆ y) : x ∩ s ⊆ y ∩ s :=
  Finset.inter_subset_inter h (Finset.Subset.refl _)

theorem inter_subset_inter_left {x y s : Finset α} (h : x ⊆ y) : s ∩ x ⊆ s ∩ y :=
  Finset.inter_subset_inter (Finset.Subset.refl _) h

/-! ### lattice laws -/


instance  : Lattice (Finset α) :=
  { Finset.partialOrder with sup := · ∪ ·, sup_le := fun a b c => union_subset, le_sup_left := subset_union_left,
    le_sup_right := subset_union_right, inf := · ∩ ·, le_inf := fun a b c => subset_inter,
    inf_le_left := inter_subset_left, inf_le_right := inter_subset_right }

@[simp]
theorem sup_eq_union : (·⊔· : Finset α → Finset α → Finset α) = · ∪ · :=
  rfl

@[simp]
theorem inf_eq_inter : (·⊓· : Finset α → Finset α → Finset α) = · ∩ · :=
  rfl

instance  {α : Type u} : OrderBot (Finset α) :=
  { bot := ∅, bot_le := empty_subset }

@[simp]
theorem bot_eq_empty {α : Type u} : (⊥ : Finset α) = ∅ :=
  rfl

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : distrib_lattice (finset α) :=
{ le_sup_inf := assume
  a
  b
  c, show «expr ⊆ »(«expr ∩ »(«expr ∪ »(a, b), «expr ∪ »(a, c)), «expr ∪ »(a, «expr ∩ »(b, c))), by simp [] [] ["only"] ["[", expr subset_iff, ",", expr mem_inter, ",", expr mem_union, ",", expr and_imp, ",", expr or_imp_distrib, "]"] [] [] { contextual := tt }; simp [] [] ["only"] ["[", expr true_or, ",", expr imp_true_iff, ",", expr true_and, ",", expr or_true, "]"] [] [],
  ..finset.lattice }

@[simp]
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t :=
  sup_left_idem

@[simp]
theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t :=
  sup_right_idem

@[simp]
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t :=
  inf_left_idem

@[simp]
theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t :=
  inf_right_idem

theorem inter_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left

theorem inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right

theorem union_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left

theorem union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right

theorem union_eq_empty_iff (A B : Finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ :=
  sup_eq_bot_iff

theorem union_subset_iff {s₁ s₂ s₃ : Finset α} : s₁ ∪ s₂ ⊆ s₃ ↔ s₁ ⊆ s₃ ∧ s₂ ⊆ s₃ :=
  (sup_le_iff : s₁⊔s₂ ≤ s₃ ↔ s₁ ≤ s₃ ∧ s₂ ≤ s₃)

theorem subset_inter_iff {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ ∩ s₃ ↔ s₁ ⊆ s₂ ∧ s₁ ⊆ s₃ :=
  (le_inf_iff : s₁ ≤ s₂⊓s₃ ↔ s₁ ≤ s₂ ∧ s₁ ≤ s₃)

theorem inter_eq_left_iff_subset (s t : Finset α) : s ∩ t = s ↔ s ⊆ t :=
  (inf_eq_left : s⊓t = s ↔ s ≤ t)

theorem inter_eq_right_iff_subset (s t : Finset α) : t ∩ s = s ↔ s ⊆ t :=
  (inf_eq_right : t⊓s = s ↔ s ≤ t)

/-! ### erase -/


/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, nodup_erase_of_nodup a s.2⟩

@[simp]
theorem erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.erase a :=
  rfl

@[simp]
theorem mem_erase {a b : α} {s : Finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
  mem_erase_iff_of_nodup s.2

theorem not_mem_erase (a : α) (s : Finset α) : a ∉ erase s a :=
  mem_erase_of_nodup s.2

@[nolint simp_nf, simp]
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl

@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ :=
  by 
    ext x 
    rw [mem_erase, mem_singleton, not_and_selfₓ]
    rfl

theorem ne_of_mem_erase {a b : α} {s : Finset α} : b ∈ erase s a → b ≠ a :=
  by 
    simp only [mem_erase] <;> exact And.left

theorem mem_of_mem_erase {a b : α} {s : Finset α} : b ∈ erase s a → b ∈ s :=
  mem_of_mem_erase

theorem mem_erase_of_ne_of_mem {a b : α} {s : Finset α} : a ≠ b → a ∈ s → a ∈ erase s b :=
  by 
    simp only [mem_erase] <;> exact And.intro

/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
theorem eq_of_mem_of_not_mem_erase {a b : α} {s : Finset α} (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a :=
  by 
    rw [mem_erase, not_and] at hsa 
    exact not_imp_not.mp hsa hs

theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : erase (insert a s) a = s :=
  ext$
    fun x =>
      by 
        simp only [mem_erase, mem_insert, and_or_distrib_left, not_and_selfₓ, false_orₓ] <;>
          apply and_iff_right_of_imp <;> rintro H rfl <;> exact h H

theorem insert_erase {a : α} {s : Finset α} (h : a ∈ s) : insert a (erase s a) = s :=
  ext$
    fun x =>
      by 
        simp only [mem_insert, mem_erase, or_and_distrib_left, dec_em, true_andₓ] <;>
          apply or_iff_right_of_imp <;> rintro rfl <;> exact h

theorem erase_subset_erase (a : α) {s t : Finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
  val_le_iff.1$ erase_le_erase _$ val_le_iff.2 h

theorem erase_subset (a : α) (s : Finset α) : erase s a ⊆ s :=
  erase_subset _ _

@[simp, normCast]
theorem coe_erase (a : α) (s : Finset α) : «expr↑ » (erase s a) = (s \ {a} : Set α) :=
  Set.ext$
    fun _ =>
      mem_erase.trans$
        by 
          rw [and_comm, Set.mem_diff, Set.mem_singleton_iff] <;> rfl

theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s :=
  calc s.erase a ⊂ insert a (s.erase a) := ssubset_insert$ not_mem_erase _ _ 
    _ = _ := insert_erase h
    

@[simp]
theorem erase_eq_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s :=
  eq_of_veq$ erase_of_not_mem h

theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a :=
  by 
    simp 

theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a :=
  by 
    ext x 
    simp only [mem_erase, ←and_assoc]
    rw [and_comm (x ≠ a)]

theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ erase s a ⊆ t :=
  by 
    simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp] <;>
      exact forall_congrₓ fun x => forall_swap

theorem erase_insert_subset (a : α) (s : Finset α) : erase (insert a s) a ⊆ s :=
  subset_insert_iff.1$ subset.refl _

theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (erase s a) :=
  subset_insert_iff.2$ subset.refl _

theorem erase_inj {x y : α} (s : Finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y :=
  by 
    refine' ⟨fun h => _, congr_argₓ _⟩
    rw [eq_of_mem_of_not_mem_erase hx]
    rw [←h]
    simp 

theorem erase_inj_on (s : Finset α) : Set.InjOn s.erase s :=
  fun _ _ _ _ => (erase_inj s ‹_›).mp

/-! ### sdiff -/


/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance  : HasSdiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le tsub_le_self s₁.2⟩⟩

@[simp]
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl

@[simp]
theorem mem_sdiff {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ \ s₂ ↔ a ∈ s₁ ∧ a ∉ s₂ :=
  mem_sub_of_nodup s₁.2

@[simp]
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
  eq_empty_of_forall_not_mem$
    by 
      simp only [mem_inter, mem_sdiff] <;> rintro x ⟨h, _, hn⟩ <;> exact hn h

instance  : GeneralizedBooleanAlgebra (Finset α) :=
  { Finset.hasSdiff, Finset.distribLattice, Finset.orderBot with
    sup_inf_sdiff :=
      fun x y =>
        by 
          simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union, mem_inter]
          tauto,
    inf_inf_sdiff :=
      fun x y =>
        by 
          simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc, false_iffₓ, inf_eq_inter, not_mem_empty]
          tauto }

theorem not_mem_sdiff_of_mem_right {a : α} {s t : Finset α} (h : a ∈ t) : a ∉ s \ t :=
  by 
    simp only [mem_sdiff, h, not_true, not_false_iff, and_falseₓ]

theorem union_sdiff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ∪ s₂ \ s₁ = s₂ :=
  sup_sdiff_cancel_right h

theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ :=
  (union_comm _ _).trans (union_sdiff_of_subset h)

theorem inter_sdiff (s t u : Finset α) : s ∩ (t \ u) = s ∩ t \ u :=
  by 
    ext x 
    simp [and_assoc]

@[simp]
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left

@[simp]
theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  sdiff_self

theorem sdiff_inter_distrib_right (s₁ s₂ s₃ : Finset α) : s₁ \ (s₂ ∩ s₃) = s₁ \ s₂ ∪ s₁ \ s₃ :=
  sdiff_inf

@[simp]
theorem sdiff_inter_self_left (s₁ s₂ : Finset α) : s₁ \ (s₁ ∩ s₂) = s₁ \ s₂ :=
  sdiff_inf_self_left

@[simp]
theorem sdiff_inter_self_right (s₁ s₂ : Finset α) : s₁ \ (s₂ ∩ s₁) = s₁ \ s₂ :=
  sdiff_inf_self_right

@[simp]
theorem sdiff_empty {s₁ : Finset α} : s₁ \ ∅ = s₁ :=
  sdiff_bot

@[mono]
theorem sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Finset α} (h₁ : t₁ ⊆ t₂) (h₂ : s₂ ⊆ s₁) : t₁ \ s₁ ⊆ t₂ \ s₂ :=
  sdiff_le_sdiff ‹t₁ ≤ t₂› ‹s₂ ≤ s₁›

@[simp, normCast]
theorem coe_sdiff (s₁ s₂ : Finset α) : «expr↑ » (s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext$ fun _ => mem_sdiff

@[simp]
theorem union_sdiff_self_eq_union {s t : Finset α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right

@[simp]
theorem sdiff_union_self_eq_union {s t : Finset α} : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left

theorem union_sdiff_symm {s t : Finset α} : s ∪ t \ s = t ∪ s \ t :=
  sup_sdiff_symm

theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  by 
    rw [union_comm]
    exact sup_inf_sdiff _ _

@[simp]
theorem sdiff_idem (s t : Finset α) : s \ t \ t = s \ t :=
  sdiff_idem

theorem sdiff_eq_empty_iff_subset {s t : Finset α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

@[simp]
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff

theorem insert_sdiff_of_not_mem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) : insert x s \ t = insert x (s \ t) :=
  by 
    rw [←coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert]
    exact Set.insert_diff_of_not_mem s h

theorem insert_sdiff_of_mem (s : Finset α) {t : Finset α} {x : α} (h : x ∈ t) : insert x s \ t = s \ t :=
  by 
    rw [←coe_inj, coe_sdiff, coe_sdiff, coe_insert]
    exact Set.insert_diff_of_mem s h

@[simp]
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)

theorem sdiff_insert_of_not_mem {s : Finset α} {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t :=
  by 
    refine' subset.antisymm (sdiff_subset_sdiff (subset.refl _) (subset_insert _ _)) fun y hy => _ 
    simp only [mem_sdiff, mem_insert, not_or_distrib] at hy⊢
    exact ⟨hy.1, fun hxy => h$ hxy ▸ hy.1, hy.2⟩

@[simp]
theorem sdiff_subset (s t : Finset α) : s \ t ⊆ s :=
  show s \ t ≤ s from sdiff_le

theorem sdiff_ssubset {s t : Finset α} (h : t ⊆ s) (ht : t.nonempty) : s \ t ⊂ s :=
  sdiff_lt (le_iff_subset.2 h) ht.ne_empty

theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sup_sdiff

theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sdiff_sup

theorem union_sdiff_self (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ singleton a = erase s a :=
  by 
    ext 
    rw [mem_erase, mem_sdiff, mem_singleton]
    tauto

@[simp]
theorem sdiff_singleton_not_mem_eq_self (s : Finset α) {a : α} (ha : a ∉ s) : s \ {a} = s :=
  by 
    simp only [sdiff_singleton_eq_erase, ha, erase_eq_of_not_mem, not_false_iff]

theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self

theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} : s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf

theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

end DecidableEq

/-! ### attach -/


/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨attach s.1, nodup_attach.2 s.2⟩

theorem sizeof_lt_sizeof_of_mem [SizeOf α] {x : α} {s : Finset α} (hx : x ∈ s) : sizeof x < sizeof s :=
  by 
    cases s 
    dsimp [sizeof, SizeOf.sizeof, Finset.sizeof]
    apply lt_add_left 
    exact Multiset.sizeof_lt_sizeof_of_mem hx

@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl

@[simp]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  mem_attach _

@[simp]
theorem attach_empty : attach (∅ : Finset α) = ∅ :=
  rfl

@[simp]
theorem attach_nonempty_iff (s : Finset α) : s.attach.nonempty ↔ s.nonempty :=
  by 
    simp [Finset.Nonempty]

@[simp]
theorem attach_eq_empty_iff (s : Finset α) : s.attach = ∅ ↔ s = ∅ :=
  by 
    simpa [eq_empty_iff_forall_not_mem]

/-! ### piecewise -/


section Piecewise

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type _} {δ : α → Sort _} (s : Finset α) (f g : ∀ i, δ i) [∀ j, Decidable (j ∈ s)] : ∀ i, δ i :=
  fun i => if i ∈ s then f i else g i

variable{δ : α → Sort _}(s : Finset α)(f g : ∀ i, δ i)

@[simp]
theorem piecewise_insert_self [DecidableEq α] {j : α} [∀ i, Decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g j = f j :=
  by 
    simp [piecewise]

@[simp]
theorem piecewise_empty [∀ (i : α), Decidable (i ∈ (∅ : Finset α))] : piecewise ∅ f g = g :=
  by 
    ext i 
    simp [piecewise]

variable[∀ j, Decidable (j ∈ s)]

@[normCast]
theorem piecewise_coe [∀ j, Decidable (j ∈ (s : Set α))] : (s : Set α).piecewise f g = s.piecewise f g :=
  by 
    ext 
    congr

@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  by 
    simp [piecewise, hi]

@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  by 
    simp [piecewise, hi]

theorem piecewise_congr {f f' g g' : ∀ i, δ i} (hf : ∀ i (_ : i ∈ s), f i = f' i) (hg : ∀ i (_ : i ∉ s), g i = g' i) :
  s.piecewise f g = s.piecewise f' g' :=
  funext$ fun i => if_ctx_congr Iff.rfl (hf i) (hg i)

@[simp]
theorem piecewise_insert_of_ne [DecidableEq α] {i j : α} [∀ i, Decidable (i ∈ insert j s)] (h : i ≠ j) :
  (insert j s).piecewise f g i = s.piecewise f g i :=
  by 
    simp [piecewise, h]

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g = update (s.piecewise f g) j (f j) :=
  by 
    classical 
    rw [←piecewise_coe, ←piecewise_coe, ←Set.piecewise_insert, ←coe_insert j s]
    congr

theorem piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) : p (s.piecewise f g i) :=
  by 
    byCases' hi : i ∈ s <;> simpa [hi]

theorem piecewise_mem_set_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ Set.Pi t t')
  (hg : g ∈ Set.Pi t t') : s.piecewise f g ∈ Set.Pi t t' :=
  by 
    classical 
    rw [←piecewise_coe]
    exact Set.piecewise_mem_pi («expr↑ » s) hf hg

theorem piecewise_singleton [DecidableEq α] (i : α) : piecewise {i} f g = update g i (f i) :=
  by 
    rw [←insert_emptyc_eq, piecewise_insert, piecewise_empty]

theorem piecewise_piecewise_of_subset_left {s t : Finset α} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
  (h : s ⊆ t) (f₁ f₂ g : ∀ a, δ a) : s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl

@[simp]
theorem piecewise_idem_left (f₁ f₂ g : ∀ a, δ a) : s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (subset.refl _) _ _ _

theorem piecewise_piecewise_of_subset_right {s t : Finset α} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
  (h : t ⊆ s) (f g₁ g₂ : ∀ a, δ a) : s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun i hi => t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi)

@[simp]
theorem piecewise_idem_right (f g₁ g₂ : ∀ a, δ a) : s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (subset.refl _) f g₁ g₂

theorem update_eq_piecewise {β : Type _} [DecidableEq α] (f : α → β) (i : α) (v : β) :
  update f i v = piecewise (singleton i) (fun j => v) f :=
  (piecewise_singleton _ _ _).symm

theorem update_piecewise [DecidableEq α] (i : α) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) :=
  by 
    ext j 
    rcases em (j = i) with (rfl | hj) <;> byCases' hs : j ∈ s <;> simp 

theorem update_piecewise_of_mem [DecidableEq α] {i : α} (hi : i ∈ s) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise (update f i v) g :=
  by 
    rw [update_piecewise]
    refine' s.piecewise_congr (fun _ _ => rfl) fun j hj => update_noteq _ _ _ 
    exact fun h => hj (h.symm ▸ hi)

theorem update_piecewise_of_not_mem [DecidableEq α] {i : α} (hi : i ∉ s) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise f (update g i v) :=
  by 
    rw [update_piecewise]
    refine' s.piecewise_congr (fun j hj => update_noteq _ _ _) fun _ _ => rfl 
    exact fun h => hi (h ▸ hj)

theorem piecewise_le_of_le_of_le {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g h : ∀ i, δ i} (Hf : f ≤ h) (Hg : g ≤ h) :
  s.piecewise f g ≤ h :=
  fun x => piecewise_cases s f g (· ≤ h x) (Hf x) (Hg x)

theorem le_piecewise_of_le_of_le {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g h : ∀ i, δ i} (Hf : h ≤ f) (Hg : h ≤ g) :
  h ≤ s.piecewise f g :=
  fun x => piecewise_cases s f g (fun y => h x ≤ y) (Hf x) (Hg x)

theorem piecewise_le_piecewise' {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g f' g' : ∀ i, δ i}
  (Hf : ∀ x (_ : x ∈ s), f x ≤ f' x) (Hg : ∀ x (_ : x ∉ s), g x ≤ g' x) : s.piecewise f g ≤ s.piecewise f' g' :=
  fun x =>
    by 
      byCases' hx : x ∈ s <;> simp [hx]

theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g f' g' : ∀ i, δ i} (Hf : f ≤ f')
  (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => Hf x) fun x _ => Hg x

theorem piecewise_mem_Icc_of_mem_of_mem {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f f₁ g g₁ : ∀ i, δ i}
  (hf : f ∈ Set.Icc f₁ g₁) (hg : g ∈ Set.Icc f₁ g₁) : s.piecewise f g ∈ Set.Icc f₁ g₁ :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

theorem piecewise_mem_Icc {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g : ∀ i, δ i} (h : f ≤ g) :
  s.piecewise f g ∈ Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)

theorem piecewise_mem_Icc' {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g : ∀ i, δ i} (h : g ≤ f) :
  s.piecewise f g ∈ Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)

end Piecewise

section DecidablePiExists

variable{s : Finset α}

instance decidable_dforall_finset {p : ∀ a (_ : a ∈ s), Prop} [hp : ∀ a (h : a ∈ s), Decidable (p a h)] :
  Decidable (∀ a (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidable_eq_pi_finset {β : α → Type _} [h : ∀ a, DecidableEq (β a)] : DecidableEq (∀ a (_ : a ∈ s), β a) :=
  Multiset.decidableEqPiMultiset

instance decidable_dexists_finset {p : ∀ a (_ : a ∈ s), Prop} [hp : ∀ a (h : a ∈ s), Decidable (p a h)] :
  Decidable (∃ (a : _)(h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset

end DecidablePiExists

/-! ### filter -/


section Filter

variable(p q : α → Prop)[DecidablePred p][DecidablePred q]

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : Finset α) : Finset α :=
  ⟨_, nodup_filter p s.2⟩

@[simp]
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl

@[simp]
theorem filter_subset (s : Finset α) : s.filter p ⊆ s :=
  filter_subset _ _

variable{p}

@[simp]
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  mem_filter

theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ ∃ (x : _)(_ : x ∈ s), ¬p x :=
  ⟨fun h =>
      let ⟨x, hs, hp⟩ := Set.exists_of_ssubset h
      ⟨x, hs, mt (fun hp => mem_filter.2 ⟨hs, hp⟩) hp⟩,
    fun ⟨x, hs, hp⟩ => ⟨s.filter_subset _, fun h => hp (mem_filter.1 (h hs)).2⟩⟩

variable(p)

theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a :=
  ext$
    fun a =>
      by 
        simp only [mem_filter, and_comm, And.left_comm]

theorem filter_true {s : Finset α} [h : DecidablePred fun _ => True] : @Finset.filter α (fun _ => True) h s = s :=
  by 
    ext <;> simp 

@[simp]
theorem filter_false {h} (s : Finset α) : @filter α (fun a => False) h s = ∅ :=
  ext$
    fun a =>
      by 
        simp only [mem_filter, and_falseₓ] <;> rfl

variable{p q}

/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp]
theorem filter_true_of_mem {s : Finset α} (h : ∀ x (_ : x ∈ s), p x) : s.filter p = s :=
  ext$ fun x => ⟨fun h => (mem_filter.1 h).1, fun hx => mem_filter.2 ⟨hx, h x hx⟩⟩

/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem {s : Finset α} (h : ∀ x (_ : x ∈ s), ¬p x) : s.filter p = ∅ :=
  eq_empty_of_forall_not_mem
    (by 
      simpa)

theorem filter_congr {s : Finset α} (H : ∀ x (_ : x ∈ s), p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq$ filter_congr H

variable(p q)

theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1$ filter_subset _ _

theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p :=
  fun a ha => mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

theorem monotone_filter_left (p : α → Prop) [DecidablePred p] : Monotone (filter p) :=
  fun _ _ => filter_subset_filter p

theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q] (h : p ≤ q) :
  s.filter p ≤ s.filter q :=
  Multiset.subset_of_le (Multiset.monotone_filter_right s.val h)

@[simp, normCast]
theorem coe_filter (s : Finset α) : «expr↑ » (s.filter p) = ({ x∈«expr↑ » s | p x } : Set α) :=
  Set.ext$ fun _ => mem_filter

theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ :=
  by 
    classical 
    ext x 
    simp 
    splitIfs with h <;> byCases' h' : x = a <;> simp [h, h']

variable[DecidableEq α]

theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
  ext$
    fun _ =>
      by 
        simp only [mem_filter, mem_union, or_and_distrib_right]

theorem filter_union_right (s : Finset α) : s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x :=
  ext$
    fun x =>
      by 
        simp only [mem_filter, mem_union, and_or_distrib_left.symm]

theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] : (s.filter fun i => i ∈ t) = s ∩ t :=
  ext$
    fun i =>
      by 
        rw [mem_filter, mem_inter]

theorem filter_inter (s t : Finset α) : filter p s ∩ t = filter p (s ∩ t) :=
  by 
    ext 
    simp only [mem_inter, mem_filter, And.right_comm]

theorem inter_filter (s t : Finset α) : s ∩ filter p t = filter p (s ∩ t) :=
  by 
    rw [inter_comm, filter_inter, inter_comm]

theorem filter_insert (a : α) (s : Finset α) :
  filter p (insert a s) = if p a then insert a (filter p s) else filter p s :=
  by 
    ext x 
    simp 
    splitIfs with h <;> byCases' h' : x = a <;> simp [h, h']

theorem filter_erase (a : α) (s : Finset α) : filter p (erase s a) = erase (filter p s) a :=
  by 
    ext x 
    simp only [and_assoc, mem_filter, iff_selfₓ, mem_erase]

theorem filter_or [DecidablePred fun a => p a ∨ q a] (s : Finset α) :
  (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q :=
  ext$
    fun _ =>
      by 
        simp only [mem_filter, mem_union, and_or_distrib_left]

theorem filter_and [DecidablePred fun a => p a ∧ q a] (s : Finset α) :
  (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q :=
  ext$
    fun _ =>
      by 
        simp only [mem_filter, mem_inter, and_comm, And.left_comm, and_selfₓ]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem filter_not
[decidable_pred (λ a, «expr¬ »(p a))]
(s : finset α) : «expr = »(s.filter (λ a, «expr¬ »(p a)), «expr \ »(s, s.filter p)) :=
«expr $ »(ext, by simpa [] [] ["only"] ["[", expr mem_filter, ",", expr mem_sdiff, ",", expr and_comm, ",", expr not_and, "]"] [] ["using", expr λ
  a, «expr $ »(and_congr_right, λ h : «expr ∈ »(a, s), (imp_iff_right h).symm.trans imp_not_comm)])

theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = filter (· ∉ s₂) s₁ :=
  ext$
    fun _ =>
      by 
        simp only [mem_sdiff, mem_filter]

theorem sdiff_eq_self (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ :=
  by 
    simp [subset.antisymm_iff]
    split  <;> intro h
    ·
      trans' s₁ \ s₂ ∩ s₂ 
      mono 
      simp 
    ·
      calc s₁ \ s₂ ⊇ s₁ \ (s₁ ∩ s₂) :=
        by 
          simp [· ⊇ ·]_ ⊇ s₁ \ ∅ :=
        by 
          mono using · ⊇ ·_ ⊇ s₁ :=
        by 
          simp [· ⊇ ·]

theorem filter_union_filter_neg_eq [DecidablePred fun a => ¬p a] (s : Finset α) :
  (s.filter p ∪ s.filter fun a => ¬p a) = s :=
  by 
    simp only [filter_not, union_sdiff_of_subset (filter_subset p s)]

theorem filter_inter_filter_neg_eq [DecidablePred fun a => ¬p a] (s : Finset α) :
  (s.filter p ∩ s.filter fun a => ¬p a) = ∅ :=
  by 
    simp only [filter_not, inter_sdiff_self]

theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : «expr↑ » s ⊆ t₁ ∪ t₂) :
  ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ «expr↑ » s₁ ⊆ t₁ ∧ «expr↑ » s₂ ⊆ t₂ \ t₁ :=
  by 
    classical 
    refine' ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), _, _, _⟩
    ·
      simp [filter_union_right, em]
    ·
      intro x 
      simp 
    ·
      intro x 
      simp 
      intro hx hx₂ 
      refine' ⟨Or.resolve_left (h hx) hx₂, hx₂⟩

@[simp]
theorem filter_congr_decidable {α} (s : Finset α) (p : α → Prop) (h : DecidablePred p) [DecidablePred p] :
  @filter α p h s = s.filter p :=
  by 
    congr

section Classical

open_locale Classical

/-- The following instance allows us to write `{x ∈ s | p x}` for `finset.filter p s`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{x ∈ s | p x}` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{x ∈ s | p x}` to `finset.filter p s`. If `p` happens to be decidable, the
  simp-lemma `finset.filter_congr_decidable` will make sure that `finset.filter` uses the right
  instance for decidability.
-/
noncomputable instance  {α : Type _} : HasSep α (Finset α) :=
  ⟨fun p x => x.filter p⟩

@[simp]
theorem sep_def {α : Type _} (s : Finset α) (p : α → Prop) : { x∈s | p x } = s.filter p :=
  rfl

end Classical

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) : s.filter (Eq b) = ite (b ∈ s) {b} ∅ :=
  by 
    splitIfs
    ·
      ext 
      simp only [mem_filter, mem_singleton]
      exact
        ⟨fun h => h.2.symm,
          by 
            rintro ⟨h⟩
            exact ⟨h, rfl⟩⟩
    ·
      ext 
      simp only [mem_filter, not_and, iff_falseₓ, not_mem_empty]
      rintro m ⟨e⟩
      exact h m

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ :=
  trans (filter_congr fun _ _ => ⟨Eq.symm, Eq.symm⟩) (filter_eq s b)

theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => b ≠ a) = s.erase b :=
  by 
    ext 
    simp only [mem_filter, mem_erase, Ne.def]
    tauto

theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  trans (filter_congr fun _ _ => ⟨Ne.symm, Ne.symm⟩) (filter_ne s b)

end Filter

/-! ### range -/


section Range

variable{n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩

@[simp]
theorem range_coe (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl

@[simp]
theorem mem_range : m ∈ range n ↔ m < n :=
  mem_range

@[simp]
theorem range_zero : range 0 = ∅ :=
  rfl

@[simp]
theorem range_one : range 1 = {0} :=
  rfl

theorem range_succ : range (succ n) = insert n (range n) :=
  eq_of_veq$ (range_succ n).trans$ (ndinsert_of_not_mem not_mem_range_self).symm

theorem range_add_one : range (n+1) = insert n (range n) :=
  range_succ

@[simp]
theorem not_mem_range_self : n ∉ range n :=
  not_mem_range_self

@[simp]
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n+1) :=
  Multiset.self_mem_range_succ n

@[simp]
theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
  range_subset

theorem range_mono : Monotone range :=
  fun _ _ => range_subset.2

theorem mem_range_succ_iff {a b : ℕ} : a ∈ Finset.range b.succ ↔ a ≤ b :=
  Finset.mem_range.trans Nat.lt_succ_iff

theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
  (mem_range.1 hx).le

theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
  ne_of_gtₓ$ tsub_pos_of_lt$ mem_range.1 hx

@[simp]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => ((zero_le k).trans_lt$ mem_range.1 hk).ne', fun h => ⟨0, mem_range.2$ pos_iff_ne_zero.2 h⟩⟩

@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 :=
  by 
    rw [←not_nonempty_iff_eq_empty, nonempty_range_iff, not_not]

theorem nonempty_range_succ : (range$ n+1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero

end Range

theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False :=
  by 
    simp only [not_mem_empty, false_andₓ, exists_false]

theorem exists_mem_insert [d : DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x :=
  by 
    simp only [mem_insert, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True :=
  iff_true_intro$ fun _ => False.elim

theorem forall_mem_insert [d : DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x :=
  by 
    simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

end Finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def notMemRangeEquiv (k : ℕ) : { n // n ∉ range k } ≃ ℕ :=
  { toFun := fun i => i.1 - k,
    invFun :=
      fun j =>
        ⟨j+k,
          by 
            simp ⟩,
    left_inv :=
      by 
        intro j 
        rw [Subtype.ext_iff_val]
        apply tsub_add_cancel_of_le 
        simpa using j.2,
    right_inv := fun j => add_tsub_cancel_right _ _ }

@[simp]
theorem coe_not_mem_range_equiv (k : ℕ) : (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun i => i - k :=
  rfl

@[simp]
theorem coe_not_mem_range_equiv_symm (k : ℕ) :
  ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) =
    fun j =>
      ⟨j+k,
        by 
          simp ⟩ :=
  rfl

/-! ### erase_dup on list and multiset -/


namespace Multiset

variable[DecidableEq α]

/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def to_finset (s : Multiset α) : Finset α :=
  ⟨_, nodup_erase_dup s⟩

@[simp]
theorem to_finset_val (s : Multiset α) : s.to_finset.1 = s.erase_dup :=
  rfl

theorem to_finset_eq {s : Multiset α} (n : nodup s) : Finset.mk s n = s.to_finset :=
  Finset.val_inj.1 n.erase_dup.symm

theorem nodup.to_finset_inj {l l' : Multiset α} (hl : nodup l) (hl' : nodup l') (h : l.to_finset = l'.to_finset) :
  l = l' :=
  by 
    simpa [←to_finset_eq hl, ←to_finset_eq hl'] using h

@[simp]
theorem mem_to_finset {a : α} {s : Multiset α} : a ∈ s.to_finset ↔ a ∈ s :=
  mem_erase_dup

@[simp]
theorem to_finset_zero : to_finset (0 : Multiset α) = ∅ :=
  rfl

@[simp]
theorem to_finset_cons (a : α) (s : Multiset α) : to_finset (a ::ₘ s) = insert a (to_finset s) :=
  Finset.eq_of_veq erase_dup_cons

@[simp]
theorem to_finset_singleton (a : α) : to_finset ({a} : Multiset α) = {a} :=
  by 
    rw [singleton_eq_cons, to_finset_cons, to_finset_zero, IsLawfulSingleton.insert_emptyc_eq]

@[simp]
theorem to_finset_add (s t : Multiset α) : to_finset (s+t) = to_finset s ∪ to_finset t :=
  Finset.ext$
    by 
      simp 

@[simp]
theorem to_finset_nsmul (s : Multiset α) : ∀ (n : ℕ) (hn : n ≠ 0), (n • s).toFinset = s.to_finset
| 0, h =>
  by 
    contradiction
| n+1, h =>
  by 
    byCases' n = 0
    ·
      rw [h, zero_addₓ, one_nsmul]
    ·
      rw [add_nsmul, to_finset_add, one_nsmul, to_finset_nsmul n h, Finset.union_idempotent]

@[simp]
theorem to_finset_inter (s t : Multiset α) : to_finset (s ∩ t) = to_finset s ∩ to_finset t :=
  Finset.ext$
    by 
      simp 

@[simp]
theorem to_finset_union (s t : Multiset α) : (s ∪ t).toFinset = s.to_finset ∪ t.to_finset :=
  by 
    ext <;> simp 

theorem to_finset_eq_empty {m : Multiset α} : m.to_finset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.erase_dup_eq_zero

@[simp]
theorem to_finset_subset (m1 m2 : Multiset α) : m1.to_finset ⊆ m2.to_finset ↔ m1 ⊆ m2 :=
  by 
    simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_to_finset]

end Multiset

namespace Finset

@[simp]
theorem val_to_finset [DecidableEq α] (s : Finset α) : s.val.to_finset = s :=
  by 
    ext 
    rw [Multiset.mem_to_finset, ←mem_def]

end Finset

namespace List

variable[DecidableEq α]

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset (l : List α) : Finset α :=
  Multiset.toFinset l

@[simp]
theorem to_finset_val (l : List α) : l.to_finset.1 = (l.erase_dup : Multiset α) :=
  rfl

theorem to_finset_eq {l : List α} (n : nodup l) : @Finset.mk α l n = l.to_finset :=
  Multiset.to_finset_eq n

@[simp]
theorem mem_to_finset {a : α} {l : List α} : a ∈ l.to_finset ↔ a ∈ l :=
  mem_erase_dup

@[simp]
theorem to_finset_nil : to_finset (@nil α) = ∅ :=
  rfl

@[simp]
theorem to_finset_cons {a : α} {l : List α} : to_finset (a :: l) = insert a (to_finset l) :=
  Finset.eq_of_veq$
    by 
      byCases' h : a ∈ l <;> simp [Finset.insert_val', Multiset.erase_dup_cons, h]

theorem to_finset_surj_on : Set.SurjOn to_finset { l:List α | l.nodup } Set.Univ :=
  by 
    rintro s -
    cases' s with t hl 
    induction' t using Quot.ind with l 
    refine' ⟨l, hl, (to_finset_eq hl).symm⟩

theorem to_finset_surjective : surjective (to_finset : List α → Finset α) :=
  by 
    intro s 
    rcases to_finset_surj_on (Set.mem_univ s) with ⟨l, -, hls⟩
    exact ⟨l, hls⟩

theorem to_finset_eq_iff_perm_erase_dup {l l' : List α} : l.to_finset = l'.to_finset ↔ l.erase_dup ~ l'.erase_dup :=
  by 
    simp [Finset.ext_iff, perm_ext (nodup_erase_dup _) (nodup_erase_dup _)]

theorem to_finset_eq_of_perm (l l' : List α) (h : l ~ l') : l.to_finset = l'.to_finset :=
  to_finset_eq_iff_perm_erase_dup.mpr h.erase_dup

theorem perm_of_nodup_nodup_to_finset_eq {l l' : List α} (hl : nodup l) (hl' : nodup l')
  (h : l.to_finset = l'.to_finset) : l ~ l' :=
  by 
    rw [←Multiset.coe_eq_coe]
    exact Multiset.Nodup.to_finset_inj hl hl' h

@[simp]
theorem to_finset_append {l l' : List α} : to_finset (l ++ l') = l.to_finset ∪ l'.to_finset :=
  by 
    induction' l with hd tl hl
    ·
      simp 
    ·
      simp [hl]

@[simp]
theorem to_finset_reverse {l : List α} : to_finset l.reverse = l.to_finset :=
  to_finset_eq_of_perm _ _ (reverse_perm l)

theorem to_finset_repeat_of_ne_zero {a : α} {n : ℕ} (hn : n ≠ 0) : (List.repeat a n).toFinset = {a} :=
  by 
    ext x 
    simp [hn, List.mem_repeat]

@[simp]
theorem to_finset_union (l l' : List α) : (l ∪ l').toFinset = l.to_finset ∪ l'.to_finset :=
  by 
    ext 
    simp 

@[simp]
theorem to_finset_inter (l l' : List α) : (l ∩ l').toFinset = l.to_finset ∩ l'.to_finset :=
  by 
    ext 
    simp 

end List

namespace Finset

/-! ### map -/


section Map

open Function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, nodup_map f.2 s.2⟩

@[simp]
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl

@[simp]
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl

variable{f : α ↪ β}{s : Finset α}

@[simp]
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ (a : _)(_ : a ∈ s), f a = b :=
  mem_map.trans$
    by 
      simp only [exists_prop] <;> rfl

@[simp]
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.to_embedding ↔ f.symm b ∈ s :=
  by 
    rw [mem_map]
    exact
      ⟨by 
          rintro ⟨a, H, rfl⟩
          simpa,
        fun h =>
          ⟨_, h,
            by 
              simp ⟩⟩

theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2

theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2

theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.prop

@[simp, normCast]
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s :=
  Set.ext$ fun x => mem_map.trans Set.mem_image_iff_bex.symm

theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.Range f :=
  calc «expr↑ » (s.map f) = f '' s := coe_map f s 
    _ ⊆ Set.Range f := Set.image_subset_range f («expr↑ » s)
    

theorem map_to_finset [DecidableEq α] [DecidableEq β] {s : Multiset α} : s.to_finset.map f = (s.map f).toFinset :=
  ext$
    fun _ =>
      by 
        simp only [mem_map, Multiset.mem_map, exists_prop, Multiset.mem_to_finset]

@[simp]
theorem map_refl : s.map (embedding.refl _) = s :=
  ext$
    fun _ =>
      by 
        simpa only [mem_map, exists_prop] using exists_eq_right

@[simp]
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) : HEq (s.map (Equiv.cast h).toEmbedding) s :=
  by 
    subst h 
    simp 

theorem map_map {g : β ↪ γ} : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq$
    by 
      simp only [map_val, Multiset.map_map] <;> rfl

@[simp]
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h x xs => (mem_map' _).1$ h$ (mem_map' f).2 xs,
    fun h =>
      by 
        simp [subset_def, map_subset_map h]⟩

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def map_embedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLeIff (map f) fun _ _ => map_subset_map

@[simp]
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (map_embedding f).Injective.eq_iff

@[simp]
theorem map_embedding_apply : map_embedding f s = map f s :=
  rfl

theorem map_filter {p : β → Prop} [DecidablePred p] : (s.map f).filter p = (s.filter (p ∘ f)).map f :=
  eq_of_veq (map_filter _ _ _)

theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
  (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  coe_injective$
    by 
      simp only [coe_map, coe_union, Set.image_union]

theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
  (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  coe_injective$
    by 
      simp only [coe_map, coe_inter, Set.image_inter f.injective]

@[simp]
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective$
    by 
      simp only [coe_map, coe_singleton, Set.image_singleton]

@[simp]
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
  (insert a s).map f = insert (f a) (s.map f) :=
  by 
    simp only [insert_eq, map_union, map_singleton]

@[simp]
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem$ fun a m => ne_empty_of_mem (mem_map_of_mem _ m) h, fun e => e.symm ▸ rfl⟩

theorem attach_map_val {s : Finset α} : s.attach.map (embedding.subtype _) = s :=
  eq_of_veq$
    by 
      rw [map_val, attach_val] <;> exact attach_map_val _

theorem Nonempty.map (h : s.nonempty) (f : α ↪ β) : (s.map f).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨f a, (mem_map' f).mpr ha⟩

end Map

theorem range_add_one' (n : ℕ) : range (n+1) = insert 0 ((range n).map ⟨fun i => i+1, fun i j => Nat.succ.injₓ⟩) :=
  by 
    ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.succ_eq_add_one, Nat.zero_lt_succₓ n]

/-! ### image -/


section Image

variable[DecidableEq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).eraseDup :=
  rfl

@[simp]
theorem image_empty (f : α → β) : (∅ : Finset α).Image f = ∅ :=
  rfl

variable{f : α → β}{s : Finset α}

@[simp]
theorem mem_image {b : β} : b ∈ s.image f ↔ ∃ (a : _)(_ : a ∈ s), f a = b :=
  by 
    simp only [mem_def, image_val, mem_erase_dup, Multiset.mem_map, exists_prop]

theorem mem_image_of_mem (f : α → β) {a} {s : Finset α} (h : a ∈ s) : f a ∈ s.image f :=
  mem_image.2 ⟨_, h, rfl⟩

instance  [CanLift β α] : CanLift (Finset β) (Finset α) :=
  { cond := fun s => ∀ x (_ : x ∈ s), CanLift.Cond α x, coe := image CanLift.coe,
    prf :=
      by 
        rintro ⟨⟨l⟩, hd : l.nodup⟩ hl 
        lift l to List α using hl 
        refine' ⟨⟨l, List.nodup_of_nodup_map _ hd⟩, ext$ fun a => _⟩
        simp  }

theorem _root_.function.injective.mem_finset_image {f : α → β} (hf : Function.Injective f) {s : Finset α} {x : α} :
  f x ∈ s.image f ↔ x ∈ s :=
  by 
    refine' ⟨fun h => _, Finset.mem_image_of_mem f⟩
    obtain ⟨y, hy, heq⟩ := mem_image.1 h 
    exact hf HEq ▸ hy

theorem filter_mem_image_eq_image (f : α → β) (s : Finset α) (t : Finset β) (h : ∀ x (_ : x ∈ s), f x ∈ t) :
  (t.filter fun y => y ∈ s.image f) = s.image f :=
  by 
    ext 
    rw [mem_filter, mem_image]
    simp only [and_imp, exists_prop, and_iff_right_iff_imp, exists_imp_distrib]
    rintro x xel rfl 
    exact h _ xel

theorem fiber_nonempty_iff_mem_image (f : α → β) (s : Finset α) (y : β) :
  (s.filter fun x => f x = y).Nonempty ↔ y ∈ s.image f :=
  by 
    simp [Finset.Nonempty]

@[simp, normCast]
theorem coe_image {f : α → β} : «expr↑ » (s.image f) = f '' «expr↑ » s :=
  Set.ext$ fun _ => mem_image.trans Set.mem_image_iff_bex.symm

theorem nonempty.image (h : s.nonempty) (f : α → β) : (s.image f).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨f a, mem_image_of_mem f ha⟩

@[simp]
theorem nonempty.image_iff (f : α → β) : (s.image f).Nonempty ↔ s.nonempty :=
  ⟨fun ⟨y, hy⟩ =>
      let ⟨x, hx, _⟩ := mem_image.mp hy
      ⟨x, hx⟩,
    fun h => h.image f⟩

theorem image_to_finset [DecidableEq α] {s : Multiset α} : s.to_finset.image f = (s.map f).toFinset :=
  ext$
    fun _ =>
      by 
        simp only [mem_image, Multiset.mem_to_finset, exists_prop, Multiset.mem_map]

theorem image_val_of_inj_on (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (nodup_map_on H s.2).eraseDup

@[simp]
theorem image_id [DecidableEq α] : s.image id = s :=
  ext$
    fun _ =>
      by 
        simp only [mem_image, exists_prop, id, exists_eq_right]

@[simp]
theorem image_id' [DecidableEq α] : (s.image fun x => x) = s :=
  image_id

theorem image_image [DecidableEq γ] {g : β → γ} : (s.image f).Image g = s.image (g ∘ f) :=
  eq_of_veq$
    by 
      simp only [image_val, erase_dup_map_erase_dup_eq, Multiset.map_map]

theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
  by 
    simp only [subset_def, image_val, subset_erase_dup', erase_dup_subset', Multiset.map_subset_map h]

theorem image_subset_iff {s : Finset α} {t : Finset β} {f : α → β} : s.image f ⊆ t ↔ ∀ x (_ : x ∈ s), f x ∈ t :=
  calc s.image f ⊆ t ↔ f '' «expr↑ » s ⊆ «expr↑ » t :=
    by 
      normCast 
    _ ↔ _ := Set.image_subset_iff
    

theorem image_mono (f : α → β) : Monotone (Finset.image f) :=
  fun _ _ => image_subset_image

theorem coe_image_subset_range : «expr↑ » (s.image f) ⊆ Set.Range f :=
  calc «expr↑ » (s.image f) = f '' «expr↑ » s := coe_image 
    _ ⊆ Set.Range f := Set.image_subset_range f («expr↑ » s)
    

theorem image_filter {p : β → Prop} [DecidablePred p] : (s.image f).filter p = (s.filter (p ∘ f)).Image f :=
  ext$
    fun b =>
      by 
        simp only [mem_filter, mem_image, exists_prop] <;>
          exact
            ⟨by 
                rintro ⟨⟨x, h1, rfl⟩, h2⟩ <;> exact ⟨x, ⟨h1, h2⟩, rfl⟩,
              by 
                rintro ⟨x, ⟨h1, h2⟩, rfl⟩ <;> exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) : (s₁ ∪ s₂).Image f = s₁.image f ∪ s₂.image f :=
  ext$
    fun _ =>
      by 
        simp only [mem_image, mem_union, exists_prop, or_and_distrib_right, exists_or_distrib]

theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : ∀ x y, f x = f y → x = y) :
  (s₁ ∩ s₂).Image f = s₁.image f ∩ s₂.image f :=
  ext$
    by 
      simp only [mem_image, exists_prop, mem_inter] <;>
        exact
          fun b =>
            ⟨fun ⟨a, ⟨m₁, m₂⟩, e⟩ => ⟨⟨a, m₁, e⟩, ⟨a, m₂, e⟩⟩,
              fun ⟨⟨a, m₁, e₁⟩, ⟨a', m₂, e₂⟩⟩ => ⟨a, ⟨m₁, hf _ _ (e₂.trans e₁.symm) ▸ m₂⟩, e₁⟩⟩

@[simp]
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
  ext$
    fun x =>
      by 
        simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm

@[simp]
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
  (insert a s).Image f = insert (f a) (s.image f) :=
  by 
    simp only [insert_eq, image_singleton, image_union]

@[simp]
theorem image_erase [DecidableEq α] {f : α → β} (hf : injective f) (s : Finset α) (a : α) :
  (s.erase a).Image f = (s.image f).erase (f a) :=
  by 
    ext b 
    simp only [mem_image, exists_prop, mem_erase]
    split 
    ·
      rintro ⟨a', ⟨haa', ha'⟩, rfl⟩
      exact ⟨hf.ne haa', a', ha', rfl⟩
    ·
      rintro ⟨h, a', ha', rfl⟩
      exact ⟨a', ⟨ne_of_apply_ne _ h, ha'⟩, rfl⟩

@[simp]
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem$ fun a m => ne_empty_of_mem (mem_image_of_mem _ m) h, fun e => e.symm ▸ rfl⟩

theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ} (hn : 0 < n)
  (h : ∀ i, f (i % n) = f i) : a ∈ Set.Range f ↔ a ∈ (Finset.range n).Image fun i => f i :=
  by 
    split 
    ·
      rintro ⟨i, hi⟩
      simp only [mem_image, exists_prop, mem_range]
      exact ⟨i % n, Nat.mod_ltₓ i hn, (rfl.congr hi).mp (h i)⟩
    ·
      rintro h 
      simp only [mem_image, exists_prop, Set.mem_range, mem_range] at *
      rcases h with ⟨i, hi, ha⟩
      use ⟨i, ha⟩

theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ} (hn : 0 < n)
  (h : ∀ i, f (i % n) = f i) : a ∈ Set.Range f ↔ a ∈ (Finset.range n).Image fun i => f i :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f («expr↑ » i) = a by 
    simpa [h]
  have hn' : 0 < (n : ℤ) := Int.coe_nat_lt.mpr hn 
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have  : 0 ≤ i % «expr↑ » n := Int.mod_nonneg _ (ne_of_gtₓ hn')
      ⟨Int.toNat (i % n),
        by 
          rw [←Int.coe_nat_lt, Int.to_nat_of_nonneg this] <;> exact ⟨Int.mod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
      ⟨i,
        by 
          rw [Int.mod_eq_of_lt (Int.coe_zero_le _) (Int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩

@[simp]
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.val = s :=
  eq_of_veq$
    by 
      rw [image_val, attach_val, Multiset.attach_map_val, erase_dup_eq_self]

@[simp]
theorem attach_image_coe [DecidableEq α] {s : Finset α} : s.attach.image coeₓ = s :=
  Finset.attach_image_val

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem attach_insert
[decidable_eq α]
{a : α}
{s : finset α} : «expr = »(attach (insert a s), insert (⟨a, mem_insert_self a s⟩ : {x // «expr ∈ »(x, insert a s)}) ((attach s).image (λ
   x, ⟨x.1, mem_insert_of_mem x.2⟩))) :=
«expr $ »(ext, λ
 ⟨x, hx⟩, ⟨or.cases_on (mem_insert.1 hx) (λ
   h : «expr = »(x, a), λ
   _, «expr $ »(mem_insert.2, «expr $ »(or.inl, subtype.eq h))) (λ
   h : «expr ∈ »(x, s), λ
   _, «expr $ »(mem_insert_of_mem, «expr $ »(mem_image.2, ⟨⟨x, h⟩, mem_attach _ _, subtype.eq rfl⟩))), λ
  _, finset.mem_attach _ _⟩)

theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.eraseDup.symm

theorem image_const {s : Finset α} (h : s.nonempty) (b : β) : (s.image fun a => b) = singleton b :=
  ext$
    fun b' =>
      by 
        simp only [mem_image, exists_prop, exists_and_distrib_right, h.bex, true_andₓ, mem_singleton, eq_comm]

@[simp]
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) : (s.erase a).map f = (s.map f).erase (f a) :=
  by 
    simpRw [map_eq_image]
    exact s.image_erase f.2 a

/--
Because `finset.image` requires a `decidable_eq` instances for the target type,
we can only construct a `functor finset` when working classically.
-/
instance  [∀ P, Decidable P] : Functor Finset :=
  { map := fun α β f s => s.image f }

instance  [∀ P, Decidable P] : IsLawfulFunctor Finset :=
  { id_map := fun α x => image_id, comp_map := fun α β γ f g s => image_image.symm }

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`. -/
protected def Subtype {α} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filter p).attach.map ⟨fun x => ⟨x.1, (Finset.mem_filter.1 x.2).2⟩, fun x y H => Subtype.eq$ Subtype.mk.injₓ H⟩

@[simp]
theorem mem_subtype {p : α → Prop} [DecidablePred p] {s : Finset α} : ∀ {a : Subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
| ⟨a, ha⟩ =>
  by 
    simp [Finset.subtype, ha]

theorem subtype_eq_empty {p : α → Prop} [DecidablePred p] {s : Finset α} : s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s :=
  by 
    simp [ext_iff, Subtype.forall, Subtype.coe_mk] <;> rfl

@[mono]
theorem subtype_mono {p : α → Prop} [DecidablePred p] : Monotone (Finset.subtype p) :=
  fun s t h x hx => mem_subtype.2$ h$ mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp]
theorem subtype_map (p : α → Prop) [DecidablePred p] : (s.subtype p).map (embedding.subtype _) = s.filter p :=
  by 
    ext x 
    simp [and_comm _ (_ = _), @And.left_comm _ (_ = _), and_comm (p x) (x ∈ s)]

/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
theorem subtype_map_of_mem {p : α → Prop} [DecidablePred p] (h : ∀ x (_ : x ∈ s), p x) :
  (s.subtype p).map (embedding.subtype _) = s :=
  by 
    rw [subtype_map, filter_true_of_mem h]

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
theorem property_of_mem_map_subtype {p : α → Prop} (s : Finset { x // p x }) {a : α}
  (h : a ∈ s.map (embedding.subtype _)) : p a :=
  by 
    rcases mem_map.1 h with ⟨x, hx, rfl⟩
    exact x.2

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
theorem not_mem_map_subtype_of_not_property {p : α → Prop} (s : Finset { x // p x }) {a : α} (h : ¬p a) :
  a ∉ s.map (embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
theorem map_subtype_subset {t : Set α} (s : Finset t) : «expr↑ » (s.map (embedding.subtype _)) ⊆ t :=
  by 
    intro a ha 
    rw [mem_coe] at ha 
    convert property_of_mem_map_subtype s ha

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem subset_image_iff
{f : α → β}
{s : finset β}
{t : set α} : «expr ↔ »(«expr ⊆ »(«expr↑ »(s), «expr '' »(f, t)), «expr∃ , »((s' : finset α), «expr ∧ »(«expr ⊆ »(«expr↑ »(s'), t), «expr = »(s'.image f, s)))) :=
begin
  split,
  swap,
  { rintro ["⟨", ident s, ",", ident hs, ",", ident rfl, "⟩"],
    rw ["[", expr coe_image, "]"] [],
    exact [expr set.image_subset f hs] },
  intro [ident h],
  letI [] [":", expr can_lift β t] [":=", expr ⟨«expr ∘ »(f, coe), λ
    y, «expr ∈ »(y, «expr '' »(f, t)), λ (y) ⟨x, hxt, hy⟩, ⟨⟨x, hxt⟩, hy⟩⟩],
  lift [expr s] ["to", expr finset t] ["using", expr h] [],
  refine [expr ⟨s.map (embedding.subtype _), map_subtype_subset _, _⟩],
  ext [] [ident y] [],
  simp [] [] [] [] [] []
end

end Image

end Finset

theorem Multiset.to_finset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
  (m.map f).toFinset = m.to_finset.image f :=
  Finset.val_inj.1 (Multiset.erase_dup_map_erase_dup_eq _ _).symm

namespace Finset

/-! ### card -/


section Card

/-- `card s` is the cardinality (number of elements) of `s`. -/
def card (s : Finset α) : Nat :=
  s.1.card

theorem card_def (s : Finset α) : s.card = s.1.card :=
  rfl

@[simp]
theorem card_mk {m nodup} : (⟨m, nodup⟩ : Finset α).card = m.card :=
  rfl

@[simp]
theorem card_empty : card (∅ : Finset α) = 0 :=
  rfl

theorem card_le_of_subset {s t : Finset α} : s ⊆ t → card s ≤ card t :=
  Multiset.card_le_of_le ∘ val_le_iff.mpr

@[simp]
theorem card_eq_zero {s : Finset α} : card s = 0 ↔ s = ∅ :=
  card_eq_zero.trans val_eq_zero

theorem card_pos {s : Finset α} : 0 < card s ↔ s.nonempty :=
  pos_iff_ne_zero.trans$ (not_congr card_eq_zero).trans nonempty_iff_ne_empty.symm

alias Finset.card_pos ↔ _ Finset.Nonempty.card_pos

theorem card_ne_zero_of_mem {s : Finset α} {a : α} (h : a ∈ s) : card s ≠ 0 :=
  (not_congr card_eq_zero).2 (ne_empty_of_mem h)

theorem card_eq_one {s : Finset α} : s.card = 1 ↔ ∃ a, s = {a} :=
  by 
    cases s <;> simp only [Multiset.card_eq_one, Finset.card, ←val_inj, singleton_val]

theorem card_le_one {s : Finset α} : s.card ≤ 1 ↔ ∀ a (_ : a ∈ s) b (_ : b ∈ s), a = b :=
  by 
    rcases s.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
    ·
      simp 
    refine' (Nat.succ_le_of_ltₓ (card_pos.2 ⟨x, hx⟩)).le_iff_eq.trans (card_eq_one.trans ⟨_, _⟩)
    ·
      rintro ⟨y, rfl⟩
      simp 
    ·
      exact fun h => ⟨x, eq_singleton_iff_unique_mem.2 ⟨hx, fun y hy => h _ hy _ hx⟩⟩

theorem card_le_one_iff {s : Finset α} : s.card ≤ 1 ↔ ∀ {a b}, a ∈ s → b ∈ s → a = b :=
  by 
    rw [card_le_one]
    tauto

theorem card_le_one_iff_subset_singleton [Nonempty α] {s : Finset α} : s.card ≤ 1 ↔ ∃ x : α, s ⊆ {x} :=
  by 
    split 
    ·
      intro H 
      byCases' h : ∃ x, x ∈ s
      ·
        rcases h with ⟨x, hx⟩
        refine' ⟨x, fun y hy => _⟩
        rw [card_le_one.1 H y hy x hx, mem_singleton]
      ·
        pushNeg  at h 
        inhabit α 
        exact ⟨default α, fun y hy => (h y hy).elim⟩
    ·
      rintro ⟨x, hx⟩
      rw [←card_singleton x]
      exact card_le_of_subset hx

/-- A `finset` of a subsingleton type has cardinality at most one. -/
theorem card_le_one_of_subsingleton [Subsingleton α] (s : Finset α) : s.card ≤ 1 :=
  Finset.card_le_one_iff.2$ fun _ _ _ _ => Subsingleton.elimₓ _ _

theorem one_lt_card {s : Finset α} : 1 < s.card ↔ ∃ (a : _)(_ : a ∈ s)(b : _)(_ : b ∈ s), a ≠ b :=
  by 
    rw [←not_iff_not]
    pushNeg 
    exact card_le_one

theorem exists_ne_of_one_lt_card {s : Finset α} (hs : 1 < s.card) (a : α) : ∃ b : α, b ∈ s ∧ b ≠ a :=
  by 
    obtain ⟨x, hx, y, hy, hxy⟩ := finset.one_lt_card.mp hs 
    byCases' ha : y = a
    ·
      exact ⟨x, hx, ne_of_ne_of_eq hxy ha⟩
    ·
      exact ⟨y, hy, ha⟩

theorem one_lt_card_iff {s : Finset α} : 1 < s.card ↔ ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y :=
  by 
    rw [one_lt_card]
    simp only [exists_prop, exists_and_distrib_left]

@[simp]
theorem card_cons {a : α} {s : Finset α} (h : a ∉ s) : card (cons a s h) = card s+1 :=
  card_cons _ _

@[simp]
theorem card_insert_of_not_mem [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) : card (insert a s) = card s+1 :=
  by 
    rw [←cons_eq_insert _ _ h, card_cons]

theorem card_insert_of_mem [DecidableEq α] {a : α} {s : Finset α} (h : a ∈ s) : card (insert a s) = card s :=
  by 
    rw [insert_eq_of_mem h]

theorem card_insert_le [DecidableEq α] (a : α) (s : Finset α) : card (insert a s) ≤ card s+1 :=
  by 
    byCases' a ∈ s <;>
      [·
        rw [insert_eq_of_mem h]
        apply Nat.le_add_rightₓ,
      rw [card_insert_of_not_mem h]]

/-- If `a ∈ s` is known, see also `finset.card_insert_of_mem` and
`finset.card_insert_of_not_mem`. -/
theorem card_insert_eq_ite [DecidableEq α] {a : α} {s : Finset α} :
  card (insert a s) = if a ∈ s then card s else card s+1 :=
  by 
    byCases' h : a ∈ s
    ·
      rw [card_insert_of_mem h, if_pos h]
    ·
      rw [card_insert_of_not_mem h, if_neg h]

@[simp]
theorem card_singleton (a : α) : card ({a} : Finset α) = 1 :=
  card_singleton _

theorem card_singleton_inter [DecidableEq α] {x : α} {s : Finset α} : ({x} ∩ s).card ≤ 1 :=
  by 
    cases Finset.decidableMem x s
    ·
      simp [Finset.singleton_inter_of_not_mem h]
    ·
      simp [Finset.singleton_inter_of_mem h]

@[simp]
theorem card_erase_of_mem [DecidableEq α] {a : α} {s : Finset α} : a ∈ s → card (erase s a) = pred (card s) :=
  card_erase_of_mem

theorem card_erase_lt_of_mem [DecidableEq α] {a : α} {s : Finset α} : a ∈ s → card (erase s a) < card s :=
  card_erase_lt_of_mem

theorem card_erase_le [DecidableEq α] {a : α} {s : Finset α} : card (erase s a) ≤ card s :=
  card_erase_le

theorem pred_card_le_card_erase [DecidableEq α] {a : α} {s : Finset α} : card s - 1 ≤ card (erase s a) :=
  by 
    byCases' h : a ∈ s
    ·
      rw [card_erase_of_mem h]
      rfl
    ·
      rw [erase_eq_of_not_mem h]
      apply Nat.sub_leₓ

/-- If `a ∈ s` is known, see also `finset.card_erase_of_mem` and `finset.erase_eq_of_not_mem`. -/
theorem card_erase_eq_ite [DecidableEq α] {a : α} {s : Finset α} :
  card (erase s a) = if a ∈ s then pred (card s) else card s :=
  card_erase_eq_ite

@[simp]
theorem card_range (n : ℕ) : card (range n) = n :=
  card_range n

@[simp]
theorem card_attach {s : Finset α} : card (attach s) = card s :=
  Multiset.card_attach

end Card

end Finset

theorem Multiset.to_finset_card_le [DecidableEq α] (m : Multiset α) : m.to_finset.card ≤ m.card :=
  card_le_of_le (erase_dup_le _)

theorem List.card_to_finset [DecidableEq α] (l : List α) : Finset.card l.to_finset = l.erase_dup.length :=
  rfl

theorem List.to_finset_card_le [DecidableEq α] (l : List α) : l.to_finset.card ≤ l.length :=
  Multiset.to_finset_card_le («expr⟦ ⟧» l)

namespace Finset

section Card

theorem card_image_le [DecidableEq β] {f : α → β} {s : Finset α} : card (image f s) ≤ card s :=
  by 
    simpa only [card_map] using (s.1.map f).to_finset_card_le

theorem card_image_of_inj_on [DecidableEq β] {f : α → β} {s : Finset α} (H : Set.InjOn f s) :
  card (image f s) = card s :=
  by 
    simp only [card, image_val_of_inj_on H, card_map]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inj_on_of_card_image_eq
[decidable_eq β]
{f : α → β}
{s : finset α}
(H : «expr = »(card (image f s), card s)) : set.inj_on f s :=
begin
  change [expr «expr = »((s.1.map f).erase_dup.card, s.1.card)] [] ["at", ident H],
  have [] [":", expr «expr = »((s.1.map f).erase_dup, s.1.map f)] [],
  { apply [expr multiset.eq_of_le_of_card_le],
    { apply [expr multiset.erase_dup_le] },
    rw [expr H] [],
    simp [] [] ["only"] ["[", expr multiset.card_map, "]"] [] [] },
  rw [expr multiset.erase_dup_eq_self] ["at", ident this],
  apply [expr inj_on_of_nodup_map this]
end

theorem card_image_eq_iff_inj_on [DecidableEq β] {f : α → β} {s : Finset α} :
  (s.image f).card = s.card ↔ Set.InjOn f s :=
  ⟨inj_on_of_card_image_eq, card_image_of_inj_on⟩

theorem card_image_of_injective [DecidableEq β] {f : α → β} (s : Finset α) (H : injective f) :
  card (image f s) = card s :=
  card_image_of_inj_on$ fun x _ y _ h => H h

theorem fiber_card_ne_zero_iff_mem_image (s : Finset α) (f : α → β) [DecidableEq β] (y : β) :
  (s.filter fun x => f x = y).card ≠ 0 ↔ y ∈ s.image f :=
  by 
    rw [←pos_iff_ne_zero, card_pos, fiber_nonempty_iff_mem_image]

@[simp]
theorem card_map {α β} (f : α ↪ β) {s : Finset α} : (s.map f).card = s.card :=
  Multiset.card_map _ _

@[simp]
theorem card_subtype (p : α → Prop) [DecidablePred p] (s : Finset α) : (s.subtype p).card = (s.filter p).card :=
  by 
    simp [Finset.subtype]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_eq_of_bijective
{s : finset α}
{n : exprℕ()}
(f : ∀ i, «expr < »(i, n) → α)
(hf : ∀ a «expr ∈ » s, «expr∃ , »((i), «expr∃ , »((h : «expr < »(i, n)), «expr = »(f i h, a))))
(hf' : ∀ (i) (h : «expr < »(i, n)), «expr ∈ »(f i h, s))
(f_inj : ∀
 (i j)
 (hi : «expr < »(i, n))
 (hj : «expr < »(j, n)), «expr = »(f i hi, f j hj) → «expr = »(i, j)) : «expr = »(card s, n) :=
begin
  classical,
  have [] [":", expr ∀
   a : α, «expr ↔ »(«expr ∈ »(a, s), «expr∃ , »((i)
     (hi : «expr ∈ »(i, range n)), «expr = »(f i (mem_range.1 hi), a)))] [],
  from [expr assume
   a, ⟨assume ha, let ⟨i, hi, eq⟩ := hf a ha in
    ⟨i, mem_range.2 hi, eq⟩, assume ⟨i, hi, eq⟩, «expr ▸ »(eq, hf' i (mem_range.1 hi))⟩],
  have [] [":", expr «expr = »(s, «expr $ »((range n).attach.image, λ i, f i.1 (mem_range.1 i.2)))] [],
  by simpa [] [] ["only"] ["[", expr ext_iff, ",", expr mem_image, ",", expr exists_prop, ",", expr subtype.exists, ",", expr mem_attach, ",", expr true_and, "]"] [] [],
  calc
    «expr = »(card s, card «expr $ »((range n).attach.image, λ
      i, f i.1 (mem_range.1 i.2))) : by rw ["[", expr this, "]"] []
    «expr = »(..., card (range n).attach) : «expr $ »(card_image_of_injective _, assume
     ⟨i, hi⟩
     ⟨j, hj⟩
     (eq), «expr $ »(subtype.eq, f_inj i j (mem_range.1 hi) (mem_range.1 hj) eq))
    «expr = »(..., card (range n)) : card_attach
    «expr = »(..., n) : card_range n
end

theorem card_eq_succ [DecidableEq α] {s : Finset α} {n : ℕ} :
  (s.card = n+1) ↔ ∃ a t, a ∉ t ∧ insert a t = s ∧ card t = n :=
  Iff.intro
    (fun eq =>
      have  : 0 < card s := Eq.symm ▸ Nat.zero_lt_succₓ _ 
      let ⟨a, has⟩ := card_pos.mp this
      ⟨a, s.erase a, s.not_mem_erase a, insert_erase has,
        by 
          simp only [Eq, card_erase_of_mem has, pred_succ]⟩)
    fun ⟨a, t, hat, s_eq, n_eq⟩ => s_eq ▸ n_eq ▸ card_insert_of_not_mem hat

theorem card_eq_two [DecidableEq α] {s : Finset α} : s.card = 2 ↔ ∃ x y, x ≠ y ∧ s = {x, y} :=
  by 
    split 
    ·
      rw [card_eq_succ]
      simpRw [card_eq_one]
      rintro ⟨a, _, hab, rfl, b, rfl⟩
      exact ⟨a, b, not_mem_singleton.1 hab, rfl⟩
    ·
      rintro ⟨x, y, hxy, rfl⟩
      simp only [hxy, card_insert_of_not_mem, not_false_iff, mem_singleton, card_singleton]

theorem card_eq_three [DecidableEq α] {s : Finset α} : s.card = 3 ↔ ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ s = {x, y, z} :=
  by 
    split 
    ·
      rw [card_eq_succ]
      simpRw [card_eq_two]
      rintro ⟨a, _, abc, rfl, b, c, bc, rfl⟩
      rw [mem_insert, mem_singleton, not_or_distrib] at abc 
      exact ⟨a, b, c, abc.1, abc.2, bc, rfl⟩
    ·
      rintro ⟨x, y, z, xy, xz, yz, rfl⟩
      simp only [xy, xz, yz, mem_insert, card_insert_of_not_mem, not_false_iff, mem_singleton, or_selfₓ, card_singleton]

theorem card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p] : card (s.filter p) ≤ card s :=
  card_le_of_subset$ filter_subset _ _

theorem eq_of_subset_of_card_le {s t : Finset α} (h : s ⊆ t) (h₂ : card t ≤ card s) : s = t :=
  eq_of_veq$ Multiset.eq_of_le_of_card_le (val_le_iff.mpr h) h₂

theorem filter_card_eq {s : Finset α} {p : α → Prop} [DecidablePred p] (h : (s.filter p).card = s.card) (x : α)
  (hx : x ∈ s) : p x :=
  by 
    rw [←eq_of_subset_of_card_le (s.filter_subset p) h.ge, mem_filter] at hx 
    exact hx.2

theorem card_lt_card {s t : Finset α} (h : s ⊂ t) : s.card < t.card :=
  card_lt_of_lt (val_lt_iff.2 h)

theorem card_le_card_of_inj_on {s : Finset α} {t : Finset β} (f : α → β) (hf : ∀ a (_ : a ∈ s), f a ∈ t)
  (f_inj : ∀ a₁ (_ : a₁ ∈ s), ∀ a₂ (_ : a₂ ∈ s), f a₁ = f a₂ → a₁ = a₂) : card s ≤ card t :=
  by 
    classical 
    calc card s = card (s.image f) :=
      by 
        rw [card_image_of_inj_on f_inj]_ ≤ card t :=
      card_le_of_subset$ image_subset_iff.2 hf

/--
If there are more pigeons than pigeonholes, then there are two pigeons
in the same pigeonhole.
-/
theorem exists_ne_map_eq_of_card_lt_of_maps_to {s : Finset α} {t : Finset β} (hc : t.card < s.card) {f : α → β}
  (hf : ∀ a (_ : a ∈ s), f a ∈ t) : ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s), x ≠ y ∧ f x = f y :=
  by 
    classical 
    byContra hz 
    pushNeg  at hz 
    refine' hc.not_le (card_le_card_of_inj_on f hf _)
    intro x hx y hy 
    contrapose 
    exact hz x hx y hy

theorem le_card_of_inj_on_range {n} {s : Finset α} (f : ℕ → α) (hf : ∀ i (_ : i < n), f i ∈ s)
  (f_inj : ∀ i (_ : i < n) j (_ : j < n), f i = f j → i = j) : n ≤ card s :=
  calc n = card (range n) := (card_range n).symm 
    _ ≤ card s :=
    card_le_card_of_inj_on f
      (by 
        simpa only [mem_range])
      (by 
        simpa only [mem_range])
    

/-- Suppose that, given objects defined on all strict subsets of any finset `s`, one knows how to
define an object on `s`. Then one can inductively define an object on all finsets, starting from
the empty set and iterating. This can be used either to define data, or to prove properties. -/
def strong_induction {p : Finset α → Sort _} (H : ∀ s, (∀ t (_ : t ⊂ s), p t) → p s) : ∀ (s : Finset α), p s
| s =>
  H s
    fun t h =>
      have  : card t < card s := card_lt_card h 
      strong_induction t

theorem strong_induction_eq {p : Finset α → Sort _} (H : ∀ s, (∀ t (_ : t ⊂ s), p t) → p s) (s : Finset α) :
  strong_induction H s = H s fun t h => strong_induction H t :=
  by 
    rw [strong_induction]

/-- Analogue of `strong_induction` with order of arguments swapped. -/
@[elab_as_eliminator]
def strong_induction_on {p : Finset α → Sort _} : ∀ (s : Finset α), (∀ s, (∀ t (_ : t ⊂ s), p t) → p s) → p s :=
  fun s H => strong_induction H s

theorem strong_induction_on_eq {p : Finset α → Sort _} (s : Finset α) (H : ∀ s, (∀ t (_ : t ⊂ s), p t) → p s) :
  s.strong_induction_on H = H s fun t h => t.strong_induction_on H :=
  by 
    dunfold strong_induction_on 
    rw [strong_induction]

@[elab_as_eliminator]
theorem case_strong_induction_on [DecidableEq α] {p : Finset α → Prop} (s : Finset α) (h₀ : p ∅)
  (h₁ : ∀ a s, a ∉ s → (∀ t (_ : t ⊆ s), p t) → p (insert a s)) : p s :=
  Finset.strongInductionOn s$
    fun s =>
      (Finset.induction_on s fun _ => h₀)$
        fun a s n _ ih => h₁ a s n$ fun t ss => ih _ (lt_of_le_of_ltₓ ss (ssubset_insert n) : t < _)

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all finsets `s` of
cardinality less than `n`, starting from finsets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strong_downward_induction {p : Finset α → Sort _} {n : ℕ}
  (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  ∀ (s : Finset α), s.card ≤ n → p s
| s =>
  H s
    fun t ht h =>
      have  : n - card t < n - card s := (tsub_lt_tsub_iff_left_of_le ht).2 (Finset.card_lt_card h)
      strong_downward_induction t ht

theorem strong_downward_induction_eq {p : Finset α → Sort _} {n : ℕ}
  (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) (s : Finset α) :
  strong_downward_induction H s = H s fun t ht hst => strong_downward_induction H t ht :=
  by 
    rw [strong_downward_induction]

/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_eliminator]
def strong_downward_induction_on {p : Finset α → Sort _} {n : ℕ} :
  ∀ (s : Finset α), (∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) → s.card ≤ n → p s :=
  fun s H => strong_downward_induction H s

theorem strong_downward_induction_on_eq {p : Finset α → Sort _} (s : Finset α) {n : ℕ}
  (H : ∀ t₁, (∀ {t₂ : Finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  s.strong_downward_induction_on H = H s fun t ht h => t.strong_downward_induction_on H ht :=
  by 
    dunfold strong_downward_induction_on 
    rw [strong_downward_induction]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem card_congr
{s : finset α}
{t : finset β}
(f : ∀ a «expr ∈ » s, β)
(h₁ : ∀ a ha, «expr ∈ »(f a ha, t))
(h₂ : ∀ a b ha hb, «expr = »(f a ha, f b hb) → «expr = »(a, b))
(h₃ : ∀ b «expr ∈ » t, «expr∃ , »((a ha), «expr = »(f a ha, b))) : «expr = »(s.card, t.card) :=
by haveI [] [] [":=", expr classical.prop_decidable]; exact [expr calc
   «expr = »(s.card, s.attach.card) : card_attach.symm
   «expr = »(..., (s.attach.image (λ
      a : {a // «expr ∈ »(a, s)}, f a.1 a.2)).card) : eq.symm (card_image_of_injective _ (λ
     a b h, subtype.eq (h₂ _ _ _ _ h)))
   «expr = »(..., t.card) : congr_arg card «expr $ »(finset.ext, λ
    b, ⟨λ h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in
     «expr ▸ »(ha₂, h₁ _ _), λ h, let ⟨a, ha₁, ha₂⟩ := h₃ b h in
     mem_image.2 ⟨⟨a, ha₁⟩, by simp [] [] [] ["[", expr ha₂, "]"] [] []⟩⟩)]

theorem card_union_add_card_inter [DecidableEq α] (s t : Finset α) : ((s ∪ t).card+(s ∩ t).card) = s.card+t.card :=
  Finset.induction_on t
      (by 
        simp )$
    fun a r har =>
      by 
        byCases' a ∈ s <;> simp  <;> cc

theorem card_union_le [DecidableEq α] (s t : Finset α) : (s ∪ t).card ≤ s.card+t.card :=
  card_union_add_card_inter s t ▸ Nat.le_add_rightₓ _ _

theorem card_union_eq [DecidableEq α] {s t : Finset α} (h : Disjoint s t) : (s ∪ t).card = s.card+t.card :=
  by 
    rw [←card_union_add_card_inter]
    convert (add_zeroₓ _).symm 
    rw [card_eq_zero]
    rwa [disjoint_iff] at h

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem surj_on_of_inj_on_of_card_le
{s : finset α}
{t : finset β}
(f : ∀ a «expr ∈ » s, β)
(hf : ∀ a ha, «expr ∈ »(f a ha, t))
(hinj : ∀ a₁ a₂ ha₁ ha₂, «expr = »(f a₁ ha₁, f a₂ ha₂) → «expr = »(a₁, a₂))
(hst : «expr ≤ »(card t, card s)) : ∀ b «expr ∈ » t, «expr∃ , »((a ha), «expr = »(b, f a ha)) :=
by haveI [] [] [":=", expr classical.dec_eq β]; exact [expr λ
 b
 hb, have h : «expr = »(card (image (λ
    a : {a // «expr ∈ »(a, s)}, f a a.prop) (attach s)), card s), from «expr ▸ »(@card_attach _ s, card_image_of_injective _ (λ
   ⟨a₁, ha₁⟩
   ⟨a₂, ha₂⟩
   (h), «expr $ »(subtype.eq, hinj _ _ _ _ h))),
 have h₁ : «expr = »(image (λ
   a : {a // «expr ∈ »(a, s)}, f a a.prop) s.attach, t) := eq_of_subset_of_card_le (λ
  b h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in
  «expr ▸ »(ha₂, hf _ _)) (by simp [] [] [] ["[", expr hst, ",", expr h, "]"] [] []),
 begin
   rw ["<-", expr h₁] ["at", ident hb],
   rcases [expr mem_image.1 hb, "with", "⟨", ident a, ",", ident ha₁, ",", ident ha₂, "⟩"],
   exact [expr ⟨a, a.2, ha₂.symm⟩]
 end]

open Function

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem inj_on_of_surj_on_of_card_le
{s : finset α}
{t : finset β}
(f : ∀ a «expr ∈ » s, β)
(hf : ∀ a ha, «expr ∈ »(f a ha, t))
(hsurj : ∀ b «expr ∈ » t, «expr∃ , »((a ha), «expr = »(b, f a ha)))
(hst : «expr ≤ »(card s, card t))
{{a₁ a₂}}
(ha₁ : «expr ∈ »(a₁, s))
(ha₂ : «expr ∈ »(a₂, s))
(ha₁a₂ : «expr = »(f a₁ ha₁, f a₂ ha₂)) : «expr = »(a₁, a₂) :=
by haveI [] [":", expr inhabited {x // «expr ∈ »(x, s)}] [":=", expr ⟨⟨a₁, ha₁⟩⟩]; exact [expr let f' : {x // «expr ∈ »(x, s)} → {x // «expr ∈ »(x, t)} := λ
     x, ⟨f x.1 x.2, hf x.1 x.2⟩ in
 let g : {x // «expr ∈ »(x, t)} → {x // «expr ∈ »(x, s)} := @surj_inv _ _ f' (λ x, let ⟨y, hy₁, hy₂⟩ := hsurj x.1 x.2 in
      ⟨⟨y, hy₁⟩, subtype.eq hy₂.symm⟩) in
 have hg : injective g, from injective_surj_inv _,
 have hsg : surjective g, from λ
 x, let ⟨y, hy⟩ := surj_on_of_inj_on_of_card_le (λ
      (x : {x // «expr ∈ »(x, t)})
      (hx : «expr ∈ »(x, t.attach)), g x) (λ
      x
      _, show «expr ∈ »(g x, s.attach), from mem_attach _ _) (λ
      x y _ _ hxy, hg hxy) (by simpa [] [] [] [] [] []) x (mem_attach _ _) in
 ⟨y, hy.snd.symm⟩,
 have hif : injective f', from (left_inverse_of_surjective_of_right_inverse hsg (right_inverse_surj_inv _)).injective,
 subtype.ext_iff_val.1 (@hif ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ (subtype.eq ha₁a₂))]

end Card

section ToList

/-- Produce a list of the elements in the finite set using choice. -/
@[reducible]
noncomputable def to_list (s : Finset α) : List α :=
  s.1.toList

theorem nodup_to_list (s : Finset α) : s.to_list.nodup :=
  by 
    rw [to_list, ←Multiset.coe_nodup, Multiset.coe_to_list]
    exact s.nodup

@[simp]
theorem mem_to_list {a : α} (s : Finset α) : a ∈ s.to_list ↔ a ∈ s :=
  by 
    rw [to_list, ←Multiset.mem_coe, Multiset.coe_to_list]
    exact Iff.rfl

@[simp]
theorem length_to_list (s : Finset α) : s.to_list.length = s.card :=
  by 
    rw [to_list, ←Multiset.coe_card, Multiset.coe_to_list]
    rfl

@[simp]
theorem to_list_empty : (∅ : Finset α).toList = [] :=
  by 
    simp [to_list]

@[simp, normCast]
theorem coe_to_list (s : Finset α) : (s.to_list : Multiset α) = s.val :=
  by 
    classical 
    ext 
    simp 

@[simp]
theorem to_list_to_finset [DecidableEq α] (s : Finset α) : s.to_list.to_finset = s :=
  by 
    ext 
    simp 

theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) : ∃ l : List α, l.nodup ∧ l.to_finset = s :=
  ⟨s.to_list, s.nodup_to_list, s.to_list_to_finset⟩

end ToList

section BUnion

/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/


variable[DecidableEq β]{s : Finset α}{t : α → Finset β}

/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bUnion (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a => (t a).1).toFinset

@[simp]
theorem bUnion_val (s : Finset α) (t : α → Finset β) : (s.bUnion t).1 = (s.1.bind fun a => (t a).1).eraseDup :=
  rfl

@[simp]
theorem bUnion_empty : Finset.bUnion ∅ t = ∅ :=
  rfl

@[simp]
theorem mem_bUnion {b : β} : b ∈ s.bUnion t ↔ ∃ (a : _)(_ : a ∈ s), b ∈ t a :=
  by 
    simp only [mem_def, bUnion_val, mem_erase_dup, mem_bind, exists_prop]

@[simp]
theorem bUnion_insert [DecidableEq α] {a : α} : (insert a s).bUnion t = t a ∪ s.bUnion t :=
  ext$
    fun x =>
      by 
        simp only [mem_bUnion, exists_prop, mem_union, mem_insert, or_and_distrib_right, exists_or_distrib,
          exists_eq_left]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bUnion_congr
{s₁ s₂ : finset α}
{t₁ t₂ : α → finset β}
(hs : «expr = »(s₁, s₂))
(ht : ∀ a «expr ∈ » s₁, «expr = »(t₁ a, t₂ a)) : «expr = »(s₁.bUnion t₁, s₂.bUnion t₂) :=
«expr $ »(ext, λ x, by simp [] [] [] ["[", expr hs, ",", expr ht, "]"] [] [] { contextual := tt })

theorem bUnion_subset {s' : Finset β} : s.bUnion t ⊆ s' ↔ ∀ x (_ : x ∈ s), t x ⊆ s' :=
  by 
    simp only [subset_iff, mem_bUnion] <;> exact ⟨fun H a ha b hb => H ⟨a, ha, hb⟩, fun H b ⟨a, ha, hb⟩ => H a ha hb⟩

@[simp]
theorem singleton_bUnion {a : α} : Finset.bUnion {a} t = t a :=
  by 
    classical 
    rw [←insert_emptyc_eq, bUnion_insert, bUnion_empty, union_empty]

theorem bUnion_inter (s : Finset α) (f : α → Finset β) (t : Finset β) : s.bUnion f ∩ t = s.bUnion fun x => f x ∩ t :=
  by 
    ext x 
    simp only [mem_bUnion, mem_inter]
    tauto

theorem inter_bUnion (t : Finset β) (s : Finset α) (f : α → Finset β) : t ∩ s.bUnion f = s.bUnion fun x => t ∩ f x :=
  by 
    rw [inter_comm, bUnion_inter] <;> simp [inter_comm]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem image_bUnion
[decidable_eq γ]
{f : α → β}
{s : finset α}
{t : β → finset γ} : «expr = »((s.image f).bUnion t, s.bUnion (λ a, t (f a))) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr finset.induction_on s rfl (λ
  a s has ih, by simp [] [] ["only"] ["[", expr image_insert, ",", expr bUnion_insert, ",", expr ih, "]"] [] [])]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bUnion_image
[decidable_eq γ]
{s : finset α}
{t : α → finset β}
{f : β → γ} : «expr = »((s.bUnion t).image f, s.bUnion (λ a, (t a).image f)) :=
by haveI [] [] [":=", expr classical.dec_eq α]; exact [expr finset.induction_on s rfl (λ
  a s has ih, by simp [] [] ["only"] ["[", expr bUnion_insert, ",", expr image_union, ",", expr ih, "]"] [] [])]

theorem bUnion_bUnion [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
  (s.bUnion f).bUnion g = s.bUnion fun a => (f a).bUnion g :=
  by 
    ext 
    simp only [Finset.mem_bUnion, exists_prop]
    simpRw [←exists_and_distrib_right, ←exists_and_distrib_left, and_assoc]
    rw [exists_comm]

theorem bind_to_finset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
  (s.bind t).toFinset = s.to_finset.bUnion fun a => (t a).toFinset :=
  ext$
    fun x =>
      by 
        simp only [Multiset.mem_to_finset, mem_bUnion, Multiset.mem_bind, exists_prop]

theorem bUnion_mono {t₁ t₂ : α → Finset β} (h : ∀ a (_ : a ∈ s), t₁ a ⊆ t₂ a) : s.bUnion t₁ ⊆ s.bUnion t₂ :=
  have  : ∀ b a, a ∈ s → b ∈ t₁ a → ∃ a : α, a ∈ s ∧ b ∈ t₂ a :=
    fun b a ha hb => ⟨a, ha, Finset.mem_of_subset (h a ha) hb⟩
  by 
    simpa only [subset_iff, mem_bUnion, exists_imp_distrib, and_imp, exists_prop]

theorem bUnion_subset_bUnion_of_subset_left {α : Type _} {s₁ s₂ : Finset α} (t : α → Finset β) (h : s₁ ⊆ s₂) :
  s₁.bUnion t ⊆ s₂.bUnion t :=
  by 
    intro x 
    simp only [and_imp, mem_bUnion, exists_prop]
    exact Exists.impₓ fun a ha => ⟨h ha.1, ha.2⟩

theorem subset_bUnion_of_mem {s : Finset α} (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.bUnion u :=
  by 
    apply subset.trans _ (bUnion_subset_bUnion_of_subset_left u (singleton_subset_iff.2 xs))
    exact subset_of_eq singleton_bUnion.symm

@[simp]
theorem bUnion_subset_iff_forall_subset {α β : Type _} [DecidableEq β] {s : Finset α} {t : Finset β}
  {f : α → Finset β} : s.bUnion f ⊆ t ↔ ∀ x (_ : x ∈ s), f x ⊆ t :=
  ⟨fun h x hx => (subset_bUnion_of_mem f hx).trans h,
    fun h x hx =>
      let ⟨a, ha₁, ha₂⟩ := mem_bUnion.mp hx 
      h _ ha₁ ha₂⟩

theorem bUnion_singleton {f : α → β} : (s.bUnion fun a => {f a}) = s.image f :=
  ext$
    fun x =>
      by 
        simp only [mem_bUnion, mem_image, mem_singleton, eq_comm]

@[simp]
theorem bUnion_singleton_eq_self [DecidableEq α] : s.bUnion (singleton : α → Finset α) = s :=
  by 
    rw [bUnion_singleton]
    exact image_id

theorem bUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
  (h : ∀ x (_ : x ∈ s), f x ∈ t) : (t.bUnion fun a => s.filter$ fun c => f c = a) = s :=
  ext$
    fun b =>
      by 
        simpa using h b

theorem image_bUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
  ((s.image g).bUnion fun a => s.filter$ fun c => g c = a) = s :=
  bUnion_filter_eq_of_maps_to fun x => mem_image_of_mem g

theorem erase_bUnion (f : α → Finset β) (s : Finset α) (b : β) :
  (s.bUnion f).erase b = s.bUnion fun x => (f x).erase b :=
  by 
    ext 
    simp only [Finset.mem_bUnion, iff_selfₓ, exists_and_distrib_left, Finset.mem_erase]

@[simp]
theorem bUnion_nonempty : (s.bUnion t).Nonempty ↔ ∃ (x : _)(_ : x ∈ s), (t x).Nonempty :=
  by 
    simp [Finset.Nonempty, ←exists_and_distrib_left, @exists_swap α]

theorem nonempty.bUnion (hs : s.nonempty) (ht : ∀ x (_ : x ∈ s), (t x).Nonempty) : (s.bUnion t).Nonempty :=
  bUnion_nonempty.2$ hs.imp$ fun x hx => ⟨hx, ht x hx⟩

end BUnion

/-! ### sigma -/


section Sigma

variable{σ : α → Type _}{s : Finset α}{t : ∀ a, Finset (σ a)}

/-- `sigma s t` is the set of dependent pairs `⟨a, b⟩` such that `a ∈ s` and `b ∈ t a`. -/
protected def Sigma (s : Finset α) (t : ∀ a, Finset (σ a)) : Finset (Σa, σ a) :=
  ⟨_, nodup_sigma s.2 fun a => (t a).2⟩

@[simp]
theorem mem_sigma {p : Sigma σ} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1 :=
  mem_sigma

@[simp]
theorem sigma_nonempty : (s.sigma t).Nonempty ↔ ∃ (x : _)(_ : x ∈ s), (t x).Nonempty :=
  by 
    simp [Finset.Nonempty]

@[simp]
theorem sigma_eq_empty : s.sigma t = ∅ ↔ ∀ x (_ : x ∈ s), t x = ∅ :=
  by 
    simp only [←not_nonempty_iff_eq_empty, sigma_nonempty, not_exists]

@[mono]
theorem sigma_mono {s₁ s₂ : Finset α} {t₁ t₂ : ∀ a, Finset (σ a)} (H1 : s₁ ⊆ s₂) (H2 : ∀ a, t₁ a ⊆ t₂ a) :
  s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
  fun ⟨x, sx⟩ H =>
    let ⟨H3, H4⟩ := mem_sigma.1 H 
    mem_sigma.2 ⟨H1 H3, H2 x H4⟩

theorem sigma_eq_bUnion [DecidableEq (Σa, σ a)] (s : Finset α) (t : ∀ a, Finset (σ a)) :
  s.sigma t = s.bUnion fun a => (t a).map$ embedding.sigma_mk a :=
  by 
    ext ⟨x, y⟩
    simp [And.left_comm]

end Sigma

/-! ### disjoint -/


section Disjoint

variable[DecidableEq α]

theorem disjoint_left {s t : Finset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
  by 
    simp only [_root_.disjoint, inf_eq_inter, le_iff_subset, subset_iff, mem_inter, not_and, and_imp] <;> rfl

theorem disjoint_val {s t : Finset α} : Disjoint s t ↔ s.1.Disjoint t.1 :=
  disjoint_left

theorem disjoint_iff_inter_eq_empty {s t : Finset α} : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

instance decidable_disjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidableOfDecidableOfIff
    (by 
      infer_instance)
    eq_bot_iff

theorem disjoint_right {s t : Finset α} : Disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
  by 
    rw [Disjoint.comm, disjoint_left]

theorem disjoint_iff_ne {s t : Finset α} : Disjoint s t ↔ ∀ a (_ : a ∈ s), ∀ b (_ : b ∈ t), a ≠ b :=
  by 
    simp only [disjoint_left, imp_not_comm, forall_eq']

theorem not_disjoint_iff {s t : Finset α} : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  not_forall.trans$
    exists_congr$
      fun a =>
        by 
          rw [Finset.inf_eq_inter, Finset.mem_inter]
          exact not_not

theorem disjoint_of_subset_left {s t u : Finset α} (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun x m₁ => (disjoint_left.1 d) (h m₁)

theorem disjoint_of_subset_right {s t u : Finset α} (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left

@[simp]
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right

@[simp]
theorem disjoint_singleton_left {s : Finset α} {a : α} : Disjoint (singleton a) s ↔ a ∉ s :=
  by 
    simp only [disjoint_left, mem_singleton, forall_eq]

@[simp]
theorem disjoint_singleton_right {s : Finset α} {a : α} : Disjoint s (singleton a) ↔ a ∉ s :=
  Disjoint.comm.trans disjoint_singleton_left

@[simp]
theorem disjoint_singleton {a b : α} : Disjoint ({a} : Finset α) {b} ↔ a ≠ b :=
  by 
    rw [disjoint_singleton_left, mem_singleton]

@[simp]
theorem disjoint_insert_left {a : α} {s t : Finset α} : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t :=
  by 
    simp only [disjoint_left, mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

@[simp]
theorem disjoint_insert_right {a : α} {s t : Finset α} : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  Disjoint.comm.trans$
    by 
      rw [disjoint_insert_left, Disjoint.comm]

@[simp]
theorem disjoint_union_left {s t u : Finset α} : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u :=
  by 
    simp only [disjoint_left, mem_union, or_imp_distrib, forall_and_distrib]

@[simp]
theorem disjoint_union_right {s t u : Finset α} : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u :=
  by 
    simp only [disjoint_right, mem_union, or_imp_distrib, forall_and_distrib]

theorem sdiff_disjoint {s t : Finset α} : Disjoint (t \ s) s :=
  disjoint_left.2$ fun a ha => (mem_sdiff.1 ha).2

theorem disjoint_sdiff {s t : Finset α} : Disjoint s (t \ s) :=
  sdiff_disjoint.symm

theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

theorem sdiff_eq_self_iff_disjoint {s t : Finset α} : s \ t = s ↔ Disjoint s t :=
  by 
    rw [sdiff_eq_self, subset_empty, disjoint_iff_inter_eq_empty]

theorem sdiff_eq_self_of_disjoint {s t : Finset α} (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h

theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self

theorem disjoint_bUnion_left {ι : Type _} (s : Finset ι) (f : ι → Finset α) (t : Finset α) :
  Disjoint (s.bUnion f) t ↔ ∀ i (_ : i ∈ s), Disjoint (f i) t :=
  by 
    classical 
    refine' s.induction _ _
    ·
      simp only [forall_mem_empty_iff, bUnion_empty, disjoint_empty_left]
    ·
      intro i s his ih 
      simp only [disjoint_union_left, bUnion_insert, his, forall_mem_insert, ih]

theorem disjoint_bUnion_right {ι : Type _} (s : Finset α) (t : Finset ι) (f : ι → Finset α) :
  Disjoint s (t.bUnion f) ↔ ∀ i (_ : i ∈ t), Disjoint s (f i) :=
  by 
    simpa only [Disjoint.comm] using disjoint_bUnion_left t f s

@[simp]
theorem card_disjoint_union {s t : Finset α} (h : Disjoint s t) : card (s ∪ t) = card s+card t :=
  by 
    rw [←card_union_add_card_inter, disjoint_iff_inter_eq_empty.1 h, card_empty, add_zeroₓ]

theorem card_sdiff {s t : Finset α} (h : s ⊆ t) : card (t \ s) = card t - card s :=
  suffices card (t \ s) = card (t \ s ∪ s) - card s by 
    rwa [sdiff_union_of_subset h] at this 
  by 
    rw [card_disjoint_union sdiff_disjoint, add_tsub_cancel_right]

theorem card_sdiff_add_card {s t : Finset α} : ((s \ t).card+t.card) = (s ∪ t).card :=
  by 
    rw [←card_disjoint_union sdiff_disjoint, sdiff_union_self_eq_union]

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem disjoint_filter
{s : finset α}
{p q : α → exprProp()}
[decidable_pred p]
[decidable_pred q] : «expr ↔ »(disjoint (s.filter p) (s.filter q), ∀ x «expr ∈ » s, p x → «expr¬ »(q x)) :=
by split; simp [] [] [] ["[", expr disjoint_left, "]"] [] [] { contextual := tt }

theorem disjoint_filter_filter {s t : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
  Disjoint s t → Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)

theorem disjoint_iff_disjoint_coe {α : Type _} {a b : Finset α} [DecidableEq α] :
  Disjoint a b ↔ Disjoint («expr↑ » a : Set α) («expr↑ » b : Set α) :=
  by 
    rw [Finset.disjoint_left, Set.disjoint_left]
    rfl

theorem filter_card_add_filter_neg_card_eq_card {α : Type _} {s : Finset α} (p : α → Prop) [DecidablePred p] :
  ((s.filter p).card+(s.filter (Not ∘ p)).card) = s.card :=
  by 
    classical 
    simp [←card_union_eq, filter_union_filter_neg_eq, disjoint_filter]

end Disjoint

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Given a set A and a set B inside it, we can shrink A to any appropriate size, and keep B
inside it.
-/
theorem exists_intermediate_set
{A B : finset α}
(i : exprℕ())
(h₁ : «expr ≤ »(«expr + »(i, card B), card A))
(h₂ : «expr ⊆ »(B, A)) : «expr∃ , »((C : finset α), «expr ∧ »(«expr ⊆ »(B, C), «expr ∧ »(«expr ⊆ »(C, A), «expr = »(card C, «expr + »(i, card B))))) :=
begin
  classical,
  rcases [expr nat.le.dest h₁, "with", "⟨", ident k, ",", "_", "⟩"],
  clear [ident h₁],
  induction [expr k] [] ["with", ident k, ident ih] ["generalizing", ident A],
  { exact [expr ⟨A, h₂, subset.refl _, h.symm⟩] },
  { have [] [":", expr «expr \ »(A, B).nonempty] [],
    { rw ["[", "<-", expr card_pos, ",", expr card_sdiff h₂, ",", "<-", expr h, ",", expr nat.add_right_comm, ",", expr add_tsub_cancel_right, ",", expr nat.add_succ, "]"] [],
      apply [expr nat.succ_pos] },
    rcases [expr this, "with", "⟨", ident a, ",", ident ha, "⟩"],
    have [ident z] [":", expr «expr = »(«expr + »(«expr + »(i, card B), k), card (erase A a))] [],
    { rw ["[", expr card_erase_of_mem, ",", "<-", expr h, ",", expr nat.add_succ, ",", expr nat.pred_succ, "]"] [],
      rw [expr mem_sdiff] ["at", ident ha],
      exact [expr ha.1] },
    rcases [expr ih _ z, "with", "⟨", ident B', ",", ident hB', ",", ident B'subA', ",", ident cards, "⟩"],
    { exact [expr ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩] },
    { rintros [ident t, ident th],
      apply [expr mem_erase_of_ne_of_mem _ (h₂ th)],
      rintro [ident rfl],
      exact [expr not_mem_sdiff_of_mem_right th ha] } }
end

/-- We can shrink A to any smaller size. -/
theorem exists_smaller_set (A : Finset α) (i : ℕ) (h₁ : i ≤ card A) : ∃ B : Finset α, B ⊆ A ∧ card B = i :=
  let ⟨B, _, x₁, x₂⟩ :=
    exists_intermediate_set i
      (by 
        simpa)
      (empty_subset A)
  ⟨B, x₁, x₂⟩

-- error in Data.Finset.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_subset_or_subset_of_two_mul_lt_card
[decidable_eq α]
{X Y : finset α}
{n : exprℕ()}
(hXY : «expr < »(«expr * »(2, n), «expr ∪ »(X, Y).card)) : «expr∃ , »((C : finset α), «expr ∧ »(«expr < »(n, C.card), «expr ∨ »(«expr ⊆ »(C, X), «expr ⊆ »(C, Y)))) :=
begin
  have [ident h₁] [":", expr «expr = »(«expr ∩ »(X, «expr \ »(Y, X)).card, 0)] [":=", expr finset.card_eq_zero.mpr (finset.inter_sdiff_self X Y)],
  have [ident h₂] [":", expr «expr = »(«expr ∪ »(X, Y).card, «expr + »(X.card, «expr \ »(Y, X).card))] [],
  { rw ["[", "<-", expr card_union_add_card_inter X «expr \ »(Y, X), ",", expr finset.union_sdiff_self_eq_union, ",", expr h₁, ",", expr add_zero, "]"] [] },
  rw ["[", expr h₂, ",", expr two_mul, "]"] ["at", ident hXY],
  rcases [expr lt_or_lt_of_add_lt_add hXY, "with", ident h, "|", ident h],
  { exact [expr ⟨X, h, or.inl (finset.subset.refl X)⟩] },
  { exact [expr ⟨«expr \ »(Y, X), h, or.inr (finset.sdiff_subset Y X)⟩] }
end

/-- `finset.fin_range k` is the finset `{0, 1, ..., k-1}`, as a `finset (fin k)`. -/
def fin_range (k : ℕ) : Finset (Finₓ k) :=
  ⟨List.finRange k, List.nodup_fin_range k⟩

@[simp]
theorem fin_range_card {k : ℕ} : (fin_range k).card = k :=
  by 
    simp [fin_range]

@[simp]
theorem mem_fin_range {k : ℕ} (m : Finₓ k) : m ∈ fin_range k :=
  List.mem_fin_range m

@[simp]
theorem coe_fin_range (k : ℕ) : (fin_range k : Set (Finₓ k)) = Set.Univ :=
  Set.eq_univ_of_forall mem_fin_range

/-- Given a finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding finset in `fin n`
is `s.attach_fin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attach_fin (s : Finset ℕ) {n : ℕ} (h : ∀ m (_ : m ∈ s), m < n) : Finset (Finₓ n) :=
  ⟨s.1.pmap (fun a ha => ⟨a, ha⟩) h, Multiset.nodup_pmap (fun _ _ _ _ => Finₓ.veq_of_eq) s.2⟩

@[simp]
theorem mem_attach_fin {n : ℕ} {s : Finset ℕ} (h : ∀ m (_ : m ∈ s), m < n) {a : Finₓ n} :
  a ∈ s.attach_fin h ↔ (a : ℕ) ∈ s :=
  ⟨fun h =>
      let ⟨b, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h 
      hb₂ ▸ hb₁,
    fun h => Multiset.mem_pmap.2 ⟨a, h, Finₓ.eta _ _⟩⟩

@[simp]
theorem card_attach_fin {n : ℕ} (s : Finset ℕ) (h : ∀ m (_ : m ∈ s), m < n) : (s.attach_fin h).card = s.card :=
  Multiset.card_pmap _ _ _

/-! ### choose -/


section Choose

variable(p : α → Prop)[DecidablePred p](l : Finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : ∃!a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  Multiset.chooseX p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃!a, a ∈ l ∧ p a) : α :=
  choose_x p l hp

theorem choose_spec (hp : ∃!a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (choose_x p l hp).property

theorem choose_mem (hp : ∃!a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃!a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

theorem lt_wf {α} : WellFounded (@LT.lt (Finset α) _) :=
  have H : Subrelation (@LT.lt (Finset α) _) (InvImage (· < ·) card) := fun x y hxy => card_lt_card hxy 
  Subrelation.wfₓ H$ InvImage.wfₓ _$ Nat.lt_wf

end Finset

namespace Equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finset_congr (e : α ≃ β) : Finset α ≃ Finset β :=
  { toFun := fun s => s.map e.to_embedding, invFun := fun s => s.map e.symm.to_embedding,
    left_inv :=
      fun s =>
        by 
          simp [Finset.map_map],
    right_inv :=
      fun s =>
        by 
          simp [Finset.map_map] }

@[simp]
theorem finset_congr_apply (e : α ≃ β) (s : Finset α) : e.finset_congr s = s.map e.to_embedding :=
  rfl

@[simp]
theorem finset_congr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ :=
  by 
    ext 
    simp 

@[simp]
theorem finset_congr_symm (e : α ≃ β) : e.finset_congr.symm = e.symm.finset_congr :=
  rfl

@[simp]
theorem finset_congr_trans (e : α ≃ β) (e' : β ≃ γ) : e.finset_congr.trans e'.finset_congr = (e.trans e').finsetCongr :=
  by 
    ext 
    simp [-Finset.mem_map, -Equiv.trans_to_embedding]

end Equiv

namespace Multiset

variable[DecidableEq α]

theorem to_finset_card_of_nodup {l : Multiset α} (h : l.nodup) : l.to_finset.card = l.card :=
  congr_argₓ card$ Multiset.erase_dup_eq_self.mpr h

theorem disjoint_to_finset {m1 m2 : Multiset α} : _root_.disjoint m1.to_finset m2.to_finset ↔ m1.disjoint m2 :=
  by 
    rw [Finset.disjoint_iff_ne]
    split 
    ·
      intro h 
      intro a ha1 ha2 
      rw [←Multiset.mem_to_finset] at ha1 ha2 
      exact h _ ha1 _ ha2 rfl
    ·
      rintro h a ha b hb rfl 
      rw [Multiset.mem_to_finset] at ha hb 
      exact h ha hb

end Multiset

namespace List

variable[DecidableEq α]

theorem to_finset_card_of_nodup {l : List α} (h : l.nodup) : l.to_finset.card = l.length :=
  Multiset.to_finset_card_of_nodup h

theorem disjoint_to_finset_iff_disjoint {l l' : List α} : _root_.disjoint l.to_finset l'.to_finset ↔ l.disjoint l' :=
  Multiset.disjoint_to_finset

end List

