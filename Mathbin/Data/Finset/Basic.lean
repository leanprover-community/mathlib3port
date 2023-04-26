/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro

! This file was ported from Lean 3 source module data.finset.basic
! leanprover-community/mathlib commit 9ac7c0c8c4d7a535ec3e5b34b8859aab9233b2f4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.FinsetOps
import Mathbin.Tactic.Apply
import Mathbin.Tactic.NthRewrite.Default
import Mathbin.Tactic.Monotonicity.Default

/-!
# Finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

`finset.card`, the size of a finset is defined in `data.finset.card`. This is then used to define
`fintype.card`, the size of a type.

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

### Finset constructions

* `singleton`: Denoted by `{a}`; the finset consisting of one element.
* `finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.
* `finset.attach`: Given `s : finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `finset.filter`: Given a predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`order.lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and `⊤` is
called `top` with `⊤ = univ`.

* `finset.has_subset`: Lots of API about lattices, otherwise behaves exactly as one would expect.
* `finset.has_union`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `finset.sup`/`finset.bUnion` for finite unions.
* `finset.has_inter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  See `finset.inf` for finite intersections.
* `finset.disj_union`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disj_union t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.

### Operations on two or more finsets

* `insert` and `finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.
* `finset.has_union`: see "The lattice structure on subsets of finsets"
* `finset.has_inter`: see "The lattice structure on subsets of finsets"
* `finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `finset.has_sdiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `finset.product`: Given finsets of `α` and `β`, defines finsets of `α × β`.
  For arbitrary dependent products, see `data.finset.pi`.
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

variable {α : Type _} {β : Type _} {γ : Type _}

#print Finset /-
/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type _) where
  val : Multiset α
  Nodup : Nodup val
#align finset Finset
-/

#print Multiset.canLiftFinset /-
instance Multiset.canLiftFinset {α} : CanLift (Multiset α) (Finset α) Finset.val Multiset.Nodup :=
  ⟨fun m hm => ⟨⟨m, hm⟩, rfl⟩⟩
#align multiset.can_lift_finset Multiset.canLiftFinset
-/

namespace Finset

#print Finset.eq_of_veq /-
theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t
  | ⟨s, _⟩, ⟨t, _⟩, rfl => rfl
#align finset.eq_of_veq Finset.eq_of_veq
-/

#print Finset.val_injective /-
theorem val_injective : Injective (val : Finset α → Multiset α) := fun _ _ => eq_of_veq
#align finset.val_injective Finset.val_injective
-/

#print Finset.val_inj /-
@[simp]
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  val_injective.eq_iff
#align finset.val_inj Finset.val_inj
-/

#print Finset.dedup_eq_self /-
@[simp]
theorem dedup_eq_self [DecidableEq α] (s : Finset α) : dedup s.1 = s.1 :=
  s.2.dedup
#align finset.dedup_eq_self Finset.dedup_eq_self
-/

#print Finset.decidableEq /-
instance decidableEq [DecidableEq α] : DecidableEq (Finset α)
  | s₁, s₂ => decidable_of_iff _ val_inj
#align finset.has_decidable_eq Finset.decidableEq
-/

/-! ### membership -/


instance : Membership α (Finset α) :=
  ⟨fun a s => a ∈ s.1⟩

#print Finset.mem_def /-
theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl
#align finset.mem_def Finset.mem_def
-/

#print Finset.mem_val /-
@[simp]
theorem mem_val {a : α} {s : Finset α} : a ∈ s.1 ↔ a ∈ s :=
  Iff.rfl
#align finset.mem_val Finset.mem_val
-/

#print Finset.mem_mk /-
@[simp]
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl
#align finset.mem_mk Finset.mem_mk
-/

#print Finset.decidableMem /-
instance decidableMem [h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _
#align finset.decidable_mem Finset.decidableMem
-/

/-! ### set coercion -/


/-- Convert a finset to a set in the natural way. -/
instance : CoeTC (Finset α) (Set α) :=
  ⟨fun s => { x | x ∈ s }⟩

#print Finset.mem_coe /-
@[simp, norm_cast]
theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl
#align finset.mem_coe Finset.mem_coe
-/

#print Finset.setOf_mem /-
@[simp]
theorem setOf_mem {α} {s : Finset α} : { a | a ∈ s } = s :=
  rfl
#align finset.set_of_mem Finset.setOf_mem
-/

#print Finset.coe_mem /-
@[simp]
theorem coe_mem {s : Finset α} (x : (s : Set α)) : ↑x ∈ s :=
  x.2
#align finset.coe_mem Finset.coe_mem
-/

#print Finset.mk_coe /-
@[simp]
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _
#align finset.mk_coe Finset.mk_coe
-/

#print Finset.decidableMem' /-
instance decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ (s : Set α)) :=
  s.decidableMem _
#align finset.decidable_mem' Finset.decidableMem'
-/

/-! ### extensionality -/


#print Finset.ext_iff /-
theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
  val_inj.symm.trans <| s₁.Nodup.ext s₂.Nodup
#align finset.ext_iff Finset.ext_iff
-/

#print Finset.ext /-
@[ext]
theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  ext_iff.2
#align finset.ext Finset.ext
-/

#print Finset.coe_inj /-
@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  Set.ext_iff.trans ext_iff.symm
#align finset.coe_inj Finset.coe_inj
-/

#print Finset.coe_injective /-
theorem coe_injective {α} : Injective (coe : Finset α → Set α) := fun s t => coe_inj.1
#align finset.coe_injective Finset.coe_injective
-/

/-! ### type coercion -/


/-- Coercion from a finset to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Finset α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

#print Finset.forall_coe /-
@[simp]
protected theorem forall_coe {α : Type _} (s : Finset α) (p : s → Prop) :
    (∀ x : s, p x) ↔ ∀ (x : α) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
#align finset.forall_coe Finset.forall_coe
-/

#print Finset.exists_coe /-
@[simp]
protected theorem exists_coe {α : Type _} (s : Finset α) (p : s → Prop) :
    (∃ x : s, p x) ↔ ∃ (x : α)(h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
#align finset.exists_coe Finset.exists_coe
-/

#print Finset.PiFinsetCoe.canLift /-
instance PiFinsetCoe.canLift (ι : Type _) (α : ∀ i : ι, Type _) [ne : ∀ i, Nonempty (α i)]
    (s : Finset ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α (· ∈ s)
#align finset.pi_finset_coe.can_lift Finset.PiFinsetCoe.canLift
-/

#print Finset.PiFinsetCoe.canLift' /-
instance PiFinsetCoe.canLift' (ι α : Type _) [ne : Nonempty α] (s : Finset ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiFinsetCoe.canLift ι (fun _ => α) s
#align finset.pi_finset_coe.can_lift' Finset.PiFinsetCoe.canLift'
-/

#print Finset.FinsetCoe.canLift /-
instance FinsetCoe.canLift (s : Finset α) : CanLift α s coe fun a => a ∈ s
    where prf a ha := ⟨⟨a, ha⟩, rfl⟩
#align finset.finset_coe.can_lift Finset.FinsetCoe.canLift
-/

#print Finset.coe_sort_coe /-
@[simp, norm_cast]
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl
#align finset.coe_sort_coe Finset.coe_sort_coe
-/

/-! ### Subset and strict subset relations -/


section Subset

variable {s t : Finset α}

instance : HasSubset (Finset α) :=
  ⟨fun s t => ∀ ⦃a⦄, a ∈ s → a ∈ t⟩

instance : HasSSubset (Finset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩

instance : PartialOrder (Finset α) where
  le := (· ⊆ ·)
  lt := (· ⊂ ·)
  le_refl s a := id
  le_trans s t u hst htu a ha := htu <| hst ha
  le_antisymm s t hst hts := ext fun a => ⟨@hst _, @hts _⟩

instance : IsRefl (Finset α) (· ⊆ ·) :=
  LE.le.isRefl

instance : IsTrans (Finset α) (· ⊆ ·) :=
  LE.le.isTrans

instance : IsAntisymm (Finset α) (· ⊆ ·) :=
  LE.le.isAntisymm

instance : IsIrrefl (Finset α) (· ⊂ ·) :=
  LT.lt.isIrrefl

instance : IsTrans (Finset α) (· ⊂ ·) :=
  LT.lt.isTrans

instance : IsAsymm (Finset α) (· ⊂ ·) :=
  LT.lt.isAsymm

instance : IsNonstrictStrictOrder (Finset α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

#print Finset.subset_def /-
theorem subset_def : s ⊆ t ↔ s.1 ⊆ t.1 :=
  Iff.rfl
#align finset.subset_def Finset.subset_def
-/

#print Finset.ssubset_def /-
theorem ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬t ⊆ s :=
  Iff.rfl
#align finset.ssubset_def Finset.ssubset_def
-/

#print Finset.Subset.refl /-
@[simp]
theorem Subset.refl (s : Finset α) : s ⊆ s :=
  Subset.refl _
#align finset.subset.refl Finset.Subset.refl
-/

#print Finset.Subset.rfl /-
protected theorem Subset.rfl {s : Finset α} : s ⊆ s :=
  Subset.refl _
#align finset.subset.rfl Finset.Subset.rfl
-/

#print Finset.subset_of_eq /-
protected theorem subset_of_eq {s t : Finset α} (h : s = t) : s ⊆ t :=
  h ▸ Subset.refl _
#align finset.subset_of_eq Finset.subset_of_eq
-/

#print Finset.Subset.trans /-
theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  Subset.trans
#align finset.subset.trans Finset.Subset.trans
-/

#print Finset.Superset.trans /-
theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ := fun h' h =>
  Subset.trans h h'
#align finset.superset.trans Finset.Superset.trans
-/

#print Finset.mem_of_subset /-
theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  mem_of_subset
#align finset.mem_of_subset Finset.mem_of_subset
-/

#print Finset.not_mem_mono /-
theorem not_mem_mono {s t : Finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s :=
  mt <| @h _
#align finset.not_mem_mono Finset.not_mem_mono
-/

#print Finset.Subset.antisymm /-
theorem Subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun a => ⟨@H₁ a, @H₂ a⟩
#align finset.subset.antisymm Finset.Subset.antisymm
-/

#print Finset.subset_iff /-
theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl
#align finset.subset_iff Finset.subset_iff
-/

#print Finset.coe_subset /-
@[simp, norm_cast]
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊆ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl
#align finset.coe_subset Finset.coe_subset
-/

/- warning: finset.val_le_iff -> Finset.val_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Finset.val.{u1} α s₁) (Finset.val.{u1} α s₂)) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Finset.val.{u1} α s₁) (Finset.val.{u1} α s₂)) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align finset.val_le_iff Finset.val_le_iffₓ'. -/
@[simp]
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ :=
  le_iff_subset s₁.2
#align finset.val_le_iff Finset.val_le_iff

#print Finset.Subset.antisymm_iff /-
theorem Subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iff
#align finset.subset.antisymm_iff Finset.Subset.antisymm_iff
-/

/- warning: finset.not_subset -> Finset.not_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x t))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x t))))
Case conversion may be inaccurate. Consider using '#align finset.not_subset Finset.not_subsetₓ'. -/
theorem not_subset : ¬s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by simp only [← coe_subset, Set.not_subset, mem_coe]
#align finset.not_subset Finset.not_subset

#print Finset.le_eq_subset /-
@[simp]
theorem le_eq_subset : ((· ≤ ·) : Finset α → Finset α → Prop) = (· ⊆ ·) :=
  rfl
#align finset.le_eq_subset Finset.le_eq_subset
-/

#print Finset.lt_eq_subset /-
@[simp]
theorem lt_eq_subset : ((· < ·) : Finset α → Finset α → Prop) = (· ⊂ ·) :=
  rfl
#align finset.lt_eq_subset Finset.lt_eq_subset
-/

#print Finset.le_iff_subset /-
theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl
#align finset.le_iff_subset Finset.le_iff_subset
-/

#print Finset.lt_iff_ssubset /-
theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl
#align finset.lt_iff_ssubset Finset.lt_iff_ssubset
-/

/- warning: finset.coe_ssubset -> Finset.coe_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂)) (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s₁ s₂)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (Finset.toSet.{u1} α s₁) (Finset.toSet.{u1} α s₂)) (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align finset.coe_ssubset Finset.coe_ssubsetₓ'. -/
@[simp, norm_cast]
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
  show (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁ by simp only [Set.ssubset_def, Finset.coe_subset]
#align finset.coe_ssubset Finset.coe_ssubset

/- warning: finset.val_lt_iff -> Finset.val_lt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Finset.val.{u1} α s₁) (Finset.val.{u1} α s₂)) (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s₁ s₂)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (LT.lt.{u1} (Multiset.{u1} α) (Preorder.toLT.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Finset.val.{u1} α s₁) (Finset.val.{u1} α s₂)) (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align finset.val_lt_iff Finset.val_lt_iffₓ'. -/
@[simp]
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff <| not_congr val_le_iff
#align finset.val_lt_iff Finset.val_lt_iff

#print Finset.ssubset_iff_subset_ne /-
theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne _ _ s t
#align finset.ssubset_iff_subset_ne Finset.ssubset_iff_subset_ne
-/

/- warning: finset.ssubset_iff_of_subset -> Finset.ssubset_iff_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂) -> (Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s₁ s₂) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₂) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₂) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₁)))))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s₁ s₂) -> (Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s₁ s₂) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s₂) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s₁)))))
Case conversion may be inaccurate. Consider using '#align finset.ssubset_iff_of_subset Finset.ssubset_iff_of_subsetₓ'. -/
theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
  Set.ssubset_iff_of_subset h
#align finset.ssubset_iff_of_subset Finset.ssubset_iff_of_subset

#print Finset.ssubset_of_ssubset_of_subset /-
theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃
#align finset.ssubset_of_ssubset_of_subset Finset.ssubset_of_ssubset_of_subset
-/

#print Finset.ssubset_of_subset_of_ssubset /-
theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
    s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃
#align finset.ssubset_of_subset_of_ssubset Finset.ssubset_of_subset_of_ssubset
-/

/- warning: finset.exists_of_ssubset -> Finset.exists_of_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s₁ s₂) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₂) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₂) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s₁))))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s₁ s₂) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s₂) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s₁))))
Case conversion may be inaccurate. Consider using '#align finset.exists_of_ssubset Finset.exists_of_ssubsetₓ'. -/
theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : ∃ x ∈ s₂, x ∉ s₁ :=
  Set.exists_of_ssubset h
#align finset.exists_of_ssubset Finset.exists_of_ssubset

#print Finset.isWellFounded_ssubset /-
instance isWellFounded_ssubset : IsWellFounded (Finset α) (· ⊂ ·) :=
  Subrelation.isWellFounded (InvImage _ _) fun _ _ => val_lt_iff.2
#align finset.is_well_founded_ssubset Finset.isWellFounded_ssubset
-/

#print Finset.wellFoundedLT /-
instance wellFoundedLT : WellFoundedLT (Finset α) :=
  Finset.isWellFounded_ssubset
#align finset.is_well_founded_lt Finset.wellFoundedLT
-/

end Subset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] subset.trans superset.trans

/-! ### Order embedding from `finset α` to `set α` -/


#print Finset.coeEmb /-
/-- Coercion to `set α` as an `order_embedding`. -/
def coeEmb : Finset α ↪o Set α :=
  ⟨⟨coe, coe_injective⟩, fun s t => coe_subset⟩
#align finset.coe_emb Finset.coeEmb
-/

/- warning: finset.coe_coe_emb -> Finset.coe_coeEmb is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Finset.{u1} α) -> (Set.{u1} α)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Set.hasLe.{u1} α)) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Set.{u1} α) (Set.hasLe.{u1} α))) => (Finset.{u1} α) -> (Set.{u1} α)) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Set.{u1} α) (Set.hasLe.{u1} α))) (Finset.coeEmb.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (forall (ᾰ : Finset.{u1} α), (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Finset.{u1} α) => Set.{u1} α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Set.instLESet.{u1} α)) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : Finset.{u1} α) => Set.{u1} α) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Set.instLESet.{u1} α)) (Finset.{u1} α) (Set.{u1} α) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} α) => LE.le.{u1} (Set.{u1} α) (Set.instLESet.{u1} α) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (Finset.{u1} α) (Set.{u1} α) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Set.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} α) => LE.le.{u1} (Set.{u1} α) (Set.instLESet.{u1} α) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697))) (Finset.coeEmb.{u1} α)) (Finset.toSet.{u1} α)
Case conversion may be inaccurate. Consider using '#align finset.coe_coe_emb Finset.coe_coeEmbₓ'. -/
@[simp]
theorem coe_coeEmb : ⇑(coeEmb : Finset α ↪o Set α) = coe :=
  rfl
#align finset.coe_coe_emb Finset.coe_coeEmb

/-! ### Nonempty -/


#print Finset.Nonempty /-
/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Finset α) : Prop :=
  ∃ x : α, x ∈ s
#align finset.nonempty Finset.Nonempty
-/

#print Finset.decidableNonempty /-
instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
  decidable_of_iff (∃ a ∈ s, True) <| by simp_rw [exists_prop, and_true_iff, Finset.Nonempty]
#align finset.decidable_nonempty Finset.decidableNonempty
-/

#print Finset.coe_nonempty /-
@[simp, norm_cast]
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty :=
  Iff.rfl
#align finset.coe_nonempty Finset.coe_nonempty
-/

#print Finset.nonempty_coe_sort /-
@[simp]
theorem nonempty_coe_sort {s : Finset α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype
#align finset.nonempty_coe_sort Finset.nonempty_coe_sort
-/

alias coe_nonempty ↔ _ nonempty.to_set
#align finset.nonempty.to_set Finset.Nonempty.to_set

alias nonempty_coe_sort ↔ _ nonempty.coe_sort
#align finset.nonempty.coe_sort Finset.Nonempty.coe_sort

#print Finset.Nonempty.bex /-
theorem Nonempty.bex {s : Finset α} (h : s.Nonempty) : ∃ x : α, x ∈ s :=
  h
#align finset.nonempty.bex Finset.Nonempty.bex
-/

#print Finset.Nonempty.mono /-
theorem Nonempty.mono {s t : Finset α} (hst : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  Set.Nonempty.mono hst hs
#align finset.nonempty.mono Finset.Nonempty.mono
-/

#print Finset.Nonempty.forall_const /-
theorem Nonempty.forall_const {s : Finset α} (h : s.Nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h x hx => h⟩
#align finset.nonempty.forall_const Finset.Nonempty.forall_const
-/

#print Finset.Nonempty.to_subtype /-
theorem Nonempty.to_subtype {s : Finset α} : s.Nonempty → Nonempty s :=
  nonempty_coe_sort.2
#align finset.nonempty.to_subtype Finset.Nonempty.to_subtype
-/

#print Finset.Nonempty.to_type /-
theorem Nonempty.to_type {s : Finset α} : s.Nonempty → Nonempty α := fun ⟨x, hx⟩ => ⟨x⟩
#align finset.nonempty.to_type Finset.Nonempty.to_type
-/

/-! ### empty -/


section Empty

variable {s : Finset α}

#print Finset.empty /-
/-- The empty finset -/
protected def empty : Finset α :=
  ⟨0, nodup_zero⟩
#align finset.empty Finset.empty
-/

instance : EmptyCollection (Finset α) :=
  ⟨Finset.empty⟩

#print Finset.inhabitedFinset /-
instance inhabitedFinset : Inhabited (Finset α) :=
  ⟨∅⟩
#align finset.inhabited_finset Finset.inhabitedFinset
-/

#print Finset.empty_val /-
@[simp]
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl
#align finset.empty_val Finset.empty_val
-/

#print Finset.not_mem_empty /-
@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : Finset α) :=
  id
#align finset.not_mem_empty Finset.not_mem_empty
-/

#print Finset.not_nonempty_empty /-
@[simp]
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty := fun ⟨x, hx⟩ => not_mem_empty x hx
#align finset.not_nonempty_empty Finset.not_nonempty_empty
-/

#print Finset.mk_zero /-
@[simp]
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl
#align finset.mk_zero Finset.mk_zero
-/

#print Finset.ne_empty_of_mem /-
theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  not_mem_empty a <| e ▸ h
#align finset.ne_empty_of_mem Finset.ne_empty_of_mem
-/

#print Finset.Nonempty.ne_empty /-
theorem Nonempty.ne_empty {s : Finset α} (h : s.Nonempty) : s ≠ ∅ :=
  Exists.elim h fun a => ne_empty_of_mem
#align finset.nonempty.ne_empty Finset.Nonempty.ne_empty
-/

#print Finset.empty_subset /-
@[simp]
theorem empty_subset (s : Finset α) : ∅ ⊆ s :=
  zero_subset _
#align finset.empty_subset Finset.empty_subset
-/

#print Finset.eq_empty_of_forall_not_mem /-
theorem eq_empty_of_forall_not_mem {s : Finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_not_mem H)
#align finset.eq_empty_of_forall_not_mem Finset.eq_empty_of_forall_not_mem
-/

#print Finset.eq_empty_iff_forall_not_mem /-
theorem eq_empty_iff_forall_not_mem {s : Finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
  ⟨by rintro rfl x <;> exact id, fun h => eq_empty_of_forall_not_mem h⟩
#align finset.eq_empty_iff_forall_not_mem Finset.eq_empty_iff_forall_not_mem
-/

#print Finset.val_eq_zero /-
@[simp]
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅
#align finset.val_eq_zero Finset.val_eq_zero
-/

#print Finset.subset_empty /-
theorem subset_empty {s : Finset α} : s ⊆ ∅ ↔ s = ∅ :=
  subset_zero.trans val_eq_zero
#align finset.subset_empty Finset.subset_empty
-/

#print Finset.not_ssubset_empty /-
@[simp]
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ := fun h =>
  let ⟨x, he, hs⟩ := exists_of_ssubset h
  he
#align finset.not_ssubset_empty Finset.not_ssubset_empty
-/

#print Finset.nonempty_of_ne_empty /-
theorem nonempty_of_ne_empty {s : Finset α} (h : s ≠ ∅) : s.Nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)
#align finset.nonempty_of_ne_empty Finset.nonempty_of_ne_empty
-/

#print Finset.nonempty_iff_ne_empty /-
theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=
  ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩
#align finset.nonempty_iff_ne_empty Finset.nonempty_iff_ne_empty
-/

#print Finset.not_nonempty_iff_eq_empty /-
@[simp]
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅ :=
  nonempty_iff_ne_empty.Not.trans Classical.not_not
#align finset.not_nonempty_iff_eq_empty Finset.not_nonempty_iff_eq_empty
-/

#print Finset.eq_empty_or_nonempty /-
theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty :=
  by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)
#align finset.eq_empty_or_nonempty Finset.eq_empty_or_nonempty
-/

#print Finset.coe_empty /-
@[simp, norm_cast]
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ :=
  rfl
#align finset.coe_empty Finset.coe_empty
-/

#print Finset.coe_eq_empty /-
@[simp, norm_cast]
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by rw [← coe_empty, coe_inj]
#align finset.coe_eq_empty Finset.coe_eq_empty
-/

#print Finset.isEmpty_coe_sort /-
@[simp]
theorem isEmpty_coe_sort {s : Finset α} : IsEmpty ↥s ↔ s = ∅ := by
  simpa using @Set.isEmpty_coe_sort α s
#align finset.is_empty_coe_sort Finset.isEmpty_coe_sort
-/

instance : IsEmpty (∅ : Finset α) :=
  isEmpty_coe_sort.2 rfl

#print Finset.eq_empty_of_isEmpty /-
/-- A `finset` for an empty type is empty. -/
theorem eq_empty_of_isEmpty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_not_mem isEmptyElim
#align finset.eq_empty_of_is_empty Finset.eq_empty_of_isEmpty
-/

instance : OrderBot (Finset α) where
  bot := ∅
  bot_le := empty_subset

/- warning: finset.bot_eq_empty -> Finset.bot_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Finset.{u1} α) (Bot.bot.{u1} (Finset.{u1} α) (OrderBot.toHasBot.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.orderBot.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Finset.{u1} α) (Bot.bot.{u1} (Finset.{u1} α) (OrderBot.toBot.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.bot_eq_empty Finset.bot_eq_emptyₓ'. -/
@[simp]
theorem bot_eq_empty : (⊥ : Finset α) = ∅ :=
  rfl
#align finset.bot_eq_empty Finset.bot_eq_empty

#print Finset.empty_ssubset /-
@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm
#align finset.empty_ssubset Finset.empty_ssubset
-/

alias empty_ssubset ↔ _ nonempty.empty_ssubset
#align finset.nonempty.empty_ssubset Finset.Nonempty.empty_ssubset

end Empty

/-! ### singleton -/


section Singleton

variable {s : Finset α} {a b : α}

/-- `{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance : Singleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

#print Finset.singleton_val /-
@[simp]
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl
#align finset.singleton_val Finset.singleton_val
-/

#print Finset.mem_singleton /-
@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  mem_singleton
#align finset.mem_singleton Finset.mem_singleton
-/

#print Finset.eq_of_mem_singleton /-
theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Finset α)) : x = y :=
  mem_singleton.1 h
#align finset.eq_of_mem_singleton Finset.eq_of_mem_singleton
-/

#print Finset.not_mem_singleton /-
theorem not_mem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a ≠ b :=
  not_congr mem_singleton
#align finset.not_mem_singleton Finset.not_mem_singleton
-/

#print Finset.mem_singleton_self /-
theorem mem_singleton_self (a : α) : a ∈ ({a} : Finset α) :=
  Or.inl rfl
#align finset.mem_singleton_self Finset.mem_singleton_self
-/

#print Finset.val_eq_singleton_iff /-
@[simp]
theorem val_eq_singleton_iff {a : α} {s : Finset α} : s.val = {a} ↔ s = {a} :=
  by
  rw [← val_inj]
  rfl
#align finset.val_eq_singleton_iff Finset.val_eq_singleton_iff
-/

#print Finset.singleton_injective /-
theorem singleton_injective : Injective (singleton : α → Finset α) := fun a b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)
#align finset.singleton_injective Finset.singleton_injective
-/

#print Finset.singleton_inj /-
@[simp]
theorem singleton_inj : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff
#align finset.singleton_inj Finset.singleton_inj
-/

#print Finset.singleton_nonempty /-
@[simp]
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩
#align finset.singleton_nonempty Finset.singleton_nonempty
-/

#print Finset.singleton_ne_empty /-
@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Finset α) ≠ ∅ :=
  (singleton_nonempty a).ne_empty
#align finset.singleton_ne_empty Finset.singleton_ne_empty
-/

#print Finset.empty_ssubset_singleton /-
theorem empty_ssubset_singleton : (∅ : Finset α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset
#align finset.empty_ssubset_singleton Finset.empty_ssubset_singleton
-/

#print Finset.coe_singleton /-
@[simp, norm_cast]
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} :=
  by
  ext
  simp
#align finset.coe_singleton Finset.coe_singleton
-/

#print Finset.coe_eq_singleton /-
@[simp, norm_cast]
theorem coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by
  rw [← coe_singleton, coe_inj]
#align finset.coe_eq_singleton Finset.coe_eq_singleton
-/

#print Finset.eq_singleton_iff_unique_mem /-
theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  by
  constructor <;> intro t
  rw [t]
  refine' ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
  ext; rw [Finset.mem_singleton]
  refine' ⟨t.right _, fun r => r.symm ▸ t.left⟩
#align finset.eq_singleton_iff_unique_mem Finset.eq_singleton_iff_unique_mem
-/

#print Finset.eq_singleton_iff_nonempty_unique_mem /-
theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hne, h_uniq⟩
    rw [eq_singleton_iff_unique_mem]
    refine' ⟨_, h_uniq⟩
    rw [← h_uniq hne.some hne.some_spec]
    exact hne.some_spec
#align finset.eq_singleton_iff_nonempty_unique_mem Finset.eq_singleton_iff_nonempty_unique_mem
-/

#print Finset.nonempty_iff_eq_singleton_default /-
theorem nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} : s.Nonempty ↔ s = {default} :=
  by simp [eq_singleton_iff_nonempty_unique_mem]
#align finset.nonempty_iff_eq_singleton_default Finset.nonempty_iff_eq_singleton_default
-/

alias nonempty_iff_eq_singleton_default ↔ nonempty.eq_singleton_default _
#align finset.nonempty.eq_singleton_default Finset.Nonempty.eq_singleton_default

#print Finset.singleton_iff_unique_mem /-
theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]
#align finset.singleton_iff_unique_mem Finset.singleton_iff_unique_mem
-/

#print Finset.singleton_subset_set_iff /-
theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) ⊆ s ↔ a ∈ s := by
  rw [coe_singleton, Set.singleton_subset_iff]
#align finset.singleton_subset_set_iff Finset.singleton_subset_set_iff
-/

#print Finset.singleton_subset_iff /-
@[simp]
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff
#align finset.singleton_subset_iff Finset.singleton_subset_iff
-/

#print Finset.subset_singleton_iff /-
@[simp]
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} := by
  rw [← coe_subset, coe_singleton, Set.subset_singleton_iff_eq, coe_eq_empty, coe_eq_singleton]
#align finset.subset_singleton_iff Finset.subset_singleton_iff
-/

#print Finset.singleton_subset_singleton /-
theorem singleton_subset_singleton : ({a} : Finset α) ⊆ {b} ↔ a = b := by simp
#align finset.singleton_subset_singleton Finset.singleton_subset_singleton
-/

#print Finset.Nonempty.subset_singleton_iff /-
protected theorem Nonempty.subset_singleton_iff {s : Finset α} {a : α} (h : s.Nonempty) :
    s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff.trans <| or_iff_right h.ne_empty
#align finset.nonempty.subset_singleton_iff Finset.Nonempty.subset_singleton_iff
-/

#print Finset.subset_singleton_iff' /-
theorem subset_singleton_iff' {s : Finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
  forall₂_congr fun _ _ => mem_singleton
#align finset.subset_singleton_iff' Finset.subset_singleton_iff'
-/

#print Finset.ssubset_singleton_iff /-
@[simp]
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ := by
  rw [← coe_ssubset, coe_singleton, Set.ssubset_singleton_iff, coe_eq_empty]
#align finset.ssubset_singleton_iff Finset.ssubset_singleton_iff
-/

#print Finset.eq_empty_of_ssubset_singleton /-
theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs
#align finset.eq_empty_of_ssubset_singleton Finset.eq_empty_of_ssubset_singleton
-/

#print Finset.eq_singleton_or_nontrivial /-
theorem eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ (s : Set α).Nontrivial :=
  by
  rw [← coe_eq_singleton]
  exact Set.eq_singleton_or_nontrivial ha
#align finset.eq_singleton_or_nontrivial Finset.eq_singleton_or_nontrivial
-/

#print Finset.Nonempty.exists_eq_singleton_or_nontrivial /-
theorem Nonempty.exists_eq_singleton_or_nontrivial :
    s.Nonempty → (∃ a, s = {a}) ∨ (s : Set α).Nontrivial := fun ⟨a, ha⟩ =>
  (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
#align finset.nonempty.exists_eq_singleton_or_nontrivial Finset.Nonempty.exists_eq_singleton_or_nontrivial
-/

instance [Nonempty α] : Nontrivial (Finset α) :=
  ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

instance [IsEmpty α] : Unique (Finset α)
    where
  default := ∅
  uniq s := eq_empty_of_forall_not_mem isEmptyElim

end Singleton

/-! ### cons -/


section Cons

variable {s t : Finset α} {a b : α}

#print Finset.cons /-
/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint. -/
def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩
#align finset.cons Finset.cons
-/

#print Finset.mem_cons /-
@[simp]
theorem mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s :=
  mem_cons
#align finset.mem_cons Finset.mem_cons
-/

#print Finset.mem_cons_self /-
@[simp]
theorem mem_cons_self (a : α) (s : Finset α) {h} : a ∈ cons a s h :=
  mem_cons_self _ _
#align finset.mem_cons_self Finset.mem_cons_self
-/

#print Finset.cons_val /-
@[simp]
theorem cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl
#align finset.cons_val Finset.cons_val
-/

#print Finset.forall_mem_cons /-
theorem forall_mem_cons (h : a ∉ s) (p : α → Prop) :
    (∀ x, x ∈ cons a s h → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_cons, or_imp, forall_and, forall_eq]
#align finset.forall_mem_cons Finset.forall_mem_cons
-/

#print Finset.mk_cons /-
@[simp]
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl
#align finset.mk_cons Finset.mk_cons
-/

#print Finset.nonempty_cons /-
@[simp]
theorem nonempty_cons (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 <| Or.inl rfl⟩
#align finset.nonempty_cons Finset.nonempty_cons
-/

#print Finset.nonempty_mk /-
@[simp]
theorem nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m ≠ 0 := by
  induction m using Multiset.induction_on <;> simp
#align finset.nonempty_mk Finset.nonempty_mk
-/

#print Finset.coe_cons /-
@[simp]
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a s :=
  by
  ext
  simp
#align finset.coe_cons Finset.coe_cons
-/

#print Finset.subset_cons /-
theorem subset_cons (h : a ∉ s) : s ⊆ s.cons a h :=
  subset_cons _ _
#align finset.subset_cons Finset.subset_cons
-/

#print Finset.ssubset_cons /-
theorem ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h :=
  ssubset_cons h
#align finset.ssubset_cons Finset.ssubset_cons
-/

#print Finset.cons_subset /-
theorem cons_subset {h : a ∉ s} : s.cons a h ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  cons_subset
#align finset.cons_subset Finset.cons_subset
-/

#print Finset.cons_subset_cons /-
@[simp]
theorem cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t := by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]
#align finset.cons_subset_cons Finset.cons_subset_cons
-/

#print Finset.ssubset_iff_exists_cons_subset /-
theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ (a : _)(h : a ∉ s), s.cons a h ⊆ t :=
  by
  refine' ⟨fun h => _, fun ⟨a, ha, h⟩ => ssubset_of_ssubset_of_subset (ssubset_cons _) h⟩
  obtain ⟨a, hs, ht⟩ := not_subset.1 h.2
  exact ⟨a, ht, cons_subset.2 ⟨hs, h.subset⟩⟩
#align finset.ssubset_iff_exists_cons_subset Finset.ssubset_iff_exists_cons_subset
-/

end Cons

/-! ### disjoint -/


section Disjoint

variable {f : α → β} {s t u : Finset α} {a b : α}

/- warning: finset.disjoint_left -> Finset.disjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) (forall {{a : α}}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_left Finset.disjoint_leftₓ'. -/
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  ⟨fun h a hs ht =>
    singleton_subset_iff.mp (h (singleton_subset_iff.mpr hs) (singleton_subset_iff.mpr ht)),
    fun h x hs ht a ha => h (hs ha) (ht ha)⟩
#align finset.disjoint_left Finset.disjoint_left

/- warning: finset.disjoint_right -> Finset.disjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t) -> (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) (forall {{a : α}}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t) -> (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_right Finset.disjoint_rightₓ'. -/
theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint_comm, disjoint_left]
#align finset.disjoint_right Finset.disjoint_right

/- warning: finset.disjoint_iff_ne -> Finset.disjoint_iff_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Ne.{succ u1} α a b)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (forall (b : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Ne.{succ u1} α a b)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_iff_ne Finset.disjoint_iff_neₓ'. -/
theorem disjoint_iff_ne : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp only [disjoint_left, imp_not_comm, forall_eq']
#align finset.disjoint_iff_ne Finset.disjoint_iff_ne

/- warning: finset.disjoint_val -> Finset.disjoint_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Multiset.Disjoint.{u1} α (Finset.val.{u1} α s) (Finset.val.{u1} α t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Multiset.Disjoint.{u1} α (Finset.val.{u1} α s) (Finset.val.{u1} α t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_val Finset.disjoint_valₓ'. -/
@[simp]
theorem disjoint_val : s.1.Disjoint t.1 ↔ Disjoint s t :=
  disjoint_left.symm
#align finset.disjoint_val Finset.disjoint_val

/- warning: disjoint.forall_ne_finset -> Disjoint.forall_ne_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α} {b : α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b t) -> (Ne.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α} {b : α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b t) -> (Ne.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align disjoint.forall_ne_finset Disjoint.forall_ne_finsetₓ'. -/
theorem Disjoint.forall_ne_finset (h : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  disjoint_iff_ne.1 h _ ha _ hb
#align disjoint.forall_ne_finset Disjoint.forall_ne_finset

/- warning: finset.not_disjoint_iff -> Finset.not_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t)))
Case conversion may be inaccurate. Consider using '#align finset.not_disjoint_iff Finset.not_disjoint_iffₓ'. -/
theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  disjoint_left.Not.trans <|
    not_forall.trans <| exists_congr fun _ => by rw [not_imp, Classical.not_not]
#align finset.not_disjoint_iff Finset.not_disjoint_iff

/- warning: finset.disjoint_of_subset_left -> Finset.disjoint_of_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s u) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) u t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s u) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) u t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_of_subset_left Finset.disjoint_of_subset_leftₓ'. -/
theorem disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun x m₁ => (disjoint_left.1 d) (h m₁)
#align finset.disjoint_of_subset_left Finset.disjoint_of_subset_left

/- warning: finset.disjoint_of_subset_right -> Finset.disjoint_of_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t u) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s u) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) t u) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s u) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_of_subset_right Finset.disjoint_of_subset_rightₓ'. -/
theorem disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun x m₁ => (disjoint_right.1 d) (h m₁)
#align finset.disjoint_of_subset_right Finset.disjoint_of_subset_right

/- warning: finset.disjoint_empty_left -> Finset.disjoint_empty_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) s
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)) s
Case conversion may be inaccurate. Consider using '#align finset.disjoint_empty_left Finset.disjoint_empty_leftₓ'. -/
@[simp]
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left
#align finset.disjoint_empty_left Finset.disjoint_empty_left

/- warning: finset.disjoint_empty_right -> Finset.disjoint_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_empty_right Finset.disjoint_empty_rightₓ'. -/
@[simp]
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right
#align finset.disjoint_empty_right Finset.disjoint_empty_right

/- warning: finset.disjoint_singleton_left -> Finset.disjoint_singleton_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) s) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) s) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_singleton_left Finset.disjoint_singleton_leftₓ'. -/
@[simp]
theorem disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s := by
  simp only [disjoint_left, mem_singleton, forall_eq]
#align finset.disjoint_singleton_left Finset.disjoint_singleton_left

/- warning: finset.disjoint_singleton_right -> Finset.disjoint_singleton_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_singleton_right Finset.disjoint_singleton_rightₓ'. -/
@[simp]
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left
#align finset.disjoint_singleton_right Finset.disjoint_singleton_right

/- warning: finset.disjoint_singleton -> Finset.disjoint_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b)) (Ne.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b)) (Ne.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_singleton Finset.disjoint_singletonₓ'. -/
@[simp]
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton]
#align finset.disjoint_singleton Finset.disjoint_singleton

/- warning: finset.disjoint_self_iff_empty -> Finset.disjoint_self_iff_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s) (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s s) (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_self_iff_empty Finset.disjoint_self_iff_emptyₓ'. -/
theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self
#align finset.disjoint_self_iff_empty Finset.disjoint_self_iff_empty

/- warning: finset.disjoint_coe -> Finset.disjoint_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (Finset.toSet.{u1} α s) (Finset.toSet.{u1} α t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_coe Finset.disjoint_coeₓ'. -/
@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t :=
  by
  rw [Finset.disjoint_left, Set.disjoint_left]
  rfl
#align finset.disjoint_coe Finset.disjoint_coe

/- warning: finset.pairwise_disjoint_coe -> Finset.pairwiseDisjoint_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Finset.{u1} α)}, Iff (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (f i))) (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s f)
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι} {f : ι -> (Finset.{u1} α)}, Iff (Set.PairwiseDisjoint.{u1, u2} (Set.{u1} α) ι (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (fun (i : ι) => Finset.toSet.{u1} α (f i))) (Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s f)
Case conversion may be inaccurate. Consider using '#align finset.pairwise_disjoint_coe Finset.pairwiseDisjoint_coeₓ'. -/
@[simp, norm_cast]
theorem pairwiseDisjoint_coe {ι : Type _} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint (fun i => f i : ι → Set α) ↔ s.PairwiseDisjoint f :=
  forall₅_congr fun _ _ _ _ _ => disjoint_coe
#align finset.pairwise_disjoint_coe Finset.pairwiseDisjoint_coe

end Disjoint

/-! ### disjoint union -/


/- warning: finset.disj_union -> Finset.disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α), (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Finset.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α), (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Finset.{u1} α)
Case conversion may be inaccurate. Consider using '#align finset.disj_union Finset.disjUnionₓ'. -/
/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disjUnion (s t : Finset α) (h : Disjoint s t) : Finset α :=
  ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, disjoint_val.2 h⟩⟩
#align finset.disj_union Finset.disjUnion

/- warning: finset.mem_disj_union -> Finset.mem_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t} {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.disjUnion.{u1} α s t h)) (Or (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t} {a : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (Finset.disjUnion.{u1} α s t h)) (Or (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t))
Case conversion may be inaccurate. Consider using '#align finset.mem_disj_union Finset.mem_disjUnionₓ'. -/
@[simp]
theorem mem_disjUnion {α s t h a} : a ∈ @disjUnion α s t h ↔ a ∈ s ∨ a ∈ t := by
  rcases s with ⟨⟨s⟩⟩ <;> rcases t with ⟨⟨t⟩⟩ <;> apply List.mem_append
#align finset.mem_disj_union Finset.mem_disjUnion

/- warning: finset.disj_union_comm -> Finset.disjUnion_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s t h) (Finset.disjUnion.{u1} α t s (Disjoint.symm.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t h))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s t h) (Finset.disjUnion.{u1} α t s (Disjoint.symm.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t h))
Case conversion may be inaccurate. Consider using '#align finset.disj_union_comm Finset.disjUnion_commₓ'. -/
theorem disjUnion_comm (s t : Finset α) (h : Disjoint s t) :
    disjUnion s t h = disjUnion t s h.symm :=
  eq_of_veq <| add_comm _ _
#align finset.disj_union_comm Finset.disjUnion_comm

/- warning: finset.empty_disj_union -> Finset.empty_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Finset.{u1} α) (h : optParam.{0} (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) t) (disjoint_bot_left.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) t)), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) t h) t
but is expected to have type
  forall {α : Type.{u1}} (t : Finset.{u1} α) (h : optParam.{0} (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)) t) (disjoint_bot_left.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) t)), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)) t h) t
Case conversion may be inaccurate. Consider using '#align finset.empty_disj_union Finset.empty_disjUnionₓ'. -/
@[simp]
theorem empty_disjUnion (t : Finset α) (h : Disjoint ∅ t := disjoint_bot_left) :
    disjUnion ∅ t h = t :=
  eq_of_veq <| zero_add _
#align finset.empty_disj_union Finset.empty_disjUnion

/- warning: finset.disj_union_empty -> Finset.disjUnion_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (h : optParam.{0} (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (disjoint_bot_right.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s)), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) h) s
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (h : optParam.{0} (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))) (disjoint_bot_right.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s)), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)) h) s
Case conversion may be inaccurate. Consider using '#align finset.disj_union_empty Finset.disjUnion_emptyₓ'. -/
@[simp]
theorem disjUnion_empty (s : Finset α) (h : Disjoint s ∅ := disjoint_bot_right) :
    disjUnion s ∅ h = s :=
  eq_of_veq <| add_zero _
#align finset.disj_union_empty Finset.disjUnion_empty

/- warning: finset.singleton_disj_union -> Finset.singleton_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t h) (Finset.cons.{u1} α a t (Iff.mp (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t)) (Finset.disjoint_singleton_left.{u1} α t a) h))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t h) (Finset.cons.{u1} α a t (Iff.mp (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t)) (Finset.disjoint_singleton_left.{u1} α t a) h))
Case conversion may be inaccurate. Consider using '#align finset.singleton_disj_union Finset.singleton_disjUnionₓ'. -/
theorem singleton_disjUnion (a : α) (t : Finset α) (h : Disjoint {a} t) :
    disjUnion {a} t h = cons a t (disjoint_singleton_left.mp h) :=
  eq_of_veq <| Multiset.singleton_add _ _
#align finset.singleton_disj_union Finset.singleton_disjUnion

/- warning: finset.disj_union_singleton -> Finset.disjUnion_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (a : α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) h) (Finset.cons.{u1} α a s (Iff.mp (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (Finset.disjoint_singleton_right.{u1} α s a) h))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (a : α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) h) (Finset.cons.{u1} α a s (Iff.mp (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) (Finset.disjoint_singleton_right.{u1} α s a) h))
Case conversion may be inaccurate. Consider using '#align finset.disj_union_singleton Finset.disjUnion_singletonₓ'. -/
theorem disjUnion_singleton (s : Finset α) (a : α) (h : Disjoint s {a}) :
    disjUnion s {a} h = cons a s (disjoint_singleton_right.mp h) := by
  rw [disj_union_comm, singleton_disj_union]
#align finset.disj_union_singleton Finset.disjUnion_singleton

/-! ### insert -/


section Insert

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : Insert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

#print Finset.insert_def /-
theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl
#align finset.insert_def Finset.insert_def
-/

#print Finset.insert_val /-
@[simp]
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl
#align finset.insert_val Finset.insert_val
-/

#print Finset.insert_val' /-
theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons, dedup_eq_self] <;> rfl
#align finset.insert_val' Finset.insert_val'
-/

#print Finset.insert_val_of_not_mem /-
theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_not_mem h]
#align finset.insert_val_of_not_mem Finset.insert_val_of_not_mem
-/

#print Finset.mem_insert /-
@[simp]
theorem mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert
#align finset.mem_insert Finset.mem_insert
-/

#print Finset.mem_insert_self /-
theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1
#align finset.mem_insert_self Finset.mem_insert_self
-/

#print Finset.mem_insert_of_mem /-
theorem mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s :=
  mem_ndinsert_of_mem h
#align finset.mem_insert_of_mem Finset.mem_insert_of_mem
-/

#print Finset.mem_of_mem_insert_of_ne /-
theorem mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  (mem_insert.1 h).resolve_left
#align finset.mem_of_mem_insert_of_ne Finset.mem_of_mem_insert_of_ne
-/

#print Finset.eq_of_not_mem_of_mem_insert /-
theorem eq_of_not_mem_of_mem_insert (ha : b ∈ insert a s) (hb : b ∉ s) : b = a :=
  (mem_insert.1 ha).resolve_right hb
#align finset.eq_of_not_mem_of_mem_insert Finset.eq_of_not_mem_of_mem_insert
-/

#print Finset.cons_eq_insert /-
@[simp]
theorem cons_eq_insert (a s h) : @cons α a s h = insert a s :=
  ext fun a => by simp
#align finset.cons_eq_insert Finset.cons_eq_insert
-/

#print Finset.coe_insert /-
@[simp, norm_cast]
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) :=
  Set.ext fun x => by simp only [mem_coe, mem_insert, Set.mem_insert_iff]
#align finset.coe_insert Finset.coe_insert
-/

#print Finset.mem_insert_coe /-
theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) := by
  simp
#align finset.mem_insert_coe Finset.mem_insert_coe
-/

instance : IsLawfulSingleton α (Finset α) :=
  ⟨fun a => by
    ext
    simp⟩

#print Finset.insert_eq_of_mem /-
@[simp]
theorem insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
  eq_of_veq <| ndinsert_of_mem h
#align finset.insert_eq_of_mem Finset.insert_eq_of_mem
-/

#print Finset.insert_eq_self /-
@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert_self _ _, insert_eq_of_mem⟩
#align finset.insert_eq_self Finset.insert_eq_self
-/

#print Finset.insert_ne_self /-
theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.Not
#align finset.insert_ne_self Finset.insert_ne_self
-/

#print Finset.pair_eq_singleton /-
@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem <| mem_singleton_self _
#align finset.pair_eq_singleton Finset.pair_eq_singleton
-/

#print Finset.Insert.comm /-
theorem Insert.comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => by simp only [mem_insert, or_left_comm]
#align finset.insert.comm Finset.Insert.comm
-/

#print Finset.coe_pair /-
@[simp, norm_cast]
theorem coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b} :=
  by
  ext
  simp
#align finset.coe_pair Finset.coe_pair
-/

#print Finset.coe_eq_pair /-
@[simp, norm_cast]
theorem coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b} := by
  rw [← coe_pair, coe_inj]
#align finset.coe_eq_pair Finset.coe_eq_pair
-/

#print Finset.pair_comm /-
theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  Insert.comm a b ∅
#align finset.pair_comm Finset.pair_comm
-/

#print Finset.insert_idem /-
@[simp]
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s :=
  ext fun x => by simp only [mem_insert, or.assoc.symm, or_self_iff]
#align finset.insert_idem Finset.insert_idem
-/

#print Finset.insert_nonempty /-
@[simp]
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩
#align finset.insert_nonempty Finset.insert_nonempty
-/

#print Finset.insert_ne_empty /-
@[simp]
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s ≠ ∅ :=
  (insert_nonempty a s).ne_empty
#align finset.insert_ne_empty Finset.insert_ne_empty
-/

/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/


instance {α : Type u} [DecidableEq α] (i : α) (s : Finset α) :
    Nonempty.{u + 1} ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

#print Finset.ne_insert_of_not_mem /-
theorem ne_insert_of_not_mem (s t : Finset α) {a : α} (h : a ∉ s) : s ≠ insert a t :=
  by
  contrapose! h
  simp [h]
#align finset.ne_insert_of_not_mem Finset.ne_insert_of_not_mem
-/

#print Finset.insert_subset /-
theorem insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_iff, mem_insert, forall_eq, or_imp, forall_and]
#align finset.insert_subset Finset.insert_subset
-/

#print Finset.subset_insert /-
theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s := fun b => mem_insert_of_mem
#align finset.subset_insert Finset.subset_insert
-/

#print Finset.insert_subset_insert /-
theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
  insert_subset.2 ⟨mem_insert_self _ _, Subset.trans h (subset_insert _ _)⟩
#align finset.insert_subset_insert Finset.insert_subset_insert
-/

#print Finset.insert_inj /-
theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert_self _ _) ha, congr_arg _⟩
#align finset.insert_inj Finset.insert_inj
-/

/- warning: finset.insert_inj_on -> Finset.insert_inj_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Set.InjOn.{u1, u1} α (Finset.{u1} α) (fun (a : α) => Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Set.InjOn.{u1, u1} α (Finset.{u1} α) (fun (a : α) => Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Finset.toSet.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.insert_inj_on Finset.insert_inj_onₓ'. -/
theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ) := fun a h b _ =>
  (insert_inj h).1
#align finset.insert_inj_on Finset.insert_inj_on

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ∉ » s) -/
#print Finset.ssubset_iff /-
theorem ssubset_iff : s ⊂ t ↔ ∃ (a : _)(_ : a ∉ s), insert a s ⊆ t := by
  exact_mod_cast @Set.ssubset_iff_insert α s t
#align finset.ssubset_iff Finset.ssubset_iff
-/

#print Finset.ssubset_insert /-
theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩
#align finset.ssubset_insert Finset.ssubset_insert
-/

#print Finset.cons_induction /-
@[elab_as_elim]
theorem cons_induction {α : Type _} {p : Finset α → Prop} (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
  | ⟨s, nd⟩ =>
    Multiset.induction_on s (fun _ => h₁)
      (fun a s IH nd => by
        cases' nodup_cons.1 nd with m nd'
        rw [← (eq_of_veq _ : cons a (Finset.mk s _) m = ⟨a ::ₘ s, nd⟩)]
        · exact h₂ m (IH nd')
        · rw [cons_val])
      nd
#align finset.cons_induction Finset.cons_induction
-/

#print Finset.cons_induction_on /-
@[elab_as_elim]
theorem cons_induction_on {α : Type _} {p : Finset α → Prop} (s : Finset α) (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
  cons_induction h₁ h₂ s
#align finset.cons_induction_on Finset.cons_induction_on
-/

#print Finset.induction /-
@[elab_as_elim]
protected theorem induction {α : Type _} {p : Finset α → Prop} [DecidableEq α] (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
  cons_induction h₁ fun a s ha => (s.cons_eq_insert a ha).symm ▸ h₂ ha
#align finset.induction Finset.induction
-/

#print Finset.induction_on /-
/-- To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_elim]
protected theorem induction_on {α : Type _} {p : Finset α → Prop} [DecidableEq α] (s : Finset α)
    (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
  Finset.induction h₁ h₂ s
#align finset.induction_on Finset.induction_on
-/

#print Finset.induction_on' /-
/-- To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
@[elab_as_elim]
theorem induction_on' {α : Type _} {p : Finset α → Prop} [DecidableEq α] (S : Finset α) (h₁ : p ∅)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
  @Finset.induction_on α (fun T => T ⊆ S → p T) _ S (fun _ => h₁)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset.1 hs
      h₂ hS sS has (hqs sS))
    (Finset.Subset.refl S)
#align finset.induction_on' Finset.induction_on'
-/

#print Finset.Nonempty.cons_induction /-
/-- To prove a proposition about a nonempty `s : finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : finset α`, then it also holds for the `finset`
obtained by inserting an element in `t`. -/
@[elab_as_elim]
theorem Nonempty.cons_induction {α : Type _} {p : ∀ s : Finset α, s.Nonempty → Prop}
    (h₀ : ∀ a, p {a} (singleton_nonempty _))
    (h₁ : ∀ ⦃a⦄ (s) (h : a ∉ s) (hs), p s hs → p (Finset.cons a s h) (nonempty_cons h))
    {s : Finset α} (hs : s.Nonempty) : p s hs :=
  by
  induction' s using Finset.cons_induction with a t ha h
  · exact (not_nonempty_empty hs).elim
  obtain rfl | ht := t.eq_empty_or_nonempty
  · exact h₀ a
  · exact h₁ t ha ht (h ht)
#align finset.nonempty.cons_induction Finset.Nonempty.cons_induction
-/

#print Finset.subtypeInsertEquivOption /-
/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } :=
  by
  refine'
    { toFun := fun y => if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
      invFun := fun y => y.elim ⟨x, mem_insert_self _ _⟩ fun z => ⟨z, mem_insert_of_mem z.2⟩.. }
  · intro y
    by_cases h : ↑y = x
    simp only [Subtype.ext_iff, h, Option.elim', dif_pos, Subtype.coe_mk]
    simp only [h, Option.elim', dif_neg, not_false_iff, Subtype.coe_eta, Subtype.coe_mk]
  · rintro (_ | y)
    simp only [Option.elim', dif_pos, Subtype.coe_mk]
    have : ↑y ≠ x := by
      rintro ⟨⟩
      exact h y.2
    simp only [this, Option.elim', Subtype.eta, dif_neg, not_false_iff, Subtype.coe_eta,
      Subtype.coe_mk]
#align finset.subtype_insert_equiv_option Finset.subtypeInsertEquivOption
-/

/- warning: finset.disjoint_insert_left -> Finset.disjoint_insert_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) t) (And (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s) t) (And (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_insert_left Finset.disjoint_insert_leftₓ'. -/
@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [disjoint_left, mem_insert, or_imp, forall_and, forall_eq]
#align finset.disjoint_insert_left Finset.disjoint_insert_left

/- warning: finset.disjoint_insert_right -> Finset.disjoint_insert_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a t)) (And (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a t)) (And (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_insert_right Finset.disjoint_insert_rightₓ'. -/
@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  disjoint_comm.trans <| by rw [disjoint_insert_left, disjoint_comm]
#align finset.disjoint_insert_right Finset.disjoint_insert_right

end Insert

/-! ### Lattice structure -/


section Lattice

variable [DecidableEq α] {s s₁ s₂ t t₁ t₂ u v : Finset α} {a b : α}

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : Union (Finset α) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : Inter (Finset α) :=
  ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

instance : Lattice (Finset α) :=
  { Finset.partialOrder with
    sup := (· ∪ ·)
    sup_le := fun s t u hs ht a ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h
    le_sup_left := fun s t a h => mem_ndunion.2 <| Or.inl h
    le_sup_right := fun s t a h => mem_ndunion.2 <| Or.inr h
    inf := (· ∩ ·)
    le_inf := fun s t u ht hu a h => mem_ndinter.2 ⟨ht h, hu h⟩
    inf_le_left := fun s t a h => (mem_ndinter.1 h).1
    inf_le_right := fun s t a h => (mem_ndinter.1 h).2 }

/- warning: finset.sup_eq_union -> Finset.sup_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], Eq.{succ u1} ((Finset.{u1} α) -> (Finset.{u1} α) -> (Finset.{u1} α)) (Sup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))))) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], Eq.{succ u1} ((Finset.{u1} α) -> (Finset.{u1} α) -> (Finset.{u1} α)) (Sup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))))) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align finset.sup_eq_union Finset.sup_eq_unionₓ'. -/
@[simp]
theorem sup_eq_union : ((· ⊔ ·) : Finset α → Finset α → Finset α) = (· ∪ ·) :=
  rfl
#align finset.sup_eq_union Finset.sup_eq_union

/- warning: finset.inf_eq_inter -> Finset.inf_eq_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], Eq.{succ u1} ((Finset.{u1} α) -> (Finset.{u1} α) -> (Finset.{u1} α)) (Inf.inf.{u1} (Finset.{u1} α) (SemilatticeInf.toHasInf.{u1} (Finset.{u1} α) (Lattice.toSemilatticeInf.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], Eq.{succ u1} ((Finset.{u1} α) -> (Finset.{u1} α) -> (Finset.{u1} α)) (Inf.inf.{u1} (Finset.{u1} α) (Lattice.toInf.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))
Case conversion may be inaccurate. Consider using '#align finset.inf_eq_inter Finset.inf_eq_interₓ'. -/
@[simp]
theorem inf_eq_inter : ((· ⊓ ·) : Finset α → Finset α → Finset α) = (· ∩ ·) :=
  rfl
#align finset.inf_eq_inter Finset.inf_eq_inter

/- warning: finset.disjoint_iff_inter_eq_empty -> Finset.disjoint_iff_inter_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) (Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) (Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_iff_inter_eq_empty Finset.disjoint_iff_inter_eq_emptyₓ'. -/
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
#align finset.disjoint_iff_inter_eq_empty Finset.disjoint_iff_inter_eq_empty

/- warning: finset.decidable_disjoint -> Finset.decidableDisjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (U : Finset.{u1} α) (V : Finset.{u1} α), Decidable (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) U V)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (U : Finset.{u1} α) (V : Finset.{u1} α), Decidable (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) U V)
Case conversion may be inaccurate. Consider using '#align finset.decidable_disjoint Finset.decidableDisjointₓ'. -/
instance decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidable_of_iff _ disjoint_left.symm
#align finset.decidable_disjoint Finset.decidableDisjoint

/-! #### union -/


#print Finset.union_val_nd /-
theorem union_val_nd (s t : Finset α) : (s ∪ t).1 = ndunion s.1 t.1 :=
  rfl
#align finset.union_val_nd Finset.union_val_nd
-/

#print Finset.union_val /-
@[simp]
theorem union_val (s t : Finset α) : (s ∪ t).1 = s.1 ∪ t.1 :=
  ndunion_eq_union s.2
#align finset.union_val Finset.union_val
-/

#print Finset.mem_union /-
@[simp]
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  mem_ndunion
#align finset.mem_union Finset.mem_union
-/

/- warning: finset.disj_union_eq_union -> Finset.disjUnion_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s t h) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t), Eq.{succ u1} (Finset.{u1} α) (Finset.disjUnion.{u1} α s t h) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
Case conversion may be inaccurate. Consider using '#align finset.disj_union_eq_union Finset.disjUnion_eq_unionₓ'. -/
@[simp]
theorem disjUnion_eq_union (s t h) : @disjUnion α s t h = s ∪ t :=
  ext fun a => by simp
#align finset.disj_union_eq_union Finset.disjUnion_eq_union

#print Finset.mem_union_left /-
theorem mem_union_left (t : Finset α) (h : a ∈ s) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inl h
#align finset.mem_union_left Finset.mem_union_left
-/

#print Finset.mem_union_right /-
theorem mem_union_right (s : Finset α) (h : a ∈ t) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inr h
#align finset.mem_union_right Finset.mem_union_right
-/

#print Finset.forall_mem_union /-
theorem forall_mem_union {p : α → Prop} : (∀ a ∈ s ∪ t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a :=
  ⟨fun h => ⟨fun a => h a ∘ mem_union_left _, fun b => h b ∘ mem_union_right _⟩, fun h ab hab =>
    (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩
#align finset.forall_mem_union Finset.forall_mem_union
-/

#print Finset.not_mem_union /-
theorem not_mem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union, not_or]
#align finset.not_mem_union Finset.not_mem_union
-/

/- warning: finset.coe_union -> Finset.coe_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Finset.toSet.{u1} α s₁) (Finset.toSet.{u1} α s₂))
Case conversion may be inaccurate. Consider using '#align finset.coe_union Finset.coe_unionₓ'. -/
@[simp, norm_cast]
theorem coe_union (s₁ s₂ : Finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : Set α) :=
  Set.ext fun x => mem_union
#align finset.coe_union Finset.coe_union

#print Finset.union_subset /-
theorem union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u :=
  sup_le <| le_iff_subset.2 hs
#align finset.union_subset Finset.union_subset
-/

#print Finset.subset_union_left /-
theorem subset_union_left (s₁ s₂ : Finset α) : s₁ ⊆ s₁ ∪ s₂ := fun x => mem_union_left _
#align finset.subset_union_left Finset.subset_union_left
-/

#print Finset.subset_union_right /-
theorem subset_union_right (s₁ s₂ : Finset α) : s₂ ⊆ s₁ ∪ s₂ := fun x => mem_union_right _
#align finset.subset_union_right Finset.subset_union_right
-/

#print Finset.union_subset_union /-
theorem union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  sup_le_sup (le_iff_subset.2 hsu) htv
#align finset.union_subset_union Finset.union_subset_union
-/

#print Finset.union_subset_union_left /-
theorem union_subset_union_left (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
#align finset.union_subset_union_left Finset.union_subset_union_left
-/

#print Finset.union_subset_union_right /-
theorem union_subset_union_right (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
#align finset.union_subset_union_right Finset.union_subset_union_right
-/

#print Finset.union_comm /-
theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
  sup_comm
#align finset.union_comm Finset.union_comm
-/

instance : IsCommutative (Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

#print Finset.union_assoc /-
@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  sup_assoc
#align finset.union_assoc Finset.union_assoc
-/

instance : IsAssociative (Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

#print Finset.union_idempotent /-
@[simp]
theorem union_idempotent (s : Finset α) : s ∪ s = s :=
  sup_idem
#align finset.union_idempotent Finset.union_idempotent
-/

instance : IsIdempotent (Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩

#print Finset.union_subset_left /-
theorem union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u :=
  (subset_union_left _ _).trans h
#align finset.union_subset_left Finset.union_subset_left
-/

#print Finset.union_subset_right /-
theorem union_subset_right {s t u : Finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
  Subset.trans (subset_union_right _ _) h
#align finset.union_subset_right Finset.union_subset_right
-/

#print Finset.union_left_comm /-
theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by simp only [mem_union, or_left_comm]
#align finset.union_left_comm Finset.union_left_comm
-/

#print Finset.union_right_comm /-
theorem union_right_comm (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ t :=
  ext fun x => by simp only [mem_union, or_assoc', or_comm' (x ∈ t)]
#align finset.union_right_comm Finset.union_right_comm
-/

#print Finset.union_self /-
theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s
#align finset.union_self Finset.union_self
-/

#print Finset.union_empty /-
@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| or_false_iff _
#align finset.union_empty Finset.union_empty
-/

#print Finset.empty_union /-
@[simp]
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext fun x => mem_union.trans <| false_or_iff _
#align finset.empty_union Finset.empty_union
-/

#print Finset.insert_eq /-
theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl
#align finset.insert_eq Finset.insert_eq
-/

#print Finset.insert_union /-
@[simp]
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) := by
  simp only [insert_eq, union_assoc]
#align finset.insert_union Finset.insert_union
-/

#print Finset.union_insert /-
@[simp]
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  simp only [insert_eq, union_left_comm]
#align finset.union_insert Finset.union_insert
-/

#print Finset.insert_union_distrib /-
theorem insert_union_distrib (a : α) (s t : Finset α) :
    insert a (s ∪ t) = insert a s ∪ insert a t := by
  simp only [insert_union, union_insert, insert_idem]
#align finset.insert_union_distrib Finset.insert_union_distrib
-/

#print Finset.union_eq_left_iff_subset /-
@[simp]
theorem union_eq_left_iff_subset {s t : Finset α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left
#align finset.union_eq_left_iff_subset Finset.union_eq_left_iff_subset
-/

#print Finset.left_eq_union_iff_subset /-
@[simp]
theorem left_eq_union_iff_subset {s t : Finset α} : s = s ∪ t ↔ t ⊆ s := by
  rw [← union_eq_left_iff_subset, eq_comm]
#align finset.left_eq_union_iff_subset Finset.left_eq_union_iff_subset
-/

#print Finset.union_eq_right_iff_subset /-
@[simp]
theorem union_eq_right_iff_subset {s t : Finset α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right
#align finset.union_eq_right_iff_subset Finset.union_eq_right_iff_subset
-/

#print Finset.right_eq_union_iff_subset /-
@[simp]
theorem right_eq_union_iff_subset {s t : Finset α} : s = t ∪ s ↔ t ⊆ s := by
  rw [← union_eq_right_iff_subset, eq_comm]
#align finset.right_eq_union_iff_subset Finset.right_eq_union_iff_subset
-/

/- warning: finset.union_congr_left -> Finset.union_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s u)) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) u (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Sup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) s u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) t (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s u)) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) u (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) -> (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Sup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) s u))
Case conversion may be inaccurate. Consider using '#align finset.union_congr_left Finset.union_congr_leftₓ'. -/
theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ⊔ u :=
  sup_congr_left ht hu
#align finset.union_congr_left Finset.union_congr_left

#print Finset.union_congr_right /-
theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht
#align finset.union_congr_right Finset.union_congr_right
-/

#print Finset.union_eq_union_iff_left /-
theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left
#align finset.union_eq_union_iff_left Finset.union_eq_union_iff_left
-/

#print Finset.union_eq_union_iff_right /-
theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right
#align finset.union_eq_union_iff_right Finset.union_eq_union_iff_right
-/

/- warning: finset.disjoint_union_left -> Finset.disjoint_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) u) (And (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s u) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) u) (And (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s u) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_union_left Finset.disjoint_union_leftₓ'. -/
@[simp]
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [disjoint_left, mem_union, or_imp, forall_and]
#align finset.disjoint_union_left Finset.disjoint_union_left

/- warning: finset.disjoint_union_right -> Finset.disjoint_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u)) (And (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u)) (And (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_union_right Finset.disjoint_union_rightₓ'. -/
@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [disjoint_right, mem_union, or_imp, forall_and]
#align finset.disjoint_union_right Finset.disjoint_union_right

#print Finset.induction_on_union /-
/-- To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union (P : Finset α → Finset α → Prop) (symm : ∀ {a b}, P a b → P b a)
    (empty_right : ∀ {a}, P a ∅) (singletons : ∀ {a b}, P {a} {b})
    (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) : ∀ a b, P a b :=
  by
  intro a b
  refine' Finset.induction_on b empty_right fun x s xs hi => symm _
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine' Finset.induction_on a empty_right fun a t ta hi => symm _
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)
#align finset.induction_on_union Finset.induction_on_union
-/

/- warning: directed.exists_mem_subset_of_finset_subset_bUnion -> Directed.exists_mem_subset_of_finset_subset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [hn : Nonempty.{succ u2} ι] {f : ι -> (Set.{u1} α)}, (Directed.{u1, succ u2} (Set.{u1} α) ι (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) f) -> (forall {s : Finset.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => f i))) -> (Exists.{succ u2} ι (fun (i : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (f i))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [hn : Nonempty.{succ u1} ι] {f : ι -> (Set.{u2} α)}, (Directed.{u2, succ u1} (Set.{u2} α) ι (fun (x._@.Mathlib.Data.Finset.Basic._hyg.13840 : Set.{u2} α) (x._@.Mathlib.Data.Finset.Basic._hyg.13842 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Data.Finset.Basic._hyg.13840 x._@.Mathlib.Data.Finset.Basic._hyg.13842) f) -> (forall {s : Finset.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α s) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => f i))) -> (Exists.{succ u1} ι (fun (i : ι) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α s) (f i))))
Case conversion may be inaccurate. Consider using '#align directed.exists_mem_subset_of_finset_subset_bUnion Directed.exists_mem_subset_of_finset_subset_bunionᵢₓ'. -/
theorem Directed.exists_mem_subset_of_finset_subset_bunionᵢ {α ι : Type _} [hn : Nonempty ι]
    {f : ι → Set α} (h : Directed (· ⊆ ·) f) {s : Finset α} (hs : (s : Set α) ⊆ ⋃ i, f i) :
    ∃ i, (s : Set α) ⊆ f i := by
  classical
    revert hs
    apply s.induction_on
    · refine' fun _ => ⟨hn.some, _⟩
      simp only [coe_empty, Set.empty_subset]
    · intro b t hbt htc hbtc
      obtain ⟨i : ι, hti : (t : Set α) ⊆ f i⟩ := htc (Set.Subset.trans (t.subset_insert b) hbtc)
      obtain ⟨j, hbj⟩ : ∃ j, b ∈ f j := by simpa [Set.mem_unionᵢ₂] using hbtc (t.mem_insert_self b)
      rcases h j i with ⟨k, hk, hk'⟩
      use k
      rw [coe_insert, Set.insert_subset]
      exact ⟨hk hbj, trans hti hk'⟩
#align directed.exists_mem_subset_of_finset_subset_bUnion Directed.exists_mem_subset_of_finset_subset_bunionᵢ

/- warning: directed_on.exists_mem_subset_of_finset_subset_bUnion -> DirectedOn.exists_mem_subset_of_finset_subset_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {f : ι -> (Set.{u1} α)} {c : Set.{u2} ι}, (Set.Nonempty.{u2} ι c) -> (DirectedOn.{u2} ι (fun (i : ι) (j : ι) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (f i) (f j)) c) -> (forall {s : Finset.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i c) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i c) => f i)))) -> (Exists.{succ u2} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i c) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i c) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (f i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {f : ι -> (Set.{u2} α)} {c : Set.{u1} ι}, (Set.Nonempty.{u1} ι c) -> (DirectedOn.{u1} ι (fun (i : ι) (j : ι) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (f i) (f j)) c) -> (forall {s : Finset.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α s) (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i c) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i c) => f i)))) -> (Exists.{succ u1} ι (fun (i : ι) => And (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i c) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Finset.toSet.{u2} α s) (f i)))))
Case conversion may be inaccurate. Consider using '#align directed_on.exists_mem_subset_of_finset_subset_bUnion DirectedOn.exists_mem_subset_of_finset_subset_bunionᵢₓ'. -/
theorem DirectedOn.exists_mem_subset_of_finset_subset_bunionᵢ {α ι : Type _} {f : ι → Set α}
    {c : Set ι} (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α}
    (hs : (s : Set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : Set α) ⊆ f i :=
  by
  rw [Set.bunionᵢ_eq_unionᵢ] at hs
  haveI := hn.coe_sort
  obtain ⟨⟨i, hic⟩, hi⟩ :=
    (directed_comp.2 hc.directed_coe).exists_mem_subset_of_finset_subset_bunionᵢ hs
  exact ⟨i, hic, hi⟩
#align directed_on.exists_mem_subset_of_finset_subset_bUnion DirectedOn.exists_mem_subset_of_finset_subset_bunionᵢ

/-! #### inter -/


#print Finset.inter_val_nd /-
theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl
#align finset.inter_val_nd Finset.inter_val_nd
-/

#print Finset.inter_val /-
@[simp]
theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
  ndinter_eq_inter s₁.2
#align finset.inter_val Finset.inter_val
-/

#print Finset.mem_inter /-
@[simp]
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  mem_ndinter
#align finset.mem_inter Finset.mem_inter
-/

#print Finset.mem_of_mem_inter_left /-
theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  (mem_inter.1 h).1
#align finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_left
-/

#print Finset.mem_of_mem_inter_right /-
theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  (mem_inter.1 h).2
#align finset.mem_of_mem_inter_right Finset.mem_of_mem_inter_right
-/

#print Finset.mem_inter_of_mem /-
theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  and_imp.1 mem_inter.2
#align finset.mem_inter_of_mem Finset.mem_inter_of_mem
-/

#print Finset.inter_subset_left /-
theorem inter_subset_left (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₁ := fun a => mem_of_mem_inter_left
#align finset.inter_subset_left Finset.inter_subset_left
-/

#print Finset.inter_subset_right /-
theorem inter_subset_right (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₂ := fun a => mem_of_mem_inter_right
#align finset.inter_subset_right Finset.inter_subset_right
-/

#print Finset.subset_inter /-
theorem subset_inter {s₁ s₂ u : Finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u := by
  simp (config := { contextual := true }) only [subset_iff, mem_inter] <;> intros <;>
      constructor <;>
    trivial
#align finset.subset_inter Finset.subset_inter
-/

/- warning: finset.coe_inter -> Finset.coe_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Finset.toSet.{u1} α s₁) (Finset.toSet.{u1} α s₂))
Case conversion may be inaccurate. Consider using '#align finset.coe_inter Finset.coe_interₓ'. -/
@[simp, norm_cast]
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext fun _ => mem_inter
#align finset.coe_inter Finset.coe_inter

#print Finset.union_inter_cancel_left /-
@[simp]
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_left]
#align finset.union_inter_cancel_left Finset.union_inter_cancel_left
-/

#print Finset.union_inter_cancel_right /-
@[simp]
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_right]
#align finset.union_inter_cancel_right Finset.union_inter_cancel_right
-/

#print Finset.inter_comm /-
theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
  ext fun _ => by simp only [mem_inter, and_comm']
#align finset.inter_comm Finset.inter_comm
-/

#print Finset.inter_assoc /-
@[simp]
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
  ext fun _ => by simp only [mem_inter, and_assoc']
#align finset.inter_assoc Finset.inter_assoc
-/

#print Finset.inter_left_comm /-
theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => by simp only [mem_inter, and_left_comm]
#align finset.inter_left_comm Finset.inter_left_comm
-/

#print Finset.inter_right_comm /-
theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => by simp only [mem_inter, and_right_comm]
#align finset.inter_right_comm Finset.inter_right_comm
-/

#print Finset.inter_self /-
@[simp]
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext fun _ => mem_inter.trans <| and_self_iff _
#align finset.inter_self Finset.inter_self
-/

#print Finset.inter_empty /-
@[simp]
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext fun _ => mem_inter.trans <| and_false_iff _
#align finset.inter_empty Finset.inter_empty
-/

#print Finset.empty_inter /-
@[simp]
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext fun _ => mem_inter.trans <| false_and_iff _
#align finset.empty_inter Finset.empty_inter
-/

#print Finset.inter_union_self /-
@[simp]
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s := by
  rw [inter_comm, union_inter_cancel_right]
#align finset.inter_union_self Finset.inter_union_self
-/

#print Finset.insert_inter_of_mem /-
@[simp]
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) :
    insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext fun x =>
    by
    have : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ := or_iff_right_of_imp <| by rintro rfl <;> exact h
    simp only [mem_inter, mem_insert, or_and_left, this]
#align finset.insert_inter_of_mem Finset.insert_inter_of_mem
-/

#print Finset.inter_insert_of_mem /-
@[simp]
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) :
    s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) := by rw [inter_comm, insert_inter_of_mem h, inter_comm]
#align finset.inter_insert_of_mem Finset.inter_insert_of_mem
-/

#print Finset.insert_inter_of_not_mem /-
@[simp]
theorem insert_inter_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) :
    insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x ∈ s₂) := by rintro ⟨rfl, H⟩ <;> exact h H
    simp only [mem_inter, mem_insert, or_and_right, this, false_or_iff]
#align finset.insert_inter_of_not_mem Finset.insert_inter_of_not_mem
-/

#print Finset.inter_insert_of_not_mem /-
@[simp]
theorem inter_insert_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) :
    s₁ ∩ insert a s₂ = s₁ ∩ s₂ := by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]
#align finset.inter_insert_of_not_mem Finset.inter_insert_of_not_mem
-/

#print Finset.singleton_inter_of_mem /-
@[simp]
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅ by rw [insert_inter_of_mem H, empty_inter]
#align finset.singleton_inter_of_mem Finset.singleton_inter_of_mem
-/

#print Finset.singleton_inter_of_not_mem /-
@[simp]
theorem singleton_inter_of_not_mem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [mem_inter, mem_singleton] <;> rintro x ⟨rfl, h⟩ <;> exact H h
#align finset.singleton_inter_of_not_mem Finset.singleton_inter_of_not_mem
-/

#print Finset.inter_singleton_of_mem /-
@[simp]
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} := by
  rw [inter_comm, singleton_inter_of_mem h]
#align finset.inter_singleton_of_mem Finset.inter_singleton_of_mem
-/

#print Finset.inter_singleton_of_not_mem /-
@[simp]
theorem inter_singleton_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ := by
  rw [inter_comm, singleton_inter_of_not_mem h]
#align finset.inter_singleton_of_not_mem Finset.inter_singleton_of_not_mem
-/

#print Finset.inter_subset_inter /-
@[mono]
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
  by
  intro a a_in
  rw [Finset.mem_inter] at a_in⊢
  exact ⟨h a_in.1, h' a_in.2⟩
#align finset.inter_subset_inter Finset.inter_subset_inter
-/

#print Finset.inter_subset_inter_left /-
theorem inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u :=
  inter_subset_inter Subset.rfl h
#align finset.inter_subset_inter_left Finset.inter_subset_inter_left
-/

#print Finset.inter_subset_inter_right /-
theorem inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter h Subset.rfl
#align finset.inter_subset_inter_right Finset.inter_subset_inter_right
-/

#print Finset.inter_subset_union /-
theorem inter_subset_union : s ∩ t ⊆ s ∪ t :=
  le_iff_subset.1 inf_le_sup
#align finset.inter_subset_union Finset.inter_subset_union
-/

instance : DistribLattice (Finset α) :=
  { Finset.lattice with
    le_sup_inf := fun a b c =>
      show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c by
        simp (config := { contextual := true }) only [subset_iff, mem_inter, mem_union, and_imp,
            or_imp] <;>
          simp only [true_or_iff, imp_true_iff, true_and_iff, or_true_iff] }

#print Finset.union_left_idem /-
@[simp]
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t :=
  sup_left_idem
#align finset.union_left_idem Finset.union_left_idem
-/

#print Finset.union_right_idem /-
@[simp]
theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t :=
  sup_right_idem
#align finset.union_right_idem Finset.union_right_idem
-/

#print Finset.inter_left_idem /-
@[simp]
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t :=
  inf_left_idem
#align finset.inter_left_idem Finset.inter_left_idem
-/

#print Finset.inter_right_idem /-
@[simp]
theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t :=
  inf_right_idem
#align finset.inter_right_idem Finset.inter_right_idem
-/

#print Finset.inter_distrib_left /-
theorem inter_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left
#align finset.inter_distrib_left Finset.inter_distrib_left
-/

#print Finset.inter_distrib_right /-
theorem inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right
#align finset.inter_distrib_right Finset.inter_distrib_right
-/

#print Finset.union_distrib_left /-
theorem union_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left
#align finset.union_distrib_left Finset.union_distrib_left
-/

#print Finset.union_distrib_right /-
theorem union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right
#align finset.union_distrib_right Finset.union_distrib_right
-/

#print Finset.union_union_distrib_left /-
theorem union_union_distrib_left (s t u : Finset α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _
#align finset.union_union_distrib_left Finset.union_union_distrib_left
-/

#print Finset.union_union_distrib_right /-
theorem union_union_distrib_right (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _
#align finset.union_union_distrib_right Finset.union_union_distrib_right
-/

#print Finset.inter_inter_distrib_left /-
theorem inter_inter_distrib_left (s t u : Finset α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _
#align finset.inter_inter_distrib_left Finset.inter_inter_distrib_left
-/

#print Finset.inter_inter_distrib_right /-
theorem inter_inter_distrib_right (s t u : Finset α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _
#align finset.inter_inter_distrib_right Finset.inter_inter_distrib_right
-/

#print Finset.union_union_union_comm /-
theorem union_union_union_comm (s t u v : Finset α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _
#align finset.union_union_union_comm Finset.union_union_union_comm
-/

#print Finset.inter_inter_inter_comm /-
theorem inter_inter_inter_comm (s t u v : Finset α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _
#align finset.inter_inter_inter_comm Finset.inter_inter_inter_comm
-/

#print Finset.union_eq_empty_iff /-
theorem union_eq_empty_iff (A B : Finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ :=
  sup_eq_bot_iff
#align finset.union_eq_empty_iff Finset.union_eq_empty_iff
-/

#print Finset.union_subset_iff /-
theorem union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)
#align finset.union_subset_iff Finset.union_subset_iff
-/

#print Finset.subset_inter_iff /-
theorem subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u :=
  (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)
#align finset.subset_inter_iff Finset.subset_inter_iff
-/

#print Finset.inter_eq_left_iff_subset /-
@[simp]
theorem inter_eq_left_iff_subset (s t : Finset α) : s ∩ t = s ↔ s ⊆ t :=
  inf_eq_left
#align finset.inter_eq_left_iff_subset Finset.inter_eq_left_iff_subset
-/

#print Finset.inter_eq_right_iff_subset /-
@[simp]
theorem inter_eq_right_iff_subset (s t : Finset α) : t ∩ s = s ↔ s ⊆ t :=
  inf_eq_right
#align finset.inter_eq_right_iff_subset Finset.inter_eq_right_iff_subset
-/

#print Finset.inter_congr_left /-
theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu
#align finset.inter_congr_left Finset.inter_congr_left
-/

#print Finset.inter_congr_right /-
theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht
#align finset.inter_congr_right Finset.inter_congr_right
-/

#print Finset.inter_eq_inter_iff_left /-
theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left
#align finset.inter_eq_inter_iff_left Finset.inter_eq_inter_iff_left
-/

#print Finset.inter_eq_inter_iff_right /-
theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right
#align finset.inter_eq_inter_iff_right Finset.inter_eq_inter_iff_right
-/

#print Finset.ite_subset_union /-
theorem ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' ⊆ s ∪ s' :=
  ite_le_sup s s' P
#align finset.ite_subset_union Finset.ite_subset_union
-/

#print Finset.inter_subset_ite /-
theorem inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s ∩ s' ⊆ ite P s s' :=
  inf_le_ite s s' P
#align finset.inter_subset_ite Finset.inter_subset_ite
-/

/- warning: finset.not_disjoint_iff_nonempty_inter -> Finset.not_disjoint_iff_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)) (Finset.Nonempty.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)) (Finset.Nonempty.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t))
Case conversion may be inaccurate. Consider using '#align finset.not_disjoint_iff_nonempty_inter Finset.not_disjoint_iff_nonempty_interₓ'. -/
theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s ∩ t).Nonempty :=
  not_disjoint_iff.trans <| by simp [Finset.Nonempty]
#align finset.not_disjoint_iff_nonempty_inter Finset.not_disjoint_iff_nonempty_inter

/- warning: finset.nonempty.not_disjoint -> Finset.Nonempty.not_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Finset.Nonempty.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) -> (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Finset.Nonempty.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) -> (Not (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.not_disjoint Finset.Nonempty.not_disjointₓ'. -/
alias not_disjoint_iff_nonempty_inter ↔ _ nonempty.not_disjoint
#align finset.nonempty.not_disjoint Finset.Nonempty.not_disjoint

/- warning: finset.disjoint_or_nonempty_inter -> Finset.disjoint_or_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) (Finset.Nonempty.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) (Finset.Nonempty.{u1} α (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_or_nonempty_inter Finset.disjoint_or_nonempty_interₓ'. -/
theorem disjoint_or_nonempty_inter (s t : Finset α) : Disjoint s t ∨ (s ∩ t).Nonempty :=
  by
  rw [← not_disjoint_iff_nonempty_inter]
  exact em _
#align finset.disjoint_or_nonempty_inter Finset.disjoint_or_nonempty_inter

end Lattice

/-! ### erase -/


section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

#print Finset.erase /-
/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, s.2.eraseₓ a⟩
#align finset.erase Finset.erase
-/

#print Finset.erase_val /-
@[simp]
theorem erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.eraseₓ a :=
  rfl
#align finset.erase_val Finset.erase_val
-/

#print Finset.mem_erase /-
@[simp]
theorem mem_erase {a b : α} {s : Finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
  s.2.mem_erase_iff
#align finset.mem_erase Finset.mem_erase
-/

#print Finset.not_mem_erase /-
theorem not_mem_erase (a : α) (s : Finset α) : a ∉ erase s a :=
  s.2.not_mem_erase
#align finset.not_mem_erase Finset.not_mem_erase
-/

#print Finset.erase_empty /-
-- While this can be solved by `simp`, this lemma is eligible for `dsimp`
@[nolint simp_nf, simp]
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl
#align finset.erase_empty Finset.erase_empty
-/

#print Finset.erase_singleton /-
@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).eraseₓ a = ∅ :=
  by
  ext x
  rw [mem_erase, mem_singleton, not_and_self_iff]
  rfl
#align finset.erase_singleton Finset.erase_singleton
-/

#print Finset.ne_of_mem_erase /-
theorem ne_of_mem_erase : b ∈ erase s a → b ≠ a := fun h => (mem_erase.1 h).1
#align finset.ne_of_mem_erase Finset.ne_of_mem_erase
-/

#print Finset.mem_of_mem_erase /-
theorem mem_of_mem_erase : b ∈ erase s a → b ∈ s :=
  mem_of_mem_erase
#align finset.mem_of_mem_erase Finset.mem_of_mem_erase
-/

#print Finset.mem_erase_of_ne_of_mem /-
theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b := by
  simp only [mem_erase] <;> exact And.intro
#align finset.mem_erase_of_ne_of_mem Finset.mem_erase_of_ne_of_mem
-/

#print Finset.eq_of_mem_of_not_mem_erase /-
/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
theorem eq_of_mem_of_not_mem_erase (hs : b ∈ s) (hsa : b ∉ s.eraseₓ a) : b = a :=
  by
  rw [mem_erase, not_and] at hsa
  exact not_imp_not.mp hsa hs
#align finset.eq_of_mem_of_not_mem_erase Finset.eq_of_mem_of_not_mem_erase
-/

#print Finset.erase_eq_of_not_mem /-
@[simp]
theorem erase_eq_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s :=
  eq_of_veq <| erase_of_not_mem h
#align finset.erase_eq_of_not_mem Finset.erase_eq_of_not_mem
-/

#print Finset.erase_eq_self /-
@[simp]
theorem erase_eq_self : s.eraseₓ a = s ↔ a ∉ s :=
  ⟨fun h => h ▸ not_mem_erase _ _, erase_eq_of_not_mem⟩
#align finset.erase_eq_self Finset.erase_eq_self
-/

#print Finset.erase_insert_eq_erase /-
@[simp]
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).eraseₓ a = s.eraseₓ a :=
  ext fun x => by
    simp (config := { contextual := true }) only [mem_erase, mem_insert, and_congr_right_iff,
      false_or_iff, iff_self_iff, imp_true_iff]
#align finset.erase_insert_eq_erase Finset.erase_insert_eq_erase
-/

#print Finset.erase_insert /-
theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : erase (insert a s) a = s := by
  rw [erase_insert_eq_erase, erase_eq_of_not_mem h]
#align finset.erase_insert Finset.erase_insert
-/

#print Finset.erase_insert_of_ne /-
theorem erase_insert_of_ne {a b : α} {s : Finset α} (h : a ≠ b) :
    erase (insert a s) b = insert a (erase s b) :=
  ext fun x =>
    by
    have : x ≠ b ∧ x = a ↔ x = a := and_iff_right_of_imp fun hx => hx.symm ▸ h
    simp only [mem_erase, mem_insert, and_or_left, this]
#align finset.erase_insert_of_ne Finset.erase_insert_of_ne
-/

#print Finset.erase_cons_of_ne /-
theorem erase_cons_of_ne {a b : α} {s : Finset α} (ha : a ∉ s) (hb : a ≠ b) :
    erase (cons a s ha) b = cons a (erase s b) fun h => ha <| erase_subset _ _ h := by
  simp only [cons_eq_insert, erase_insert_of_ne hb]
#align finset.erase_cons_of_ne Finset.erase_cons_of_ne
-/

#print Finset.insert_erase /-
theorem insert_erase {a : α} {s : Finset α} (h : a ∈ s) : insert a (erase s a) = s :=
  ext fun x => by
    simp only [mem_insert, mem_erase, or_and_left, dec_em, true_and_iff] <;>
          apply or_iff_right_of_imp <;>
        rintro rfl <;>
      exact h
#align finset.insert_erase Finset.insert_erase
-/

#print Finset.erase_subset_erase /-
theorem erase_subset_erase (a : α) {s t : Finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
  val_le_iff.1 <| erase_le_erase _ <| val_le_iff.2 h
#align finset.erase_subset_erase Finset.erase_subset_erase
-/

#print Finset.erase_subset /-
theorem erase_subset (a : α) (s : Finset α) : erase s a ⊆ s :=
  erase_subset _ _
#align finset.erase_subset Finset.erase_subset
-/

#print Finset.subset_erase /-
theorem subset_erase {a : α} {s t : Finset α} : s ⊆ t.eraseₓ a ↔ s ⊆ t ∧ a ∉ s :=
  ⟨fun h => ⟨h.trans (erase_subset _ _), fun ha => not_mem_erase _ _ (h ha)⟩, fun h b hb =>
    mem_erase.2 ⟨ne_of_mem_of_not_mem hb h.2, h.1 hb⟩⟩
#align finset.subset_erase Finset.subset_erase
-/

/- warning: finset.coe_erase -> Finset.coe_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (a : α) (s : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Finset.toSet.{u1} α s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))
Case conversion may be inaccurate. Consider using '#align finset.coe_erase Finset.coe_eraseₓ'. -/
@[simp, norm_cast]
theorem coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \ {a} : Set α) :=
  Set.ext fun _ => mem_erase.trans <| by rw [and_comm', Set.mem_diff, Set.mem_singleton_iff] <;> rfl
#align finset.coe_erase Finset.coe_erase

#print Finset.erase_ssubset /-
theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.eraseₓ a ⊂ s :=
  calc
    s.eraseₓ a ⊂ insert a (s.eraseₓ a) := ssubset_insert <| not_mem_erase _ _
    _ = _ := insert_erase h
    
#align finset.erase_ssubset Finset.erase_ssubset
-/

/- warning: finset.ssubset_iff_exists_subset_erase -> Finset.ssubset_iff_exists_subset_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s t) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t) => HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s t) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a))))
Case conversion may be inaccurate. Consider using '#align finset.ssubset_iff_exists_subset_erase Finset.ssubset_iff_exists_subset_eraseₓ'. -/
theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.eraseₓ a :=
  by
  refine' ⟨fun h => _, fun ⟨a, ha, h⟩ => ssubset_of_subset_of_ssubset h <| erase_ssubset ha⟩
  obtain ⟨a, ht, hs⟩ := not_subset.1 h.2
  exact ⟨a, ht, subset_erase.2 ⟨h.1, hs⟩⟩
#align finset.ssubset_iff_exists_subset_erase Finset.ssubset_iff_exists_subset_erase

#print Finset.erase_ssubset_insert /-
theorem erase_ssubset_insert (s : Finset α) (a : α) : s.eraseₓ a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2
    ⟨a, mem_insert_self _ _, erase_subset_erase _ <| subset_insert _ _⟩
#align finset.erase_ssubset_insert Finset.erase_ssubset_insert
-/

#print Finset.erase_ne_self /-
theorem erase_ne_self : s.eraseₓ a ≠ s ↔ a ∈ s :=
  erase_eq_self.not_left
#align finset.erase_ne_self Finset.erase_ne_self
-/

#print Finset.erase_cons /-
theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).eraseₓ a = s := by
  rw [cons_eq_insert, erase_insert_eq_erase, erase_eq_of_not_mem h]
#align finset.erase_cons Finset.erase_cons
-/

#print Finset.erase_idem /-
theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a := by simp
#align finset.erase_idem Finset.erase_idem
-/

#print Finset.erase_right_comm /-
theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a :=
  by
  ext x
  simp only [mem_erase, ← and_assoc']
  rw [and_comm' (x ≠ a)]
#align finset.erase_right_comm Finset.erase_right_comm
-/

#print Finset.subset_insert_iff /-
theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ erase s a ⊆ t := by
  simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp] <;>
    exact forall_congr' fun x => forall_swap
#align finset.subset_insert_iff Finset.subset_insert_iff
-/

#print Finset.erase_insert_subset /-
theorem erase_insert_subset (a : α) (s : Finset α) : erase (insert a s) a ⊆ s :=
  subset_insert_iff.1 <| Subset.rfl
#align finset.erase_insert_subset Finset.erase_insert_subset
-/

#print Finset.insert_erase_subset /-
theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (erase s a) :=
  subset_insert_iff.2 <| Subset.rfl
#align finset.insert_erase_subset Finset.insert_erase_subset
-/

#print Finset.subset_insert_iff_of_not_mem /-
theorem subset_insert_iff_of_not_mem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_not_mem h]
#align finset.subset_insert_iff_of_not_mem Finset.subset_insert_iff_of_not_mem
-/

#print Finset.erase_subset_iff_of_mem /-
theorem erase_subset_iff_of_mem (h : a ∈ t) : s.eraseₓ a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]
#align finset.erase_subset_iff_of_mem Finset.erase_subset_iff_of_mem
-/

#print Finset.erase_inj /-
theorem erase_inj {x y : α} (s : Finset α) (hx : x ∈ s) : s.eraseₓ x = s.eraseₓ y ↔ x = y :=
  by
  refine' ⟨fun h => _, congr_arg _⟩
  rw [eq_of_mem_of_not_mem_erase hx]
  rw [← h]
  simp
#align finset.erase_inj Finset.erase_inj
-/

#print Finset.erase_injOn /-
theorem erase_injOn (s : Finset α) : Set.InjOn s.eraseₓ s := fun _ _ _ _ => (erase_inj s ‹_›).mp
#align finset.erase_inj_on Finset.erase_injOn
-/

#print Finset.erase_injOn' /-
theorem erase_injOn' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => erase s a :=
  fun s hs t ht (h : s.eraseₓ a = _) => by rw [← insert_erase hs, ← insert_erase ht, h]
#align finset.erase_inj_on' Finset.erase_injOn'
-/

end Erase

/-! ### sdiff -/


section Sdiff

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : SDiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le tsub_le_self s₁.2⟩⟩

#print Finset.sdiff_val /-
@[simp]
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl
#align finset.sdiff_val Finset.sdiff_val
-/

#print Finset.mem_sdiff /-
@[simp]
theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=
  mem_sub_of_nodup s.2
#align finset.mem_sdiff Finset.mem_sdiff
-/

#print Finset.inter_sdiff_self /-
@[simp]
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [mem_inter, mem_sdiff] <;> rintro x ⟨h, _, hn⟩ <;> exact hn h
#align finset.inter_sdiff_self Finset.inter_sdiff_self
-/

instance : GeneralizedBooleanAlgebra (Finset α) :=
  { Finset.hasSdiff, Finset.distribLattice,
    Finset.orderBot with
    sup_inf_sdiff := fun x y =>
      by
      simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union, mem_inter]
      tauto
    inf_inf_sdiff := fun x y =>
      by
      simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc, false_iff_iff, inf_eq_inter,
        not_mem_empty]
      tauto }

#print Finset.not_mem_sdiff_of_mem_right /-
theorem not_mem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t := by
  simp only [mem_sdiff, h, not_true, not_false_iff, and_false_iff]
#align finset.not_mem_sdiff_of_mem_right Finset.not_mem_sdiff_of_mem_right
-/

#print Finset.not_mem_sdiff_of_not_mem_left /-
theorem not_mem_sdiff_of_not_mem_left (h : a ∉ s) : a ∉ s \ t := by simpa
#align finset.not_mem_sdiff_of_not_mem_left Finset.not_mem_sdiff_of_not_mem_left
-/

#print Finset.union_sdiff_of_subset /-
theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h
#align finset.union_sdiff_of_subset Finset.union_sdiff_of_subset
-/

#print Finset.sdiff_union_of_subset /-
theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ :=
  (union_comm _ _).trans (union_sdiff_of_subset h)
#align finset.sdiff_union_of_subset Finset.sdiff_union_of_subset
-/

#print Finset.inter_sdiff /-
theorem inter_sdiff (s t u : Finset α) : s ∩ (t \ u) = (s ∩ t) \ u :=
  by
  ext x
  simp [and_assoc']
#align finset.inter_sdiff Finset.inter_sdiff
-/

#print Finset.sdiff_inter_self /-
@[simp]
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left
#align finset.sdiff_inter_self Finset.sdiff_inter_self
-/

#print Finset.sdiff_self /-
@[simp]
theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  sdiff_self
#align finset.sdiff_self Finset.sdiff_self
-/

#print Finset.sdiff_inter_distrib_right /-
theorem sdiff_inter_distrib_right (s t u : Finset α) : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf
#align finset.sdiff_inter_distrib_right Finset.sdiff_inter_distrib_right
-/

#print Finset.sdiff_inter_self_left /-
@[simp]
theorem sdiff_inter_self_left (s t : Finset α) : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _
#align finset.sdiff_inter_self_left Finset.sdiff_inter_self_left
-/

#print Finset.sdiff_inter_self_right /-
@[simp]
theorem sdiff_inter_self_right (s t : Finset α) : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _
#align finset.sdiff_inter_self_right Finset.sdiff_inter_self_right
-/

#print Finset.sdiff_empty /-
@[simp]
theorem sdiff_empty : s \ ∅ = s :=
  sdiff_bot
#align finset.sdiff_empty Finset.sdiff_empty
-/

#print Finset.sdiff_subset_sdiff /-
@[mono]
theorem sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v :=
  sdiff_le_sdiff ‹s ≤ t› ‹v ≤ u›
#align finset.sdiff_subset_sdiff Finset.sdiff_subset_sdiff
-/

/- warning: finset.coe_sdiff -> Finset.coe_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Finset.toSet.{u1} α s₁) (Finset.toSet.{u1} α s₂))
Case conversion may be inaccurate. Consider using '#align finset.coe_sdiff Finset.coe_sdiffₓ'. -/
@[simp, norm_cast]
theorem coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext fun _ => mem_sdiff
#align finset.coe_sdiff Finset.coe_sdiff

#print Finset.union_sdiff_self_eq_union /-
@[simp]
theorem union_sdiff_self_eq_union : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right _ _
#align finset.union_sdiff_self_eq_union Finset.union_sdiff_self_eq_union
-/

#print Finset.sdiff_union_self_eq_union /-
@[simp]
theorem sdiff_union_self_eq_union : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left _ _
#align finset.sdiff_union_self_eq_union Finset.sdiff_union_self_eq_union
-/

#print Finset.union_sdiff_left /-
theorem union_sdiff_left (s t : Finset α) : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self
#align finset.union_sdiff_left Finset.union_sdiff_left
-/

#print Finset.union_sdiff_right /-
theorem union_sdiff_right (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
#align finset.union_sdiff_right Finset.union_sdiff_right
-/

/- warning: finset.union_sdiff_cancel_left -> Finset.union_sdiff_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s) t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s) t)
Case conversion may be inaccurate. Consider using '#align finset.union_sdiff_cancel_left Finset.union_sdiff_cancel_leftₓ'. -/
theorem union_sdiff_cancel_left (h : Disjoint s t) : (s ∪ t) \ s = t :=
  h.sup_sdiff_cancel_left
#align finset.union_sdiff_cancel_left Finset.union_sdiff_cancel_left

/- warning: finset.union_sdiff_cancel_right -> Finset.union_sdiff_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) t) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) t) s)
Case conversion may be inaccurate. Consider using '#align finset.union_sdiff_cancel_right Finset.union_sdiff_cancel_rightₓ'. -/
theorem union_sdiff_cancel_right (h : Disjoint s t) : (s ∪ t) \ t = s :=
  h.sup_sdiff_cancel_right
#align finset.union_sdiff_cancel_right Finset.union_sdiff_cancel_right

#print Finset.union_sdiff_symm /-
theorem union_sdiff_symm : s ∪ t \ s = t ∪ s \ t := by simp [union_comm]
#align finset.union_sdiff_symm Finset.union_sdiff_symm
-/

#print Finset.sdiff_union_inter /-
theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  sup_sdiff_inf _ _
#align finset.sdiff_union_inter Finset.sdiff_union_inter
-/

#print Finset.sdiff_idem /-
@[simp]
theorem sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t :=
  sdiff_idem
#align finset.sdiff_idem Finset.sdiff_idem
-/

/- warning: finset.subset_sdiff -> Finset.subset_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u)) (And (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {u : Finset.{u1} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t u)) (And (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) s t) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align finset.subset_sdiff Finset.subset_sdiffₓ'. -/
theorem subset_sdiff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u :=
  le_iff_subset.symm.trans le_sdiff
#align finset.subset_sdiff Finset.subset_sdiff

#print Finset.sdiff_eq_empty_iff_subset /-
@[simp]
theorem sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff
#align finset.sdiff_eq_empty_iff_subset Finset.sdiff_eq_empty_iff_subset
-/

#print Finset.sdiff_nonempty /-
theorem sdiff_nonempty : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.Not
#align finset.sdiff_nonempty Finset.sdiff_nonempty
-/

#print Finset.empty_sdiff /-
@[simp]
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff
#align finset.empty_sdiff Finset.empty_sdiff
-/

#print Finset.insert_sdiff_of_not_mem /-
theorem insert_sdiff_of_not_mem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) :
    insert x s \ t = insert x (s \ t) :=
  by
  rw [← coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert]
  exact Set.insert_diff_of_not_mem s h
#align finset.insert_sdiff_of_not_mem Finset.insert_sdiff_of_not_mem
-/

#print Finset.insert_sdiff_of_mem /-
theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x ∈ t) : insert x s \ t = s \ t :=
  by
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert]
  exact Set.insert_diff_of_mem s h
#align finset.insert_sdiff_of_mem Finset.insert_sdiff_of_mem
-/

#print Finset.insert_sdiff_insert /-
@[simp]
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)
#align finset.insert_sdiff_insert Finset.insert_sdiff_insert
-/

#print Finset.sdiff_insert_of_not_mem /-
theorem sdiff_insert_of_not_mem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t :=
  by
  refine' subset.antisymm (sdiff_subset_sdiff (subset.refl _) (subset_insert _ _)) fun y hy => _
  simp only [mem_sdiff, mem_insert, not_or] at hy⊢
  exact ⟨hy.1, fun hxy => h <| hxy ▸ hy.1, hy.2⟩
#align finset.sdiff_insert_of_not_mem Finset.sdiff_insert_of_not_mem
-/

#print Finset.sdiff_subset /-
@[simp]
theorem sdiff_subset (s t : Finset α) : s \ t ⊆ s :=
  show s \ t ≤ s from sdiff_le
#align finset.sdiff_subset Finset.sdiff_subset
-/

#print Finset.sdiff_ssubset /-
theorem sdiff_ssubset (h : t ⊆ s) (ht : t.Nonempty) : s \ t ⊂ s :=
  sdiff_lt ‹t ≤ s› ht.ne_empty
#align finset.sdiff_ssubset Finset.sdiff_ssubset
-/

#print Finset.union_sdiff_distrib /-
theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sup_sdiff
#align finset.union_sdiff_distrib Finset.union_sdiff_distrib
-/

#print Finset.sdiff_union_distrib /-
theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sdiff_sup
#align finset.sdiff_union_distrib Finset.sdiff_union_distrib
-/

#print Finset.union_sdiff_self /-
theorem union_sdiff_self (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
#align finset.union_sdiff_self Finset.union_sdiff_self
-/

#print Finset.sdiff_singleton_eq_erase /-
-- TODO: Do we want to delete this lemma and `finset.disj_union_singleton`,
-- or instead add `finset.union_singleton`/`finset.singleton_union`?
theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ singleton a = erase s a :=
  by
  ext
  rw [mem_erase, mem_sdiff, mem_singleton]
  tauto
#align finset.sdiff_singleton_eq_erase Finset.sdiff_singleton_eq_erase
-/

#print Finset.erase_eq /-
-- This lemma matches `finset.insert_eq` in functionality.
theorem erase_eq (s : Finset α) (a : α) : s.eraseₓ a = s \ {a} :=
  (sdiff_singleton_eq_erase _ _).symm
#align finset.erase_eq Finset.erase_eq
-/

/- warning: finset.disjoint_erase_comm -> Finset.disjoint_erase_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) t) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) t) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_erase_comm Finset.disjoint_erase_commₓ'. -/
theorem disjoint_erase_comm : Disjoint (s.eraseₓ a) t ↔ Disjoint s (t.eraseₓ a) := by
  simp_rw [erase_eq, disjoint_sdiff_comm]
#align finset.disjoint_erase_comm Finset.disjoint_erase_comm

/- warning: finset.disjoint_of_erase_left -> Finset.disjoint_of_erase_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s a) t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_of_erase_left Finset.disjoint_of_erase_leftₓ'. -/
theorem disjoint_of_erase_left (ha : a ∉ t) (hst : Disjoint (s.eraseₓ a) t) : Disjoint s t :=
  by
  rw [← erase_insert ha, ← disjoint_erase_comm, disjoint_insert_right]
  exact ⟨not_mem_erase _ _, hst⟩
#align finset.disjoint_of_erase_left Finset.disjoint_of_erase_left

/- warning: finset.disjoint_of_erase_right -> Finset.disjoint_of_erase_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t a)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_of_erase_right Finset.disjoint_of_erase_rightₓ'. -/
theorem disjoint_of_erase_right (ha : a ∉ s) (hst : Disjoint s (t.eraseₓ a)) : Disjoint s t :=
  by
  rw [← erase_insert ha, disjoint_erase_comm, disjoint_insert_left]
  exact ⟨not_mem_erase _ _, hst⟩
#align finset.disjoint_of_erase_right Finset.disjoint_of_erase_right

#print Finset.inter_erase /-
@[simp]
theorem inter_erase (a : α) (s t : Finset α) : s ∩ t.eraseₓ a = (s ∩ t).eraseₓ a := by
  simp only [erase_eq, inter_sdiff]
#align finset.inter_erase Finset.inter_erase
-/

#print Finset.erase_inter /-
@[simp]
theorem erase_inter (a : α) (s t : Finset α) : s.eraseₓ a ∩ t = (s ∩ t).eraseₓ a := by
  simpa only [inter_comm t] using inter_erase a t s
#align finset.erase_inter Finset.erase_inter
-/

#print Finset.erase_sdiff_comm /-
theorem erase_sdiff_comm (s t : Finset α) (a : α) : s.eraseₓ a \ t = (s \ t).eraseₓ a := by
  simp_rw [erase_eq, sdiff_right_comm]
#align finset.erase_sdiff_comm Finset.erase_sdiff_comm
-/

#print Finset.insert_union_comm /-
theorem insert_union_comm (s t : Finset α) (a : α) : insert a s ∪ t = s ∪ insert a t := by
  rw [insert_union, union_insert]
#align finset.insert_union_comm Finset.insert_union_comm
-/

#print Finset.erase_inter_comm /-
theorem erase_inter_comm (s t : Finset α) (a : α) : s.eraseₓ a ∩ t = s ∩ t.eraseₓ a := by
  rw [erase_inter, inter_erase]
#align finset.erase_inter_comm Finset.erase_inter_comm
-/

#print Finset.erase_union_distrib /-
theorem erase_union_distrib (s t : Finset α) (a : α) : (s ∪ t).eraseₓ a = s.eraseₓ a ∪ t.eraseₓ a :=
  by simp_rw [erase_eq, union_sdiff_distrib]
#align finset.erase_union_distrib Finset.erase_union_distrib
-/

#print Finset.insert_inter_distrib /-
theorem insert_inter_distrib (s t : Finset α) (a : α) :
    insert a (s ∩ t) = insert a s ∩ insert a t := by simp_rw [insert_eq, union_distrib_left]
#align finset.insert_inter_distrib Finset.insert_inter_distrib
-/

#print Finset.erase_sdiff_distrib /-
theorem erase_sdiff_distrib (s t : Finset α) (a : α) : (s \ t).eraseₓ a = s.eraseₓ a \ t.eraseₓ a :=
  by simp_rw [erase_eq, sdiff_sdiff, sup_sdiff_eq_sup le_rfl, sup_comm]
#align finset.erase_sdiff_distrib Finset.erase_sdiff_distrib
-/

#print Finset.erase_union_of_mem /-
theorem erase_union_of_mem (ha : a ∈ t) (s : Finset α) : s.eraseₓ a ∪ t = s ∪ t := by
  rw [← insert_erase (mem_union_right s ha), erase_union_distrib, ← union_insert, insert_erase ha]
#align finset.erase_union_of_mem Finset.erase_union_of_mem
-/

#print Finset.union_erase_of_mem /-
theorem union_erase_of_mem (ha : a ∈ s) (t : Finset α) : s ∪ t.eraseₓ a = s ∪ t := by
  rw [← insert_erase (mem_union_left t ha), erase_union_distrib, ← insert_union, insert_erase ha]
#align finset.union_erase_of_mem Finset.union_erase_of_mem
-/

#print Finset.sdiff_singleton_eq_self /-
@[simp]
theorem sdiff_singleton_eq_self (ha : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [ha]
#align finset.sdiff_singleton_eq_self Finset.sdiff_singleton_eq_self
-/

#print Finset.sdiff_sdiff_left' /-
theorem sdiff_sdiff_left' (s t u : Finset α) : (s \ t) \ u = s \ t ∩ (s \ u) :=
  sdiff_sdiff_left'
#align finset.sdiff_sdiff_left' Finset.sdiff_sdiff_left'
-/

#print Finset.sdiff_union_sdiff_cancel /-
theorem sdiff_union_sdiff_cancel (hts : t ⊆ s) (hut : u ⊆ t) : s \ t ∪ t \ u = s \ u :=
  sdiff_sup_sdiff_cancel hts hut
#align finset.sdiff_union_sdiff_cancel Finset.sdiff_union_sdiff_cancel
-/

#print Finset.sdiff_union_erase_cancel /-
theorem sdiff_union_erase_cancel (hts : t ⊆ s) (ha : a ∈ t) : s \ t ∪ t.eraseₓ a = s.eraseₓ a := by
  simp_rw [erase_eq, sdiff_union_sdiff_cancel hts (singleton_subset_iff.2 ha)]
#align finset.sdiff_union_erase_cancel Finset.sdiff_union_erase_cancel
-/

#print Finset.sdiff_sdiff_eq_sdiff_union /-
theorem sdiff_sdiff_eq_sdiff_union (h : u ⊆ s) : s \ (t \ u) = s \ t ∪ u :=
  sdiff_sdiff_eq_sdiff_sup h
#align finset.sdiff_sdiff_eq_sdiff_union Finset.sdiff_sdiff_eq_sdiff_union
-/

#print Finset.sdiff_insert /-
theorem sdiff_insert (s t : Finset α) (x : α) : s \ insert x t = (s \ t).eraseₓ x := by
  simp_rw [← sdiff_singleton_eq_erase, insert_eq, sdiff_sdiff_left', sdiff_union_distrib,
    inter_comm]
#align finset.sdiff_insert Finset.sdiff_insert
-/

#print Finset.sdiff_insert_insert_of_mem_of_not_mem /-
theorem sdiff_insert_insert_of_mem_of_not_mem {s t : Finset α} {x : α} (hxs : x ∈ s) (hxt : x ∉ t) :
    insert x (s \ insert x t) = s \ t := by
  rw [sdiff_insert, insert_erase (mem_sdiff.mpr ⟨hxs, hxt⟩)]
#align finset.sdiff_insert_insert_of_mem_of_not_mem Finset.sdiff_insert_insert_of_mem_of_not_mem
-/

#print Finset.sdiff_erase /-
theorem sdiff_erase (h : a ∈ s) : s \ t.eraseₓ a = insert a (s \ t) := by
  rw [← sdiff_singleton_eq_erase, sdiff_sdiff_eq_sdiff_union (singleton_subset_iff.2 h), insert_eq,
    union_comm]
#align finset.sdiff_erase Finset.sdiff_erase
-/

#print Finset.sdiff_erase_self /-
theorem sdiff_erase_self (ha : a ∈ s) : s \ s.eraseₓ a = {a} := by
  rw [sdiff_erase ha, sdiff_self, insert_emptyc_eq]
#align finset.sdiff_erase_self Finset.sdiff_erase_self
-/

#print Finset.sdiff_sdiff_self_left /-
theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self
#align finset.sdiff_sdiff_self_left Finset.sdiff_sdiff_self_left
-/

#print Finset.sdiff_sdiff_eq_self /-
theorem sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t :=
  sdiff_sdiff_eq_self h
#align finset.sdiff_sdiff_eq_self Finset.sdiff_sdiff_eq_self
-/

#print Finset.sdiff_eq_sdiff_iff_inter_eq_inter /-
theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} :
    s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf
#align finset.sdiff_eq_sdiff_iff_inter_eq_inter Finset.sdiff_eq_sdiff_iff_inter_eq_inter
-/

#print Finset.union_eq_sdiff_union_sdiff_union_inter /-
theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf
#align finset.union_eq_sdiff_union_sdiff_union_inter Finset.union_eq_sdiff_union_sdiff_union_inter
-/

#print Finset.erase_eq_empty_iff /-
theorem erase_eq_empty_iff (s : Finset α) (a : α) : s.eraseₓ a = ∅ ↔ s = ∅ ∨ s = {a} := by
  rw [← sdiff_singleton_eq_erase, sdiff_eq_empty_iff_subset, subset_singleton_iff]
#align finset.erase_eq_empty_iff Finset.erase_eq_empty_iff
-/

/- warning: finset.sdiff_disjoint -> Finset.sdiff_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s) s
Case conversion may be inaccurate. Consider using '#align finset.sdiff_disjoint Finset.sdiff_disjointₓ'. -/
--TODO@Yaël: Kill lemmas duplicate with `boolean_algebra`
theorem sdiff_disjoint : Disjoint (t \ s) s :=
  disjoint_left.2 fun a ha => (mem_sdiff.1 ha).2
#align finset.sdiff_disjoint Finset.sdiff_disjoint

/- warning: finset.disjoint_sdiff -> Finset.disjoint_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) t s)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_sdiff Finset.disjoint_sdiffₓ'. -/
theorem disjoint_sdiff : Disjoint s (t \ s) :=
  sdiff_disjoint.symm
#align finset.disjoint_sdiff Finset.disjoint_sdiff

/- warning: finset.disjoint_sdiff_inter -> Finset.disjoint_sdiff_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_sdiff_inter Finset.disjoint_sdiff_interₓ'. -/
theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint
#align finset.disjoint_sdiff_inter Finset.disjoint_sdiff_inter

/- warning: finset.sdiff_eq_self_iff_disjoint -> Finset.sdiff_eq_self_iff_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.sdiff_eq_self_iff_disjoint Finset.sdiff_eq_self_iff_disjointₓ'. -/
theorem sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t :=
  sdiff_eq_self_iff_disjoint'
#align finset.sdiff_eq_self_iff_disjoint Finset.sdiff_eq_self_iff_disjoint

/- warning: finset.sdiff_eq_self_of_disjoint -> Finset.sdiff_eq_self_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} α) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t) s)
Case conversion may be inaccurate. Consider using '#align finset.sdiff_eq_self_of_disjoint Finset.sdiff_eq_self_of_disjointₓ'. -/
theorem sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h
#align finset.sdiff_eq_self_of_disjoint Finset.sdiff_eq_self_of_disjoint

end Sdiff

/-! ### Symmetric difference -/


section symmDiff

variable [DecidableEq α] {s t : Finset α} {a b : α}

/- warning: finset.mem_symm_diff -> Finset.mem_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Or (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t))) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a t) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Or (And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t))) (And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a t) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))))
Case conversion may be inaccurate. Consider using '#align finset.mem_symm_diff Finset.mem_symmDiffₓ'. -/
theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := by
  simp_rw [symmDiff, sup_eq_union, mem_union, mem_sdiff]
#align finset.mem_symm_diff Finset.mem_symmDiff

/- warning: finset.coe_symm_diff -> Finset.coe_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Finset.toSet.{u1} α (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) (Finset.toSet.{u1} α s) (Finset.toSet.{u1} α t))
Case conversion may be inaccurate. Consider using '#align finset.coe_symm_diff Finset.coe_symmDiffₓ'. -/
@[simp, norm_cast]
theorem coe_symmDiff : (↑(s ∆ t) : Set α) = s ∆ t :=
  Set.ext fun _ => mem_symmDiff
#align finset.coe_symm_diff Finset.coe_symmDiff

end symmDiff

/-! ### attach -/


#print Finset.attach /-
/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨attach s.1, nodup_attach.2 s.2⟩
#align finset.attach Finset.attach
-/

#print Finset.sizeOf_lt_sizeOf_of_mem /-
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {s : Finset α} (hx : x ∈ s) :
    SizeOf.sizeOf x < SizeOf.sizeOf s := by
  cases s
  dsimp [SizeOf.sizeOf, SizeOf.sizeOf, Finset.sizeof]
  apply lt_add_left
  exact Multiset.sizeOf_lt_sizeOf_of_mem hx
#align finset.sizeof_lt_sizeof_of_mem Finset.sizeOf_lt_sizeOf_of_mem
-/

#print Finset.attach_val /-
@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl
#align finset.attach_val Finset.attach_val
-/

#print Finset.mem_attach /-
@[simp]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  mem_attach _
#align finset.mem_attach Finset.mem_attach
-/

#print Finset.attach_empty /-
@[simp]
theorem attach_empty : attach (∅ : Finset α) = ∅ :=
  rfl
#align finset.attach_empty Finset.attach_empty
-/

#print Finset.attach_nonempty_iff /-
@[simp]
theorem attach_nonempty_iff (s : Finset α) : s.attach.Nonempty ↔ s.Nonempty := by
  simp [Finset.Nonempty]
#align finset.attach_nonempty_iff Finset.attach_nonempty_iff
-/

#print Finset.attach_eq_empty_iff /-
@[simp]
theorem attach_eq_empty_iff (s : Finset α) : s.attach = ∅ ↔ s = ∅ := by
  simpa [eq_empty_iff_forall_not_mem]
#align finset.attach_eq_empty_iff Finset.attach_eq_empty_iff
-/

/-! ### piecewise -/


section Piecewise

#print Finset.piecewise /-
/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type _} {δ : α → Sort _} (s : Finset α) (f g : ∀ i, δ i)
    [∀ j, Decidable (j ∈ s)] : ∀ i, δ i := fun i => if i ∈ s then f i else g i
#align finset.piecewise Finset.piecewise
-/

variable {δ : α → Sort _} (s : Finset α) (f g : ∀ i, δ i)

/- warning: finset.piecewise_insert_self -> Finset.piecewise_insert_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : DecidableEq.{succ u1} α] {j : α} [_inst_2 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) j s))], Eq.{u2} (δ j) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) j s) f g (fun (j : α) => _inst_2 j) j) (f j)
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : DecidableEq.{succ u2} α] {j : α} [_inst_2 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) j s))], Eq.{u1} (δ j) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) j s) f g (fun (j : α) => _inst_2 j) j) (f j)
Case conversion may be inaccurate. Consider using '#align finset.piecewise_insert_self Finset.piecewise_insert_selfₓ'. -/
@[simp]
theorem piecewise_insert_self [DecidableEq α] {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
#align finset.piecewise_insert_self Finset.piecewise_insert_self

/- warning: finset.piecewise_empty -> Finset.piecewise_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))], Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) f g (fun (j : α) => _inst_1 j)) g
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)))], Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)) f g (fun (j : α) => _inst_1 j)) g
Case conversion may be inaccurate. Consider using '#align finset.piecewise_empty Finset.piecewise_emptyₓ'. -/
@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Finset α))] : piecewise ∅ f g = g :=
  by
  ext i
  simp [piecewise]
#align finset.piecewise_empty Finset.piecewise_empty

variable [∀ j, Decidable (j ∈ s)]

/- warning: finset.piecewise_coe -> Finset.piecewise_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] [_inst_2 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) j ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))], Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Set.piecewise.{u1, u2} α (fun (i : α) => δ i) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) f g (fun (j : α) => _inst_2 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] [_inst_2 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) j (Finset.toSet.{u2} α s))], Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Set.piecewise.{u2, u1} α (fun (i : α) => δ i) (Finset.toSet.{u2} α s) f g (fun (j : α) => _inst_2 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_coe Finset.piecewise_coeₓ'. -/
-- TODO: fix this in norm_cast
@[norm_cast move]
theorem piecewise_coe [∀ j, Decidable (j ∈ (s : Set α))] :
    (s : Set α).piecewise f g = s.piecewise f g :=
  by
  ext
  congr
#align finset.piecewise_coe Finset.piecewise_coe

/- warning: finset.piecewise_eq_of_mem -> Finset.piecewise_eq_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] {i : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (Eq.{u2} (δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) i) (f i))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] {i : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (Eq.{u1} (δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) i) (f i))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_eq_of_mem Finset.piecewise_eq_of_memₓ'. -/
@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i := by
  simp [piecewise, hi]
#align finset.piecewise_eq_of_mem Finset.piecewise_eq_of_mem

/- warning: finset.piecewise_eq_of_not_mem -> Finset.piecewise_eq_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] {i : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s)) -> (Eq.{u2} (δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) i) (g i))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] {i : α}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s)) -> (Eq.{u1} (δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) i) (g i))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_eq_of_not_mem Finset.piecewise_eq_of_not_memₓ'. -/
@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i := by
  simp [piecewise, hi]
#align finset.piecewise_eq_of_not_mem Finset.piecewise_eq_of_not_mem

/- warning: finset.piecewise_congr -> Finset.piecewise_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] {f : forall (i : α), δ i} {f' : forall (i : α), δ i} {g : forall (i : α), δ i} {g' : forall (i : α), δ i}, (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (Eq.{u2} (δ i) (f i) (f' i))) -> (forall (i : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s)) -> (Eq.{u2} (δ i) (g i) (g' i))) -> (Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f' g' (fun (j : α) => _inst_1 j)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] {f : forall (i : α), δ i} {f' : forall (i : α), δ i} {g : forall (i : α), δ i} {g' : forall (i : α), δ i}, (forall (i : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (Eq.{u1} (δ i) (f i) (f' i))) -> (forall (i : α), (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s)) -> (Eq.{u1} (δ i) (g i) (g' i))) -> (Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f' g' (fun (j : α) => _inst_1 j)))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_congr Finset.piecewise_congrₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem piecewise_congr {f f' g g' : ∀ i, δ i} (hf : ∀ i ∈ s, f i = f' i)
    (hg : ∀ (i) (_ : i ∉ s), g i = g' i) : s.piecewise f g = s.piecewise f' g' :=
  funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)
#align finset.piecewise_congr Finset.piecewise_congr

/- warning: finset.piecewise_insert_of_ne -> Finset.piecewise_insert_of_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] [_inst_2 : DecidableEq.{succ u1} α] {i : α} {j : α} [_inst_3 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) j s))], (Ne.{succ u1} α i j) -> (Eq.{u2} (δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) j s) f g (fun (j : α) => _inst_3 j) i) (Finset.piecewise.{u1, u2} α δ s f g (fun (j : α) => _inst_1 j) i))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] [_inst_2 : DecidableEq.{succ u2} α] {i : α} {j : α} [_inst_3 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) j s))], (Ne.{succ u2} α i j) -> (Eq.{u1} (δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) j s) f g (fun (j : α) => _inst_3 j) i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) i))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_insert_of_ne Finset.piecewise_insert_of_neₓ'. -/
@[simp]
theorem piecewise_insert_of_ne [DecidableEq α] {i j : α} [∀ i, Decidable (i ∈ insert j s)]
    (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
#align finset.piecewise_insert_of_ne Finset.piecewise_insert_of_ne

/- warning: finset.piecewise_insert -> Finset.piecewise_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] [_inst_2 : DecidableEq.{succ u1} α] (j : α) [_inst_3 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) j s))], Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) j s) f g (fun (j : α) => _inst_3 j)) (Function.update.{succ u1, u2} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s f g (fun (j : α) => _inst_1 j)) j (f j))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] [_inst_2 : DecidableEq.{succ u2} α] (j : α) [_inst_3 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) j s))], Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) j s) f g (fun (j : α) => _inst_3 j)) (Function.update.{succ u2, u1} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s f g (fun (j : α) => _inst_1 j)) j (f j))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_insert Finset.piecewise_insertₓ'. -/
theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = update (s.piecewise f g) j (f j) := by
  classical simp only [← piecewise_coe, coe_insert, ← Set.piecewise_insert]
#align finset.piecewise_insert Finset.piecewise_insert

/- warning: finset.piecewise_cases -> Finset.piecewise_cases is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] {i : α} (p : (δ i) -> Prop), (p (f i)) -> (p (g i)) -> (p (Finset.piecewise.{u1, u2} α δ s f g (fun (j : α) => _inst_1 j) i))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] {i : α} (p : (δ i) -> Prop), (p (f i)) -> (p (g i)) -> (p (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j) i))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_cases Finset.piecewise_casesₓ'. -/
theorem piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) :
    p (s.piecewise f g i) := by by_cases hi : i ∈ s <;> simpa [hi]
#align finset.piecewise_cases Finset.piecewise_cases

#print Finset.piecewise_mem_set_pi /-
theorem piecewise_mem_set_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g}
    (hf : f ∈ Set.pi t t') (hg : g ∈ Set.pi t t') : s.piecewise f g ∈ Set.pi t t' := by
  classical
    rw [← piecewise_coe]
    exact Set.piecewise_mem_pi (↑s) hf hg
#align finset.piecewise_mem_set_pi Finset.piecewise_mem_set_pi
-/

/- warning: finset.piecewise_singleton -> Finset.piecewise_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_2 : DecidableEq.{succ u1} α] (i : α), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) i) f g (fun (j : α) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) j (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) i))) (Function.update.{succ u1, u2} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) g i (f i))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_2 : DecidableEq.{succ u2} α] (i : α), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) i) f g (fun (j : α) => Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_2 a b) j (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) i))) (Function.update.{succ u2, u1} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) g i (f i))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_singleton Finset.piecewise_singletonₓ'. -/
theorem piecewise_singleton [DecidableEq α] (i : α) : piecewise {i} f g = update g i (f i) := by
  rw [← insert_emptyc_eq, piecewise_insert, piecewise_empty]
#align finset.piecewise_singleton Finset.piecewise_singleton

/- warning: finset.piecewise_piecewise_of_subset_left -> Finset.piecewise_piecewise_of_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_2 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s)] [_inst_3 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t)], (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t) -> (forall (f₁ : forall (a : α), δ a) (f₂ : forall (a : α), δ a) (g : forall (a : α), δ a), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) t f₁ f₂ (fun (j : α) => _inst_3 j)) g (fun (j : α) => _inst_2 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f₁ g (fun (j : α) => _inst_2 j)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} {s : Finset.{u2} α} {t : Finset.{u2} α} [_inst_2 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s)] [_inst_3 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t)], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s t) -> (forall (f₁ : forall (a : α), δ a) (f₂ : forall (a : α), δ a) (g : forall (a : α), δ a), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) t f₁ f₂ (fun (j : α) => _inst_3 j)) g (fun (j : α) => _inst_2 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f₁ g (fun (j : α) => _inst_2 j)))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_piecewise_of_subset_left Finset.piecewise_piecewise_of_subset_leftₓ'. -/
theorem piecewise_piecewise_of_subset_left {s t : Finset α} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : ∀ a, δ a) :
    s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl
#align finset.piecewise_piecewise_of_subset_left Finset.piecewise_piecewise_of_subset_left

/- warning: finset.piecewise_idem_left -> Finset.piecewise_idem_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] (f₁ : forall (a : α), δ a) (f₂ : forall (a : α), δ a) (g : forall (a : α), δ a), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s f₁ f₂ (fun (j : α) => _inst_1 j)) g (fun (j : α) => _inst_1 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f₁ g (fun (j : α) => _inst_1 j))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] (f₁ : forall (a : α), δ a) (f₂ : forall (a : α), δ a) (g : forall (a : α), δ a), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s f₁ f₂ (fun (j : α) => _inst_1 j)) g (fun (j : α) => _inst_1 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f₁ g (fun (j : α) => _inst_1 j))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_idem_left Finset.piecewise_idem_leftₓ'. -/
@[simp]
theorem piecewise_idem_left (f₁ f₂ g : ∀ a, δ a) :
    s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _
#align finset.piecewise_idem_left Finset.piecewise_idem_left

/- warning: finset.piecewise_piecewise_of_subset_right -> Finset.piecewise_piecewise_of_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} {s : Finset.{u1} α} {t : Finset.{u1} α} [_inst_2 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s)] [_inst_3 : forall (i : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t)], (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t s) -> (forall (f : forall (a : α), δ a) (g₁ : forall (a : α), δ a) (g₂ : forall (a : α), δ a), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s f (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) t g₁ g₂ (fun (j : α) => _inst_3 j)) (fun (j : α) => _inst_2 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g₂ (fun (j : α) => _inst_2 j)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} {s : Finset.{u2} α} {t : Finset.{u2} α} [_inst_2 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s)] [_inst_3 : forall (i : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i t)], (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) t s) -> (forall (f : forall (a : α), δ a) (g₁ : forall (a : α), δ a) (g₂ : forall (a : α), δ a), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s f (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) t g₁ g₂ (fun (j : α) => _inst_3 j)) (fun (j : α) => _inst_2 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g₂ (fun (j : α) => _inst_2 j)))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_piecewise_of_subset_right Finset.piecewise_piecewise_of_subset_rightₓ'. -/
theorem piecewise_piecewise_of_subset_right {s t : Finset α} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : ∀ a, δ a) :
    s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun i hi => t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi)
#align finset.piecewise_piecewise_of_subset_right Finset.piecewise_piecewise_of_subset_right

/- warning: finset.piecewise_idem_right -> Finset.piecewise_idem_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] (f : forall (a : α), δ a) (g₁ : forall (a : α), δ a) (g₂ : forall (a : α), δ a), Eq.{imax (succ u1) u2} (forall (i : α), δ i) (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s f (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s g₁ g₂ (fun (j : α) => _inst_1 j)) (fun (j : α) => _inst_1 j)) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g₂ (fun (j : α) => _inst_1 j))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] (f : forall (a : α), δ a) (g₁ : forall (a : α), δ a) (g₂ : forall (a : α), δ a), Eq.{imax (succ u2) u1} (forall (i : α), δ i) (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s f (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s g₁ g₂ (fun (j : α) => _inst_1 j)) (fun (j : α) => _inst_1 j)) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g₂ (fun (j : α) => _inst_1 j))
Case conversion may be inaccurate. Consider using '#align finset.piecewise_idem_right Finset.piecewise_idem_rightₓ'. -/
@[simp]
theorem piecewise_idem_right (f g₁ g₂ : ∀ a, δ a) :
    s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂
#align finset.piecewise_idem_right Finset.piecewise_idem_right

#print Finset.update_eq_piecewise /-
theorem update_eq_piecewise {β : Type _} [DecidableEq α] (f : α → β) (i : α) (v : β) :
    update f i v = piecewise (singleton i) (fun j => v) f :=
  (piecewise_singleton _ _ _).symm
#align finset.update_eq_piecewise Finset.update_eq_piecewise
-/

/- warning: finset.update_piecewise -> Finset.update_piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] [_inst_2 : DecidableEq.{succ u1} α] (i : α) (v : δ i), Eq.{imax (succ u1) u2} (forall (a : α), δ a) (Function.update.{succ u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) i v) (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s (Function.update.{succ u1, u2} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) f i v) (Function.update.{succ u1, u2} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) g i v) (fun (j : α) => _inst_1 j))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] [_inst_2 : DecidableEq.{succ u2} α] (i : α) (v : δ i), Eq.{imax (succ u2) u1} (forall (a : α), δ a) (Function.update.{succ u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) i v) (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s (Function.update.{succ u2, u1} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) f i v) (Function.update.{succ u2, u1} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) g i v) (fun (j : α) => _inst_1 j))
Case conversion may be inaccurate. Consider using '#align finset.update_piecewise Finset.update_piecewiseₓ'. -/
theorem update_piecewise [DecidableEq α] (i : α) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) :=
  by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j ∈ s <;> simp [*]
#align finset.update_piecewise Finset.update_piecewise

/- warning: finset.update_piecewise_of_mem -> Finset.update_piecewise_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] [_inst_2 : DecidableEq.{succ u1} α] {i : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (forall (v : δ i), Eq.{imax (succ u1) u2} (forall (a : α), δ a) (Function.update.{succ u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) i v) (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s (Function.update.{succ u1, u2} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) f i v) g (fun (j : α) => _inst_1 j)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] [_inst_2 : DecidableEq.{succ u2} α] {i : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (forall (v : δ i), Eq.{imax (succ u2) u1} (forall (a : α), δ a) (Function.update.{succ u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) i v) (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s (Function.update.{succ u2, u1} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) f i v) g (fun (j : α) => _inst_1 j)))
Case conversion may be inaccurate. Consider using '#align finset.update_piecewise_of_mem Finset.update_piecewise_of_memₓ'. -/
theorem update_piecewise_of_mem [DecidableEq α] {i : α} (hi : i ∈ s) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) g :=
  by
  rw [update_piecewise]
  refine' s.piecewise_congr (fun _ _ => rfl) fun j hj => update_noteq _ _ _
  exact fun h => hj (h.symm ▸ hi)
#align finset.update_piecewise_of_mem Finset.update_piecewise_of_mem

/- warning: finset.update_piecewise_of_not_mem -> Finset.update_piecewise_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {δ : α -> Sort.{u2}} (s : Finset.{u1} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) j s)] [_inst_2 : DecidableEq.{succ u1} α] {i : α}, (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s)) -> (forall (v : δ i), Eq.{imax (succ u1) u2} (forall (a : α), δ a) (Function.update.{succ u1, u2} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u1, u2} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) i v) (Finset.piecewise.{u1, u2} α (fun (a : α) => δ a) s f (Function.update.{succ u1, u2} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) g i v) (fun (j : α) => _inst_1 j)))
but is expected to have type
  forall {α : Type.{u2}} {δ : α -> Sort.{u1}} (s : Finset.{u2} α) (f : forall (i : α), δ i) (g : forall (i : α), δ i) [_inst_1 : forall (j : α), Decidable (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) j s)] [_inst_2 : DecidableEq.{succ u2} α] {i : α}, (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s)) -> (forall (v : δ i), Eq.{imax (succ u2) u1} (forall (a : α), δ a) (Function.update.{succ u2, u1} α (fun (a : α) => δ a) (fun (a : α) (b : α) => _inst_2 a b) (Finset.piecewise.{u2, u1} α (fun (i : α) => δ i) s f g (fun (j : α) => _inst_1 j)) i v) (Finset.piecewise.{u2, u1} α (fun (a : α) => δ a) s f (Function.update.{succ u2, u1} α (fun (i : α) => δ i) (fun (a : α) (b : α) => _inst_2 a b) g i v) (fun (j : α) => _inst_1 j)))
Case conversion may be inaccurate. Consider using '#align finset.update_piecewise_of_not_mem Finset.update_piecewise_of_not_memₓ'. -/
theorem update_piecewise_of_not_mem [DecidableEq α] {i : α} (hi : i ∉ s) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise f (update g i v) :=
  by
  rw [update_piecewise]
  refine' s.piecewise_congr (fun j hj => update_noteq _ _ _) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)
#align finset.update_piecewise_of_not_mem Finset.update_piecewise_of_not_mem

#print Finset.piecewise_le_of_le_of_le /-
theorem piecewise_le_of_le_of_le {δ : α → Type _} [∀ i, Preorder (δ i)] {f g h : ∀ i, δ i}
    (Hf : f ≤ h) (Hg : g ≤ h) : s.piecewise f g ≤ h := fun x =>
  piecewise_cases s f g (· ≤ h x) (Hf x) (Hg x)
#align finset.piecewise_le_of_le_of_le Finset.piecewise_le_of_le_of_le
-/

#print Finset.le_piecewise_of_le_of_le /-
theorem le_piecewise_of_le_of_le {δ : α → Type _} [∀ i, Preorder (δ i)] {f g h : ∀ i, δ i}
    (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ s.piecewise f g := fun x =>
  piecewise_cases s f g (fun y => h x ≤ y) (Hf x) (Hg x)
#align finset.le_piecewise_of_le_of_le Finset.le_piecewise_of_le_of_le
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
#print Finset.piecewise_le_piecewise' /-
theorem piecewise_le_piecewise' {δ : α → Type _} [∀ i, Preorder (δ i)] {f g f' g' : ∀ i, δ i}
    (Hf : ∀ x ∈ s, f x ≤ f' x) (Hg : ∀ (x) (_ : x ∉ s), g x ≤ g' x) :
    s.piecewise f g ≤ s.piecewise f' g' := fun x => by by_cases hx : x ∈ s <;> simp [hx, *]
#align finset.piecewise_le_piecewise' Finset.piecewise_le_piecewise'
-/

#print Finset.piecewise_le_piecewise /-
theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorder (δ i)] {f g f' g' : ∀ i, δ i}
    (Hf : f ≤ f') (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => Hf x) fun x _ => Hg x
#align finset.piecewise_le_piecewise Finset.piecewise_le_piecewise
-/

#print Finset.piecewise_mem_Icc_of_mem_of_mem /-
theorem piecewise_mem_Icc_of_mem_of_mem {δ : α → Type _} [∀ i, Preorder (δ i)]
    {f f₁ g g₁ : ∀ i, δ i} (hf : f ∈ Set.Icc f₁ g₁) (hg : g ∈ Set.Icc f₁ g₁) :
    s.piecewise f g ∈ Set.Icc f₁ g₁ :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩
#align finset.piecewise_mem_Icc_of_mem_of_mem Finset.piecewise_mem_Icc_of_mem_of_mem
-/

#print Finset.piecewise_mem_Icc /-
theorem piecewise_mem_Icc {δ : α → Type _} [∀ i, Preorder (δ i)] {f g : ∀ i, δ i} (h : f ≤ g) :
    s.piecewise f g ∈ Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)
#align finset.piecewise_mem_Icc Finset.piecewise_mem_Icc
-/

#print Finset.piecewise_mem_Icc' /-
theorem piecewise_mem_Icc' {δ : α → Type _} [∀ i, Preorder (δ i)] {f g : ∀ i, δ i} (h : g ≤ f) :
    s.piecewise f g ∈ Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)
#align finset.piecewise_mem_Icc' Finset.piecewise_mem_Icc'
-/

end Piecewise

section DecidablePiExists

variable {s : Finset α}

#print Finset.decidableDforallFinset /-
instance decidableDforallFinset {p : ∀ a ∈ s, Prop} [hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset
#align finset.decidable_dforall_finset Finset.decidableDforallFinset
-/

#print Finset.decidableEqPiFinset /-
/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidableEqPiFinset {β : α → Type _} [h : ∀ a, DecidableEq (β a)] :
    DecidableEq (∀ a ∈ s, β a) :=
  Multiset.decidableEqPiMultiset
#align finset.decidable_eq_pi_finset Finset.decidableEqPiFinset
-/

#print Finset.decidableDexistsFinset /-
instance decidableDexistsFinset {p : ∀ a ∈ s, Prop} [hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∃ (a : _)(h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset
#align finset.decidable_dexists_finset Finset.decidableDexistsFinset
-/

end DecidablePiExists

/-! ### filter -/


section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q]

#print Finset.filter /-
/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filterₓ p⟩
#align finset.filter Finset.filter
-/

#print Finset.filter_val /-
@[simp]
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filterₓ p :=
  rfl
#align finset.filter_val Finset.filter_val
-/

#print Finset.filter_subset /-
@[simp]
theorem filter_subset (s : Finset α) : s.filterₓ p ⊆ s :=
  filter_subset _ _
#align finset.filter_subset Finset.filter_subset
-/

variable {p}

#print Finset.mem_filter /-
@[simp]
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filterₓ p ↔ a ∈ s ∧ p a :=
  mem_filter
#align finset.mem_filter Finset.mem_filter
-/

#print Finset.mem_of_mem_filter /-
theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x ∈ s.filterₓ p) : x ∈ s :=
  mem_of_mem_filter h
#align finset.mem_of_mem_filter Finset.mem_of_mem_filter
-/

/- warning: finset.filter_ssubset -> Finset.filter_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) s) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => Not (p x))))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) s) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (Not (p x))))
Case conversion may be inaccurate. Consider using '#align finset.filter_ssubset Finset.filter_ssubsetₓ'. -/
theorem filter_ssubset {s : Finset α} : s.filterₓ p ⊂ s ↔ ∃ x ∈ s, ¬p x :=
  ⟨fun h =>
    let ⟨x, hs, hp⟩ := Set.exists_of_ssubset h
    ⟨x, hs, mt (fun hp => mem_filter.2 ⟨hs, hp⟩) hp⟩,
    fun ⟨x, hs, hp⟩ => ⟨s.filter_subset _, fun h => hp (mem_filter.1 (h hs)).2⟩⟩
#align finset.filter_ssubset Finset.filter_ssubset

variable (p)

#print Finset.filter_filter /-
theorem filter_filter (s : Finset α) : (s.filterₓ p).filterₓ q = s.filterₓ fun a => p a ∧ q a :=
  ext fun a => by simp only [mem_filter, and_comm', and_left_comm]
#align finset.filter_filter Finset.filter_filter
-/

/- warning: finset.filter_true -> Finset.filter_True is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} [h : DecidablePred.{succ u1} α (fun (_x : α) => True)], Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (_x : α) => True) h s) s
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α}, Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (x._@.Mathlib.Data.Finset.Basic._hyg.27729 : α) => True) (fun (a : α) => instDecidableTrue) s) s
Case conversion may be inaccurate. Consider using '#align finset.filter_true Finset.filter_Trueₓ'. -/
theorem filter_True {s : Finset α} [h : DecidablePred fun _ => True] :
    @Finset.filter α (fun _ => True) h s = s := by ext <;> simp
#align finset.filter_true Finset.filter_True

/- warning: finset.filter_false -> Finset.filter_False is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {h : DecidablePred.{succ u1} α (fun (a : α) => False)} (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => False) h s) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (h : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (x._@.Mathlib.Data.Finset.Basic._hyg.27767 : α) => False) (fun (a : α) => instDecidableFalse) h) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.filter_false Finset.filter_Falseₓ'. -/
@[simp]
theorem filter_False {h} (s : Finset α) : @filter α (fun a => False) h s = ∅ :=
  ext fun a => by simp only [mem_filter, and_false_iff] <;> rfl
#align finset.filter_false Finset.filter_False

variable {p q}

#print Finset.filter_eq_self /-
theorem filter_eq_self (s : Finset α) : s.filterₓ p = s ↔ ∀ x ∈ s, p x := by simp [Finset.ext_iff]
#align finset.filter_eq_self Finset.filter_eq_self
-/

#print Finset.filter_true_of_mem /-
/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp]
theorem filter_true_of_mem {s : Finset α} (h : ∀ x ∈ s, p x) : s.filterₓ p = s :=
  (filter_eq_self s).mpr h
#align finset.filter_true_of_mem Finset.filter_true_of_mem
-/

#print Finset.filter_false_of_mem /-
/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem {s : Finset α} (h : ∀ x ∈ s, ¬p x) : s.filterₓ p = ∅ :=
  eq_empty_of_forall_not_mem (by simpa)
#align finset.filter_false_of_mem Finset.filter_false_of_mem
-/

#print Finset.filter_eq_empty_iff /-
theorem filter_eq_empty_iff (s : Finset α) : s.filterₓ p = ∅ ↔ ∀ x ∈ s, ¬p x :=
  by
  refine' ⟨_, filter_false_of_mem⟩
  intro hs
  injection hs with hs'
  rwa [filter_eq_nil] at hs'
#align finset.filter_eq_empty_iff Finset.filter_eq_empty_iff
-/

/- warning: finset.filter_nonempty_iff -> Finset.filter_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Finset.{u1} α}, Iff (Finset.Nonempty.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => p a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p] {s : Finset.{u1} α}, Iff (Finset.Nonempty.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (p a)))
Case conversion may be inaccurate. Consider using '#align finset.filter_nonempty_iff Finset.filter_nonempty_iffₓ'. -/
theorem filter_nonempty_iff {s : Finset α} : (s.filterₓ p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp only [nonempty_iff_ne_empty, Ne.def, filter_eq_empty_iff, Classical.not_not, not_forall]
#align finset.filter_nonempty_iff Finset.filter_nonempty_iff

#print Finset.filter_congr /-
theorem filter_congr {s : Finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| filter_congr H
#align finset.filter_congr Finset.filter_congr
-/

variable (p q)

#print Finset.filter_empty /-
theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _
#align finset.filter_empty Finset.filter_empty
-/

#print Finset.filter_subset_filter /-
theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filterₓ p ⊆ t.filterₓ p := fun a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩
#align finset.filter_subset_filter Finset.filter_subset_filter
-/

#print Finset.monotone_filter_left /-
theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p
#align finset.monotone_filter_left Finset.monotone_filter_left
-/

#print Finset.monotone_filter_right /-
theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : p ≤ q) : s.filterₓ p ≤ s.filterₓ q :=
  Multiset.subset_of_le (Multiset.monotone_filter_right s.val h)
#align finset.monotone_filter_right Finset.monotone_filter_right
-/

#print Finset.coe_filter /-
@[simp, norm_cast]
theorem coe_filter (s : Finset α) : ↑(s.filterₓ p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter
#align finset.coe_filter Finset.coe_filter
-/

#print Finset.subset_coe_filter_of_subset_forall /-
theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s)
    (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filterₓ p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩
#align finset.subset_coe_filter_of_subset_forall Finset.subset_coe_filter_of_subset_forall
-/

#print Finset.filter_singleton /-
theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ := by
  classical
    ext x
    simp
    split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']
#align finset.filter_singleton Finset.filter_singleton
-/

#print Finset.filter_cons_of_pos /-
theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    filter p (cons a s ha) = cons a (filter p s) (mem_filter.Not.mpr <| mt And.left ha) :=
  eq_of_veq <| Multiset.filter_cons_of_pos s.val hp
#align finset.filter_cons_of_pos Finset.filter_cons_of_pos
-/

#print Finset.filter_cons_of_neg /-
theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) :
    filter p (cons a s ha) = filter p s :=
  eq_of_veq <| Multiset.filter_cons_of_neg s.val hp
#align finset.filter_cons_of_neg Finset.filter_cons_of_neg
-/

/- warning: finset.disjoint_filter -> Finset.disjoint_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {p : α -> Prop} {q : α -> Prop} [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α q], Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_4 a) s)) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (p x) -> (Not (q x)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {p : α -> Prop} {q : α -> Prop} [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α q], Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_4 a) s)) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (p x) -> (Not (q x)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_filter Finset.disjoint_filterₓ'. -/
theorem disjoint_filter {s : Finset α} {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint (s.filterₓ p) (s.filterₓ q) ↔ ∀ x ∈ s, p x → ¬q x := by
  constructor <;> simp (config := { contextual := true }) [disjoint_left]
#align finset.disjoint_filter Finset.disjoint_filter

/- warning: finset.disjoint_filter_filter -> Finset.disjoint_filter_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop} {q : α -> Prop} [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α q], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_4 a) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {t : Finset.{u1} α} {p : α -> Prop} {q : α -> Prop} [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α q], (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_4 a) t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_filter_filter Finset.disjoint_filter_filterₓ'. -/
theorem disjoint_filter_filter {s t : Finset α} {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] : Disjoint s t → Disjoint (s.filterₓ p) (t.filterₓ q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)
#align finset.disjoint_filter_filter Finset.disjoint_filter_filter

/- warning: finset.disjoint_filter_filter' -> Finset.disjoint_filter_filter' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) {p : α -> Prop} {q : α -> Prop} [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α q], (Disjoint.{u1} (α -> Prop) (Pi.partialOrder.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.partialOrder)) (Pi.orderBot.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Preorder.toLE.{0} ((fun (i : α) => (fun (i : α) => (fun (ᾰ : α) => Prop) i) i) i) ((fun (i : α) => PartialOrder.toPreorder.{0} ((fun (ᾰ : α) => Prop) i) ((fun (i : α) => Prop.partialOrder) i)) i)) (fun (i : α) => BoundedOrder.toOrderBot.{0} Prop (Preorder.toLE.{0} ((fun (i : α) => (fun (i : α) => (fun (ᾰ : α) => Prop) i) i) i) ((fun (i : α) => PartialOrder.toPreorder.{0} ((fun (ᾰ : α) => Prop) i) ((fun (i : α) => Prop.partialOrder) i)) i)) Prop.boundedOrder)) p q) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_4 a) t))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) {p : α -> Prop} {q : α -> Prop} [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α q], (Disjoint.{u1} (α -> Prop) (Pi.partialOrder.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.partialOrder)) (Pi.orderBot.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Preorder.toLE.{0} ((fun (i : α) => (fun (i : α) => Prop) i) i) ((fun (i : α) => PartialOrder.toPreorder.{0} ((fun (ᾰ : α) => Prop) i) ((fun (i : α) => Prop.partialOrder) i)) i)) (fun (i : α) => BoundedOrder.toOrderBot.{0} Prop Prop.le Prop.boundedOrder)) p q) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_4 a) t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_filter_filter' Finset.disjoint_filter_filter'ₓ'. -/
theorem disjoint_filter_filter' (s t : Finset α) {p q : α → Prop} [DecidablePred p]
    [DecidablePred q] (h : Disjoint p q) : Disjoint (s.filterₓ p) (t.filterₓ q) :=
  by
  simp_rw [disjoint_left, mem_filter]
  rintro a ⟨hs, hp⟩ ⟨ht, hq⟩
  exact h.le_bot _ ⟨hp, hq⟩
#align finset.disjoint_filter_filter' Finset.disjoint_filter_filter'

/- warning: finset.disjoint_filter_filter_neg -> Finset.disjoint_filter_filter_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) (p : α -> Prop) [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : DecidablePred.{succ u1} α (fun (a : α) => Not (p a))], Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => _inst_4 a) t)
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (t : Finset.{u1} α) (p : α -> Prop) [_inst_3 : DecidablePred.{succ u1} α p] [_inst_4 : forall (x : α), Decidable (Not (p x))], Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_3 a) s) (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => _inst_4 a) t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_filter_filter_neg Finset.disjoint_filter_filter_negₓ'. -/
theorem disjoint_filter_filter_neg (s t : Finset α) (p : α → Prop) [DecidablePred p]
    [DecidablePred fun a => ¬p a] : Disjoint (s.filterₓ p) (t.filterₓ fun a => ¬p a) :=
  disjoint_filter_filter' s t disjoint_compl_right
#align finset.disjoint_filter_filter_neg Finset.disjoint_filter_filter_neg

/- warning: finset.filter_disj_union -> Finset.filter_disj_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) (Finset.disjUnion.{u1} α s t h)) (Finset.disjUnion.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) t) (Finset.disjoint_filter_filter.{u1} α s t p p (fun (a : α) => _inst_1 a) (fun (a : α) => _inst_1 a) h))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] (s : Finset.{u1} α) (t : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) (Finset.disjUnion.{u1} α s t h)) (Finset.disjUnion.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) t) (Finset.disjoint_filter_filter.{u1} α s t p p (fun (a : α) => _inst_1 a) (fun (a : α) => _inst_1 a) h))
Case conversion may be inaccurate. Consider using '#align finset.filter_disj_union Finset.filter_disj_unionₓ'. -/
theorem filter_disj_union (s : Finset α) (t : Finset α) (h : Disjoint s t) :
    filter p (disjUnion s t h) = (filter p s).disjUnion (filter p t) (disjoint_filter_filter h) :=
  eq_of_veq <| Multiset.filter_add _ _ _
#align finset.filter_disj_union Finset.filter_disj_union

#print Finset.filter_cons /-
theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    filter p (cons a s ha) =
      (if p a then {a} else ∅ : Finset α).disjUnion (filter p s)
        (by
          split_ifs
          · rw [disjoint_singleton_left]
            exact mem_filter.not.mpr <| mt And.left ha
          · exact disjoint_empty_left _) :=
  by
  split_ifs with h
  · rw [filter_cons_of_pos _ _ _ ha h, singleton_disj_union]
  · rw [filter_cons_of_neg _ _ _ ha h, empty_disj_union]
#align finset.filter_cons Finset.filter_cons
-/

variable [DecidableEq α]

#print Finset.filter_union /-
theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filterₓ p = s₁.filterₓ p ∪ s₂.filterₓ p :=
  ext fun _ => by simp only [mem_filter, mem_union, or_and_right]
#align finset.filter_union Finset.filter_union
-/

#print Finset.filter_union_right /-
theorem filter_union_right (s : Finset α) :
    s.filterₓ p ∪ s.filterₓ q = s.filterₓ fun x => p x ∨ q x :=
  ext fun x => by simp only [mem_filter, mem_union, and_or_distrib_left.symm]
#align finset.filter_union_right Finset.filter_union_right
-/

#print Finset.filter_mem_eq_inter /-
theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] :
    (s.filterₓ fun i => i ∈ t) = s ∩ t :=
  ext fun i => by rw [mem_filter, mem_inter]
#align finset.filter_mem_eq_inter Finset.filter_mem_eq_inter
-/

#print Finset.filter_inter_distrib /-
theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filterₓ p = s.filterₓ p ∩ t.filterₓ p :=
  by
  ext
  simp only [mem_filter, mem_inter]
  exact and_and_right _ _ _
#align finset.filter_inter_distrib Finset.filter_inter_distrib
-/

#print Finset.filter_inter /-
theorem filter_inter (s t : Finset α) : filter p s ∩ t = filter p (s ∩ t) :=
  by
  ext
  simp only [mem_inter, mem_filter, and_right_comm]
#align finset.filter_inter Finset.filter_inter
-/

#print Finset.inter_filter /-
theorem inter_filter (s t : Finset α) : s ∩ filter p t = filter p (s ∩ t) := by
  rw [inter_comm, filter_inter, inter_comm]
#align finset.inter_filter Finset.inter_filter
-/

#print Finset.filter_insert /-
theorem filter_insert (a : α) (s : Finset α) :
    filter p (insert a s) = if p a then insert a (filter p s) else filter p s :=
  by
  ext x
  simp
  split_ifs with h <;> by_cases h' : x = a <;> simp [h, h']
#align finset.filter_insert Finset.filter_insert
-/

#print Finset.filter_erase /-
theorem filter_erase (a : α) (s : Finset α) : filter p (erase s a) = erase (filter p s) a :=
  by
  ext x
  simp only [and_assoc', mem_filter, iff_self_iff, mem_erase]
#align finset.filter_erase Finset.filter_erase
-/

/- warning: finset.filter_or -> Finset.filter_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidablePred.{succ u1} α (fun (a : α) => Or (p a) (q a))] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Or (p a) (q a)) (fun (a : α) => _inst_4 a) s) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_2 a) s))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q] [_inst_3 : DecidableEq.{succ u1} α] (_inst_4 : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Or (p a) (q a)) (fun (a : α) => instDecidableOr (p a) (q a) (_inst_1 a) (_inst_2 a)) _inst_4) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) _inst_4) (Finset.filter.{u1} α q (fun (a : α) => _inst_2 a) _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.filter_or Finset.filter_orₓ'. -/
theorem filter_or [DecidablePred fun a => p a ∨ q a] (s : Finset α) :
    (s.filterₓ fun a => p a ∨ q a) = s.filterₓ p ∪ s.filterₓ q :=
  ext fun _ => by simp only [mem_filter, mem_union, and_or_left]
#align finset.filter_or Finset.filter_or

/- warning: finset.filter_and -> Finset.filter_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidablePred.{succ u1} α (fun (a : α) => And (p a) (q a))] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => And (p a) (q a)) (fun (a : α) => _inst_4 a) s) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u1} α q (fun (a : α) => _inst_2 a) s))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) (q : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u1} α q] [_inst_3 : DecidableEq.{succ u1} α] (_inst_4 : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => And (p a) (q a)) (fun (a : α) => instDecidableAnd (p a) (q a) (_inst_1 a) (_inst_2 a)) _inst_4) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) _inst_4) (Finset.filter.{u1} α q (fun (a : α) => _inst_2 a) _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.filter_and Finset.filter_andₓ'. -/
theorem filter_and [DecidablePred fun a => p a ∧ q a] (s : Finset α) :
    (s.filterₓ fun a => p a ∧ q a) = s.filterₓ p ∩ s.filterₓ q :=
  ext fun _ => by simp only [mem_filter, mem_inter, and_comm', and_left_comm, and_self_iff]
#align finset.filter_and Finset.filter_and

/- warning: finset.filter_not -> Finset.filter_not is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidablePred.{succ u1} α (fun (a : α) => Not (p a))] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => _inst_4 a) s) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_3 : DecidableEq.{succ u1} α] (_inst_4 : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => instDecidableNot (p a) (_inst_1 a)) _inst_4) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) _inst_4 (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) _inst_4))
Case conversion may be inaccurate. Consider using '#align finset.filter_not Finset.filter_notₓ'. -/
theorem filter_not [DecidablePred fun a => ¬p a] (s : Finset α) :
    (s.filterₓ fun a => ¬p a) = s \ s.filterₓ p :=
  ext <| by
    simpa only [mem_filter, mem_sdiff, and_comm', not_and] using fun a =>
      and_congr_right fun h : a ∈ s => (imp_iff_right h).symm.trans imp_not_comm
#align finset.filter_not Finset.filter_not

#print Finset.sdiff_eq_filter /-
theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = filter (· ∉ s₂) s₁ :=
  ext fun _ => by simp only [mem_sdiff, mem_filter]
#align finset.sdiff_eq_filter Finset.sdiff_eq_filter
-/

#print Finset.sdiff_eq_self /-
theorem sdiff_eq_self (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ :=
  by
  simp [subset.antisymm_iff]
  constructor <;> intro h
  · trans s₁ \ s₂ ∩ s₂
    mono
    simp
  ·
    calc
      s₁ \ s₂ ⊇ s₁ \ (s₁ ∩ s₂) := by simp [(· ⊇ ·)]
      _ ⊇ s₁ \ ∅ := by mono using (· ⊇ ·)
      _ ⊇ s₁ := by simp [(· ⊇ ·)]
      
#align finset.sdiff_eq_self Finset.sdiff_eq_self
-/

/- warning: finset.subset_union_elim -> Finset.subset_union_elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t₁ t₂)) -> (Exists.{succ u1} (Finset.{u1} α) (fun (s₁ : Finset.{u1} α) => Exists.{succ u1} (Finset.{u1} α) (fun (s₂ : Finset.{u1} α) => And (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂) s) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₁) t₁) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s₂) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t₂ t₁))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α s) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t₁ t₂)) -> (Exists.{succ u1} (Finset.{u1} α) (fun (s₁ : Finset.{u1} α) => Exists.{succ u1} (Finset.{u1} α) (fun (s₂ : Finset.{u1} α) => And (Eq.{succ u1} (Finset.{u1} α) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) s₁ s₂) s) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α s₁) t₁) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.toSet.{u1} α s₂) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t₂ t₁))))))
Case conversion may be inaccurate. Consider using '#align finset.subset_union_elim Finset.subset_union_elimₓ'. -/
theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
    refine' ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), _, _, _⟩
    · simp [filter_union_right, em]
    · intro x
      simp
    · intro x
      simp
      intro hx hx₂
      refine' ⟨Or.resolve_left (h hx) hx₂, hx₂⟩
#align finset.subset_union_elim Finset.subset_union_elim

/- warning: finset.filter_congr_decidable clashes with [anonymous] -> [anonymous]
warning: finset.filter_congr_decidable -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (s : Finset.{u_1} α) (p : α -> Prop) (h : DecidablePred.{succ u_1} α p) [_inst_4 : DecidablePred.{succ u_1} α p], Eq.{succ u_1} (Finset.{u_1} α) (Finset.filter.{u_1} α p h s) (Finset.filter.{u_1} α p (fun (a : α) => _inst_4 a) s)
but is expected to have type
  forall {α : Type.{u}} {s : Type.{v}}, (Nat -> α -> s) -> Nat -> (List.{u} α) -> (List.{v} s)
Case conversion may be inaccurate. Consider using '#align finset.filter_congr_decidable [anonymous]ₓ'. -/
-- We can simplify an application of filter where the decidability is inferred in "the wrong way"
@[simp]
theorem [anonymous] {α} (s : Finset α) (p : α → Prop) (h : DecidablePred p) [DecidablePred p] :
    @filter α p h s = s.filterₓ p := by congr
#align finset.filter_congr_decidable [anonymous]

section Classical

open Classical

/-- The following instance allows us to write `{x ∈ s | p x}` for `finset.filter p s`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{x ∈ s | p x}` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{x ∈ s | p x}` to `finset.filter p s`. If `p` happens to be decidable, the
  simp-lemma `finset.filter_congr_decidable` will make sure that `finset.filter` uses the right
  instance for decidability.
-/
noncomputable instance {α : Type _} : Sep α (Finset α) :=
  ⟨fun p x => x.filterₓ p⟩

@[simp]
theorem sep_def {α : Type _} (s : Finset α) (p : α → Prop) : { x ∈ s | p x } = s.filterₓ p :=
  rfl
#align finset.sep_def Finset.sep_def

end Classical

#print Finset.filter_eq /-
-- This is not a good simp lemma, as it would prevent `finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter(eq b)`.
/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) : s.filterₓ (Eq b) = ite (b ∈ s) {b} ∅ :=
  by
  split_ifs
  · ext
    simp only [mem_filter, mem_singleton]
    exact
      ⟨fun h => h.2.symm, by
        rintro ⟨h⟩
        exact ⟨h, rfl⟩⟩
  · ext
    simp only [mem_filter, not_and, iff_false_iff, not_mem_empty]
    rintro m ⟨e⟩
    exact h m
#align finset.filter_eq Finset.filter_eq
-/

#print Finset.filter_eq' /-
/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filterₓ fun a => a = b) = ite (b ∈ s) {b} ∅ :=
  trans (filter_congr fun _ _ => ⟨Eq.symm, Eq.symm⟩) (filter_eq s b)
#align finset.filter_eq' Finset.filter_eq'
-/

#print Finset.filter_ne /-
theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) :
    (s.filterₓ fun a => b ≠ a) = s.eraseₓ b := by
  ext
  simp only [mem_filter, mem_erase, Ne.def]
  tauto
#align finset.filter_ne Finset.filter_ne
-/

#print Finset.filter_ne' /-
theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) :
    (s.filterₓ fun a => a ≠ b) = s.eraseₓ b :=
  trans (filter_congr fun _ _ => ⟨Ne.symm, Ne.symm⟩) (filter_ne s b)
#align finset.filter_ne' Finset.filter_ne'
-/

/- warning: finset.filter_inter_filter_neg_eq -> Finset.filter_inter_filter_neg_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : DecidablePred.{succ u1} α (fun (a : α) => Not (p a))] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => _inst_4 a) t)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_3 : DecidableEq.{succ u1} α] (_inst_4 : Finset.{u1} α) (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_3 a b)) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) _inst_4) (Finset.filter.{u1} α (fun (a : α) => Not (p a)) (fun (a : α) => instDecidableNot (p a) (_inst_1 a)) s)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.instEmptyCollectionFinset.{u1} α))
Case conversion may be inaccurate. Consider using '#align finset.filter_inter_filter_neg_eq Finset.filter_inter_filter_neg_eqₓ'. -/
theorem filter_inter_filter_neg_eq [DecidablePred fun a => ¬p a] (s t : Finset α) :
    (s.filterₓ p ∩ t.filterₓ fun a => ¬p a) = ∅ :=
  (disjoint_filter_filter_neg s t p).eq_bot
#align finset.filter_inter_filter_neg_eq Finset.filter_inter_filter_neg_eq

#print Finset.filter_union_filter_of_codisjoint /-
theorem filter_union_filter_of_codisjoint (s : Finset α) (h : Codisjoint p q) :
    s.filterₓ p ∪ s.filterₓ q = s :=
  (filter_or _ _ _).symm.trans <| filter_true_of_mem fun x hx => h.top_le x trivial
#align finset.filter_union_filter_of_codisjoint Finset.filter_union_filter_of_codisjoint
-/

#print Finset.filter_union_filter_neg_eq /-
theorem filter_union_filter_neg_eq [DecidablePred fun a => ¬p a] (s : Finset α) :
    (s.filterₓ p ∪ s.filterₓ fun a => ¬p a) = s :=
  filter_union_filter_of_codisjoint _ _ _ codisjoint_hnot_right
#align finset.filter_union_filter_neg_eq Finset.filter_union_filter_neg_eq
-/

end Filter

/-! ### range -/


section Range

variable {n m l : ℕ}

#print Finset.range /-
/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩
#align finset.range Finset.range
-/

#print Finset.range_val /-
@[simp]
theorem range_val (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl
#align finset.range_val Finset.range_val
-/

#print Finset.mem_range /-
@[simp]
theorem mem_range : m ∈ range n ↔ m < n :=
  mem_range
#align finset.mem_range Finset.mem_range
-/

#print Finset.coe_range /-
@[simp, norm_cast]
theorem coe_range (n : ℕ) : (range n : Set ℕ) = Set.Iio n :=
  Set.ext fun _ => mem_range
#align finset.coe_range Finset.coe_range
-/

#print Finset.range_zero /-
@[simp]
theorem range_zero : range 0 = ∅ :=
  rfl
#align finset.range_zero Finset.range_zero
-/

#print Finset.range_one /-
@[simp]
theorem range_one : range 1 = {0} :=
  rfl
#align finset.range_one Finset.range_one
-/

/- warning: finset.range_succ -> Finset.range_succ is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.range (Nat.succ n)) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.hasInsert.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) n (Finset.range n))
but is expected to have type
  forall {n : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.range (Nat.succ n)) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.instInsertFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) n (Finset.range n))
Case conversion may be inaccurate. Consider using '#align finset.range_succ Finset.range_succₓ'. -/
theorem range_succ : range (succ n) = insert n (range n) :=
  eq_of_veq <| (range_succ n).trans <| (ndinsert_of_not_mem not_mem_range_self).symm
#align finset.range_succ Finset.range_succ

/- warning: finset.range_add_one -> Finset.range_add_one is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.hasInsert.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) n (Finset.range n))
but is expected to have type
  forall {n : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.instInsertFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) n (Finset.range n))
Case conversion may be inaccurate. Consider using '#align finset.range_add_one Finset.range_add_oneₓ'. -/
theorem range_add_one : range (n + 1) = insert n (range n) :=
  range_succ
#align finset.range_add_one Finset.range_add_one

#print Finset.not_mem_range_self /-
@[simp]
theorem not_mem_range_self : n ∉ range n :=
  not_mem_range_self
#align finset.not_mem_range_self Finset.not_mem_range_self
-/

#print Finset.self_mem_range_succ /-
@[simp]
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  Multiset.self_mem_range_succ n
#align finset.self_mem_range_succ Finset.self_mem_range_succ
-/

#print Finset.range_subset /-
@[simp]
theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
  range_subset
#align finset.range_subset Finset.range_subset
-/

#print Finset.range_mono /-
theorem range_mono : Monotone range := fun _ _ => range_subset.2
#align finset.range_mono Finset.range_mono
-/

#print Finset.mem_range_succ_iff /-
theorem mem_range_succ_iff {a b : ℕ} : a ∈ Finset.range b.succ ↔ a ≤ b :=
  Finset.mem_range.trans Nat.lt_succ_iff
#align finset.mem_range_succ_iff Finset.mem_range_succ_iff
-/

#print Finset.mem_range_le /-
theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
  (mem_range.1 hx).le
#align finset.mem_range_le Finset.mem_range_le
-/

#print Finset.mem_range_sub_ne_zero /-
theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
  ne_of_gt <| tsub_pos_of_lt <| mem_range.1 hx
#align finset.mem_range_sub_ne_zero Finset.mem_range_sub_ne_zero
-/

#print Finset.nonempty_range_iff /-
@[simp]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => ((zero_le k).trans_lt <| mem_range.1 hk).ne', fun h =>
    ⟨0, mem_range.2 <| pos_iff_ne_zero.2 h⟩⟩
#align finset.nonempty_range_iff Finset.nonempty_range_iff
-/

#print Finset.range_eq_empty_iff /-
@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_range_iff, Classical.not_not]
#align finset.range_eq_empty_iff Finset.range_eq_empty_iff
-/

#print Finset.nonempty_range_succ /-
theorem nonempty_range_succ : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero
#align finset.nonempty_range_succ Finset.nonempty_range_succ
-/

/- warning: finset.range_filter_eq -> Finset.range_filter_eq is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {m : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.filter.{0} Nat (fun (_x : Nat) => Eq.{1} Nat _x m) (fun (a : Nat) => Nat.decidableEq a m) (Finset.range n)) (ite.{1} (Finset.{0} Nat) (LT.lt.{0} Nat Nat.hasLt m n) (Nat.decidableLt m n) (Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (Finset.hasSingleton.{0} Nat) m) (EmptyCollection.emptyCollection.{0} (Finset.{0} Nat) (Finset.hasEmptyc.{0} Nat)))
but is expected to have type
  forall {n : Nat} {m : Nat}, Eq.{1} (Finset.{0} Nat) (Finset.filter.{0} Nat (fun (_x : Nat) => Eq.{1} Nat _x m) (fun (a : Nat) => instDecidableEqNat a m) (Finset.range n)) (ite.{1} (Finset.{0} Nat) (LT.lt.{0} Nat instLTNat m n) (Nat.decLt m n) (Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (Finset.instSingletonFinset.{0} Nat) m) (EmptyCollection.emptyCollection.{0} (Finset.{0} Nat) (Finset.instEmptyCollectionFinset.{0} Nat)))
Case conversion may be inaccurate. Consider using '#align finset.range_filter_eq Finset.range_filter_eqₓ'. -/
@[simp]
theorem range_filter_eq {n m : ℕ} : (range n).filterₓ (· = m) = if m < n then {m} else ∅ :=
  by
  convert filter_eq (range n) m
  · ext
    exact comm
  · simp
#align finset.range_filter_eq Finset.range_filter_eq

end Range

#print Finset.exists_mem_empty_iff /-
-- useful rules for calculations with quantifiers
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False := by
  simp only [not_mem_empty, false_and_iff, exists_false]
#align finset.exists_mem_empty_iff Finset.exists_mem_empty_iff
-/

#print Finset.exists_mem_insert /-
theorem exists_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x := by
  simp only [mem_insert, or_and_right, exists_or, exists_eq_left]
#align finset.exists_mem_insert Finset.exists_mem_insert
-/

#print Finset.forall_mem_empty_iff /-
theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True :=
  iff_true_intro fun _ => False.elim
#align finset.forall_mem_empty_iff Finset.forall_mem_empty_iff
-/

#print Finset.forall_mem_insert /-
theorem forall_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_insert, or_imp, forall_and, forall_eq]
#align finset.forall_mem_insert Finset.forall_mem_insert
-/

end Finset

#print notMemRangeEquiv /-
/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def notMemRangeEquiv (k : ℕ) : { n // n ∉ range k } ≃ ℕ
    where
  toFun i := i.1 - k
  invFun j := ⟨j + k, by simp⟩
  left_inv j := by
    rw [Subtype.ext_iff_val]
    apply tsub_add_cancel_of_le
    simpa using j.2
  right_inv j := add_tsub_cancel_right _ _
#align not_mem_range_equiv notMemRangeEquiv
-/

#print coe_notMemRangeEquiv /-
@[simp]
theorem coe_notMemRangeEquiv (k : ℕ) :
    (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun i => i - k :=
  rfl
#align coe_not_mem_range_equiv coe_notMemRangeEquiv
-/

#print coe_notMemRangeEquiv_symm /-
@[simp]
theorem coe_notMemRangeEquiv_symm (k : ℕ) :
    ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) = fun j => ⟨j + k, by simp⟩ :=
  rfl
#align coe_not_mem_range_equiv_symm coe_notMemRangeEquiv_symm
-/

/-! ### dedup on list and multiset -/


namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

#print Multiset.toFinset /-
/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def toFinset (s : Multiset α) : Finset α :=
  ⟨_, nodup_dedup s⟩
#align multiset.to_finset Multiset.toFinset
-/

#print Multiset.toFinset_val /-
@[simp]
theorem toFinset_val (s : Multiset α) : s.toFinset.1 = s.dedup :=
  rfl
#align multiset.to_finset_val Multiset.toFinset_val
-/

#print Multiset.toFinset_eq /-
theorem toFinset_eq {s : Multiset α} (n : Nodup s) : Finset.mk s n = s.toFinset :=
  Finset.val_inj.1 n.dedup.symm
#align multiset.to_finset_eq Multiset.toFinset_eq
-/

#print Multiset.Nodup.toFinset_inj /-
theorem Nodup.toFinset_inj {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l = l' := by
  simpa [← to_finset_eq hl, ← to_finset_eq hl'] using h
#align multiset.nodup.to_finset_inj Multiset.Nodup.toFinset_inj
-/

#print Multiset.mem_toFinset /-
@[simp]
theorem mem_toFinset {a : α} {s : Multiset α} : a ∈ s.toFinset ↔ a ∈ s :=
  mem_dedup
#align multiset.mem_to_finset Multiset.mem_toFinset
-/

#print Multiset.toFinset_zero /-
@[simp]
theorem toFinset_zero : toFinset (0 : Multiset α) = ∅ :=
  rfl
#align multiset.to_finset_zero Multiset.toFinset_zero
-/

#print Multiset.toFinset_cons /-
@[simp]
theorem toFinset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (toFinset s) :=
  Finset.eq_of_veq dedup_cons
#align multiset.to_finset_cons Multiset.toFinset_cons
-/

#print Multiset.toFinset_singleton /-
@[simp]
theorem toFinset_singleton (a : α) : toFinset ({a} : Multiset α) = {a} := by
  rw [← cons_zero, to_finset_cons, to_finset_zero, IsLawfulSingleton.insert_emptyCollection_eq]
#align multiset.to_finset_singleton Multiset.toFinset_singleton
-/

#print Multiset.toFinset_add /-
@[simp]
theorem toFinset_add (s t : Multiset α) : toFinset (s + t) = toFinset s ∪ toFinset t :=
  Finset.ext <| by simp
#align multiset.to_finset_add Multiset.toFinset_add
-/

/- warning: multiset.to_finset_nsmul -> Multiset.toFinset_nsmul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (n : Nat), (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{succ u1} (Finset.{u1} α) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (SMul.smul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.orderedCancelAddCommMonoid.{u1} α)))))) n s)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (n : Nat), (Ne.{1} Nat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{succ u1} (Finset.{u1} α) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (HSMul.hSMul.{0, u1, u1} Nat (Multiset.{u1} α) (Multiset.{u1} α) (instHSMul.{0, u1} Nat (Multiset.{u1} α) (AddMonoid.SMul.{u1} (Multiset.{u1} α) (AddRightCancelMonoid.toAddMonoid.{u1} (Multiset.{u1} α) (AddCancelMonoid.toAddRightCancelMonoid.{u1} (Multiset.{u1} α) (AddCancelCommMonoid.toAddCancelMonoid.{u1} (Multiset.{u1} α) (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{u1} (Multiset.{u1} α) (Multiset.instOrderedCancelAddCommMonoidMultiset.{u1} α))))))) n s)) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
Case conversion may be inaccurate. Consider using '#align multiset.to_finset_nsmul Multiset.toFinset_nsmulₓ'. -/
@[simp]
theorem toFinset_nsmul (s : Multiset α) : ∀ (n : ℕ) (hn : n ≠ 0), (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
  | n + 1, h => by
    by_cases n = 0
    · rw [h, zero_add, one_nsmul]
    · rw [add_nsmul, to_finset_add, one_nsmul, to_finset_nsmul n h, Finset.union_idempotent]
#align multiset.to_finset_nsmul Multiset.toFinset_nsmul

#print Multiset.toFinset_inter /-
@[simp]
theorem toFinset_inter (s t : Multiset α) : toFinset (s ∩ t) = toFinset s ∩ toFinset t :=
  Finset.ext <| by simp
#align multiset.to_finset_inter Multiset.toFinset_inter
-/

#print Multiset.toFinset_union /-
@[simp]
theorem toFinset_union (s t : Multiset α) : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext <;> simp
#align multiset.to_finset_union Multiset.toFinset_union
-/

#print Multiset.toFinset_eq_empty /-
@[simp]
theorem toFinset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero
#align multiset.to_finset_eq_empty Multiset.toFinset_eq_empty
-/

#print Multiset.toFinset_subset /-
@[simp]
theorem toFinset_subset : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp only [Finset.subset_iff, Multiset.subset_iff, Multiset.mem_toFinset]
#align multiset.to_finset_subset Multiset.toFinset_subset
-/

#print Multiset.toFinset_ssubset /-
@[simp]
theorem toFinset_ssubset : s.toFinset ⊂ t.toFinset ↔ s ⊂ t :=
  by
  simp_rw [Finset.ssubset_def, to_finset_subset]
  rfl
#align multiset.to_finset_ssubset Multiset.toFinset_ssubset
-/

#print Multiset.toFinset_dedup /-
@[simp]
theorem toFinset_dedup (m : Multiset α) : m.dedup.toFinset = m.toFinset := by
  simp_rw [to_finset, dedup_idempotent]
#align multiset.to_finset_dedup Multiset.toFinset_dedup
-/

#print Multiset.toFinset_bind_dedup /-
@[simp]
theorem toFinset_bind_dedup [DecidableEq β] (m : Multiset α) (f : α → Multiset β) :
    (m.dedup.bind f).toFinset = (m.bind f).toFinset := by simp_rw [to_finset, dedup_bind_dedup]
#align multiset.to_finset_bind_dedup Multiset.toFinset_bind_dedup
-/

#print Multiset.isWellFounded_ssubset /-
instance isWellFounded_ssubset : IsWellFounded (Multiset β) (· ⊂ ·) :=
  Subrelation.isWellFounded (InvImage _ _) fun _ _ => by classical exact to_finset_ssubset.2
#align multiset.is_well_founded_ssubset Multiset.isWellFounded_ssubset
-/

end Multiset

namespace Finset

#print Finset.val_toFinset /-
@[simp]
theorem val_toFinset [DecidableEq α] (s : Finset α) : s.val.toFinset = s :=
  by
  ext
  rw [Multiset.mem_toFinset, ← mem_def]
#align finset.val_to_finset Finset.val_toFinset
-/

/- warning: finset.val_le_iff_val_subset -> Finset.val_le_iff_val_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Finset.{u1} α} {b : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.partialOrder.{u1} α))) (Finset.val.{u1} α a) b) (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.hasSubset.{u1} α) (Finset.val.{u1} α a) b)
but is expected to have type
  forall {α : Type.{u1}} {a : Finset.{u1} α} {b : Multiset.{u1} α}, Iff (LE.le.{u1} (Multiset.{u1} α) (Preorder.toLE.{u1} (Multiset.{u1} α) (PartialOrder.toPreorder.{u1} (Multiset.{u1} α) (Multiset.instPartialOrderMultiset.{u1} α))) (Finset.val.{u1} α a) b) (HasSubset.Subset.{u1} (Multiset.{u1} α) (Multiset.instHasSubsetMultiset.{u1} α) (Finset.val.{u1} α a) b)
Case conversion may be inaccurate. Consider using '#align finset.val_le_iff_val_subset Finset.val_le_iff_val_subsetₓ'. -/
theorem val_le_iff_val_subset {a : Finset α} {b : Multiset α} : a.val ≤ b ↔ a.val ⊆ b :=
  Multiset.le_iff_subset a.Nodup
#align finset.val_le_iff_val_subset Finset.val_le_iff_val_subset

end Finset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α}

#print List.toFinset /-
/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def toFinset (l : List α) : Finset α :=
  Multiset.toFinset l
#align list.to_finset List.toFinset
-/

#print List.toFinset_val /-
@[simp]
theorem toFinset_val (l : List α) : l.toFinset.1 = (l.dedup : Multiset α) :=
  rfl
#align list.to_finset_val List.toFinset_val
-/

#print List.toFinset_coe /-
@[simp]
theorem toFinset_coe (l : List α) : (l : Multiset α).toFinset = l.toFinset :=
  rfl
#align list.to_finset_coe List.toFinset_coe
-/

#print List.toFinset_eq /-
theorem toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFinset :=
  Multiset.toFinset_eq n
#align list.to_finset_eq List.toFinset_eq
-/

#print List.mem_toFinset /-
@[simp]
theorem mem_toFinset : a ∈ l.toFinset ↔ a ∈ l :=
  mem_dedup
#align list.mem_to_finset List.mem_toFinset
-/

#print List.coe_toFinset /-
@[simp, norm_cast]
theorem coe_toFinset (l : List α) : (l.toFinset : Set α) = { a | a ∈ l } :=
  Set.ext fun _ => List.mem_toFinset
#align list.coe_to_finset List.coe_toFinset
-/

#print List.toFinset_nil /-
@[simp]
theorem toFinset_nil : toFinset (@nil α) = ∅ :=
  rfl
#align list.to_finset_nil List.toFinset_nil
-/

#print List.toFinset_cons /-
@[simp]
theorem toFinset_cons : toFinset (a :: l) = insert a (toFinset l) :=
  Finset.eq_of_veq <| by by_cases h : a ∈ l <;> simp [Finset.insert_val', Multiset.dedup_cons, h]
#align list.to_finset_cons List.toFinset_cons
-/

#print List.toFinset_surj_on /-
theorem toFinset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.univ :=
  by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (to_finset_eq hl).symm⟩
#align list.to_finset_surj_on List.toFinset_surj_on
-/

#print List.toFinset_surjective /-
theorem toFinset_surjective : Surjective (toFinset : List α → Finset α) := fun s =>
  let ⟨l, _, hls⟩ := toFinset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩
#align list.to_finset_surjective List.toFinset_surjective
-/

#print List.toFinset_eq_iff_perm_dedup /-
theorem toFinset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup := by
  simp [Finset.ext_iff, perm_ext (nodup_dedup _) (nodup_dedup _)]
#align list.to_finset_eq_iff_perm_dedup List.toFinset_eq_iff_perm_dedup
-/

#print List.toFinset.ext_iff /-
theorem toFinset.ext_iff {a b : List α} : a.toFinset = b.toFinset ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [Finset.ext_iff, mem_to_finset]
#align list.to_finset.ext_iff List.toFinset.ext_iff
-/

#print List.toFinset.ext /-
theorem toFinset.ext : (∀ x, x ∈ l ↔ x ∈ l') → l.toFinset = l'.toFinset :=
  toFinset.ext_iff.mpr
#align list.to_finset.ext List.toFinset.ext
-/

#print List.toFinset_eq_of_perm /-
theorem toFinset_eq_of_perm (l l' : List α) (h : l ~ l') : l.toFinset = l'.toFinset :=
  toFinset_eq_iff_perm_dedup.mpr h.dedup
#align list.to_finset_eq_of_perm List.toFinset_eq_of_perm
-/

#print List.perm_of_nodup_nodup_toFinset_eq /-
theorem perm_of_nodup_nodup_toFinset_eq (hl : Nodup l) (hl' : Nodup l')
    (h : l.toFinset = l'.toFinset) : l ~ l' :=
  by
  rw [← Multiset.coe_eq_coe]
  exact Multiset.Nodup.toFinset_inj hl hl' h
#align list.perm_of_nodup_nodup_to_finset_eq List.perm_of_nodup_nodup_toFinset_eq
-/

#print List.toFinset_append /-
@[simp]
theorem toFinset_append : toFinset (l ++ l') = l.toFinset ∪ l'.toFinset :=
  by
  induction' l with hd tl hl
  · simp
  · simp [hl]
#align list.to_finset_append List.toFinset_append
-/

#print List.toFinset_reverse /-
@[simp]
theorem toFinset_reverse {l : List α} : toFinset l.reverse = l.toFinset :=
  toFinset_eq_of_perm _ _ (reverse_perm l)
#align list.to_finset_reverse List.toFinset_reverse
-/

#print List.toFinset_replicate_of_ne_zero /-
theorem toFinset_replicate_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (List.replicate n a).toFinset = {a} :=
  by
  ext x
  simp [hn, List.mem_replicate]
#align list.to_finset_replicate_of_ne_zero List.toFinset_replicate_of_ne_zero
-/

#print List.toFinset_union /-
@[simp]
theorem toFinset_union (l l' : List α) : (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset :=
  by
  ext
  simp
#align list.to_finset_union List.toFinset_union
-/

#print List.toFinset_inter /-
@[simp]
theorem toFinset_inter (l l' : List α) : (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset :=
  by
  ext
  simp
#align list.to_finset_inter List.toFinset_inter
-/

#print List.toFinset_eq_empty_iff /-
@[simp]
theorem toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by cases l <;> simp
#align list.to_finset_eq_empty_iff List.toFinset_eq_empty_iff
-/

end List

namespace Finset

section ToList

#print Finset.toList /-
/-- Produce a list of the elements in the finite set using choice. -/
noncomputable def toList (s : Finset α) : List α :=
  s.1.toList
#align finset.to_list Finset.toList
-/

#print Finset.nodup_toList /-
theorem nodup_toList (s : Finset α) : s.toList.Nodup :=
  by
  rw [to_list, ← Multiset.coe_nodup, Multiset.coe_toList]
  exact s.nodup
#align finset.nodup_to_list Finset.nodup_toList
-/

#print Finset.mem_toList /-
@[simp]
theorem mem_toList {a : α} {s : Finset α} : a ∈ s.toList ↔ a ∈ s :=
  mem_toList
#align finset.mem_to_list Finset.mem_toList
-/

#print Finset.toList_eq_nil /-
@[simp]
theorem toList_eq_nil {s : Finset α} : s.toList = [] ↔ s = ∅ :=
  toList_eq_nil.trans val_eq_zero
#align finset.to_list_eq_nil Finset.toList_eq_nil
-/

#print Finset.empty_toList /-
@[simp]
theorem empty_toList {s : Finset α} : s.toList.Empty ↔ s = ∅ :=
  List.isEmpty_iff_eq_nil.trans toList_eq_nil
#align finset.empty_to_list Finset.empty_toList
-/

#print Finset.toList_empty /-
@[simp]
theorem toList_empty : (∅ : Finset α).toList = [] :=
  toList_eq_nil.mpr rfl
#align finset.to_list_empty Finset.toList_empty
-/

#print Finset.Nonempty.toList_ne_nil /-
theorem Nonempty.toList_ne_nil {s : Finset α} (hs : s.Nonempty) : s.toList ≠ [] :=
  mt toList_eq_nil.mp hs.ne_empty
#align finset.nonempty.to_list_ne_nil Finset.Nonempty.toList_ne_nil
-/

#print Finset.Nonempty.not_empty_toList /-
theorem Nonempty.not_empty_toList {s : Finset α} (hs : s.Nonempty) : ¬s.toList.Empty :=
  mt empty_toList.mp hs.ne_empty
#align finset.nonempty.not_empty_to_list Finset.Nonempty.not_empty_toList
-/

#print Finset.coe_toList /-
@[simp, norm_cast]
theorem coe_toList (s : Finset α) : (s.toList : Multiset α) = s.val :=
  s.val.coe_toList
#align finset.coe_to_list Finset.coe_toList
-/

#print Finset.toList_toFinset /-
@[simp]
theorem toList_toFinset [DecidableEq α] (s : Finset α) : s.toList.toFinset = s :=
  by
  ext
  simp
#align finset.to_list_to_finset Finset.toList_toFinset
-/

#print Finset.toList_eq_singleton_iff /-
@[simp]
theorem toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a} := by
  rw [to_list, to_list_eq_singleton_iff, val_eq_singleton_iff]
#align finset.to_list_eq_singleton_iff Finset.toList_eq_singleton_iff
-/

#print Finset.toList_singleton /-
@[simp]
theorem toList_singleton : ∀ a, ({a} : Finset α).toList = [a] :=
  toList_singleton
#align finset.to_list_singleton Finset.toList_singleton
-/

#print Finset.exists_list_nodup_eq /-
theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s :=
  ⟨s.toList, s.nodup_toList, s.toList_toFinset⟩
#align finset.exists_list_nodup_eq Finset.exists_list_nodup_eq
-/

#print Finset.toList_cons /-
theorem toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext (nodup_toList _) (by simp [h, nodup_to_list s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]
#align finset.to_list_cons Finset.toList_cons
-/

#print Finset.toList_insert /-
theorem toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ toList_cons _
#align finset.to_list_insert Finset.toList_insert
-/

end ToList

/-!
### disj_Union

This section is about the bounded union of a disjoint indexed family `t : α → finset β` of finite
sets over a finite set `s : finset α`. In most cases `finset.bUnion` should be preferred.
-/


section DisjUnion

variable {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

/-- `disj_Union s f h` is the set such that `a ∈ disj_Union s f` iff `a ∈ f i` for some `i ∈ s`.
It is the same as `s.bUnion f`, but it does not require decidable equality on the type. The
hypothesis ensures that the sets are disjoint. -/
def disjUnion (s : Finset α) (t : α → Finset β) (hf : (s : Set α).PairwiseDisjoint t) : Finset β :=
  ⟨s.val.bind (Finset.val ∘ t),
    Multiset.nodup_bind.mpr
      ⟨fun a ha => (t a).Nodup,
        s.Nodup.Pairwise fun a ha b hb hab => disjoint_val.2 <| hf ha hb hab⟩⟩
#align finset.disj_Union Finset.disjUnionₓ

/- warning: finset.disj_Union_val -> Finset.disjUnionᵢ_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : α -> (Finset.{u2} β)) (h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) t), Eq.{succ u2} (Multiset.{u2} β) (Finset.val.{u2} β (Finset.disjUnionₓ.{u1, u2} α β s t h)) (Multiset.bind.{u1, u2} α β (Finset.val.{u1} α s) (fun (a : α) => Finset.val.{u2} β (t a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : α -> (Finset.{u1} β)) (h : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} β) α (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.toSet.{u2} α s) t), Eq.{succ u1} (Multiset.{u1} β) (Finset.val.{u1} β (Finset.disjUnionᵢ.{u2, u1} α β s t h)) (Multiset.bind.{u2, u1} α β (Finset.val.{u2} α s) (fun (a : α) => Finset.val.{u1} β (t a)))
Case conversion may be inaccurate. Consider using '#align finset.disj_Union_val Finset.disjUnionᵢ_valₓ'. -/
@[simp]
theorem disjUnionᵢ_val (s : Finset α) (t : α → Finset β) (h) :
    (s.disjUnionₓ t h).1 = s.1.bind fun a => (t a).1 :=
  rfl
#align finset.disj_Union_val Finset.disjUnionᵢ_val

#print Finset.disjUnionᵢ_empty /-
@[simp]
theorem disjUnionᵢ_empty (t : α → Finset β) : disjUnion ∅ t (by simp) = ∅ :=
  rfl
#align finset.disj_Union_empty Finset.disjUnionᵢ_empty
-/

/- warning: finset.mem_disj_Union -> Finset.mem_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {b : β} {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) t}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s t h)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (t a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {b : β} {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (Finset.toSet.{u1} α s) t}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u1, u2} α β s t h)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (t a))))
Case conversion may be inaccurate. Consider using '#align finset.mem_disj_Union Finset.mem_disjUnionᵢₓ'. -/
@[simp]
theorem mem_disjUnionᵢ {b : β} {h} : b ∈ s.disjUnionₓ t h ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, disj_Union_val, mem_bind, exists_prop]
#align finset.mem_disj_Union Finset.mem_disjUnionᵢ

/- warning: finset.coe_disj_Union -> Finset.coe_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) t}, Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.disjUnionₓ.{u1, u2} α β s t h)) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (t x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (Finset.toSet.{u1} α s) t}, Eq.{succ u2} (Set.{u2} β) (Finset.toSet.{u2} β (Finset.disjUnionᵢ.{u1, u2} α β s t h)) (Set.unionᵢ.{u2, succ u1} β α (fun (x : α) => Set.unionᵢ.{u2, 0} β (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Finset.toSet.{u1} α s)) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Finset.toSet.{u1} α s)) => Finset.toSet.{u2} β (t x))))
Case conversion may be inaccurate. Consider using '#align finset.coe_disj_Union Finset.coe_disjUnionᵢₓ'. -/
@[simp, norm_cast]
theorem coe_disjUnionᵢ {h} : (s.disjUnionₓ t h : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp only [Set.ext_iff, mem_disj_Union, Set.mem_unionᵢ, iff_self_iff, mem_coe, imp_true_iff]
#align finset.coe_disj_Union Finset.coe_disjUnionᵢ

/- warning: finset.disj_Union_cons -> Finset.disjUnionᵢ_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (a : α) (s : Finset.{u1} α) (ha : Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (f : α -> (Finset.{u2} β)) (H : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Finset.cons.{u1} α a s ha)) f), Eq.{succ u2} (Finset.{u2} β) (Finset.disjUnionₓ.{u1, u2} α β (Finset.cons.{u1} α a s ha) f H) (Finset.disjUnion.{u2} β (f a) (Finset.disjUnionₓ.{u1, u2} α β s f (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc))) (Iff.mpr (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (f a) (Finset.disjUnionₓ.{u1, u2} α β s f (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc)))) (forall {{a_1 : β}}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f a)) -> (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (Finset.disjUnionₓ.{u1, u2} α β s f (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc)))))) (Finset.disjoint_left.{u2} β (f a) (Finset.disjUnionₓ.{u1, u2} α β s f (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc)))) (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)) (h : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc)))) => (fun (_a : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) => Exists.dcases_on.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) (fun (_a : Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) => False) _a (fun (w : α) (h_1 : Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f w))) => Exists.dcases_on.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f w)) (fun (h_1 : Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f w))) => False) h_1 (fun (h_1_w : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) w s) (h_1_h : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f w)) => id.{0} False (Iff.mp (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (f a) (f w)) (forall {{a_1 : β}}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f a)) -> (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f w)))) (Finset.disjoint_left.{u2} β (f a) (f w)) (H a (Finset.mem_cons_self.{u1} α a s ha) w (Multiset.mem_cons_of_mem.{u1} α w a (Finset.val.{u1} α s) h_1_w) (Ne.symm.{succ u1} α w a (ne_of_mem_of_not_mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) s w a h_1_w ha))) b hb h_1_h)))) (Iff.mp (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc)))) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b (fun (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (c : α) (hc : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) c ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) => H b (Multiset.mem_cons_of_mem.{u1} α b a (Finset.val.{u1} α s) hb) c (Multiset.mem_cons_of_mem.{u1} α c a (Finset.val.{u1} α s) hc))) h))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (a : α) (s : Finset.{u2} α) (ha : Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) (f : α -> (Finset.{u1} β)) (H : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} β) α (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.toSet.{u2} α (Finset.cons.{u2} α a s ha)) f), Eq.{succ u1} (Finset.{u1} β) (Finset.disjUnionᵢ.{u2, u1} α β (Finset.cons.{u2} α a s ha) f H) (Finset.disjUnion.{u1} β (f a) (Finset.disjUnionᵢ.{u2, u1} α β s f (fun (b : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b (Finset.toSet.{u2} α s)) (c : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Finset.toSet.{u2} α s)) => H b (Multiset.mem_cons_of_mem.{u2} α b a (Finset.val.{u2} α s) hb) c (Multiset.mem_cons_of_mem.{u2} α c a (Finset.val.{u2} α s) hc))) (Iff.mpr (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (f a) (Finset.disjUnionᵢ.{u2, u1} α β s f (fun (b : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b (Finset.toSet.{u2} α s)) (c : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Finset.toSet.{u2} α s)) => H b (Multiset.mem_cons_of_mem.{u2} α b a (Finset.val.{u2} α s) hb) c (Multiset.mem_cons_of_mem.{u2} α c a (Finset.val.{u2} α s) hc)))) (forall {{a_1 : β}}, (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a_1 (f a)) -> (Not (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a_1 (Finset.disjUnionᵢ.{u2, u1} α β s f (fun (b : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b (Finset.toSet.{u2} α s)) (c : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Finset.toSet.{u2} α s)) => H b (Multiset.mem_cons_of_mem.{u2} α b a (Finset.val.{u2} α s) hb) c (Multiset.mem_cons_of_mem.{u2} α c a (Finset.val.{u2} α s) hc)))))) (Finset.disjoint_left.{u1} β (f a) (Finset.disjUnionᵢ.{u2, u1} α β s f (fun (b : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b (Finset.toSet.{u2} α s)) (c : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Finset.toSet.{u2} α s)) => H b (Multiset.mem_cons_of_mem.{u2} α b a (Finset.val.{u2} α s) hb) c (Multiset.mem_cons_of_mem.{u2} α c a (Finset.val.{u2} α s) hc)))) (fun (b : β) (hb : Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (f a)) (h : Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (Finset.disjUnionᵢ.{u2, u1} α β s f (fun (b : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) b (Finset.toSet.{u2} α s)) (c : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) c (Finset.toSet.{u2} α s)) => H b (Multiset.mem_cons_of_mem.{u2} α b a (Finset.val.{u2} α s) hb) c (Multiset.mem_cons_of_mem.{u2} α c a (Finset.val.{u2} α s) hc)))) => Finset.disjUnionᵢ_cons.match_1.{u2, u1} α β s f b (fun (x._@.Mathlib.Data.Finset.Basic._hyg.34936 : Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (f a)))) => False) (Iff.mp (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (Finset.disjUnionᵢ.{u2, u1} α β s f (fun (x._@.Mathlib.Data.Finset.Basic._hyg.34901 : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x._@.Mathlib.Data.Finset.Basic._hyg.34901 (Finset.toSet.{u2} α s)) (x._@.Mathlib.Data.Finset.Basic._hyg.34904 : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x._@.Mathlib.Data.Finset.Basic._hyg.34904 (Finset.toSet.{u2} α s)) => H x._@.Mathlib.Data.Finset.Basic._hyg.34901 (Multiset.mem_cons_of_mem.{u2} α x._@.Mathlib.Data.Finset.Basic._hyg.34901 a (Finset.val.{u2} α s) hb) x._@.Mathlib.Data.Finset.Basic._hyg.34904 (Multiset.mem_cons_of_mem.{u2} α x._@.Mathlib.Data.Finset.Basic._hyg.34904 a (Finset.val.{u2} α s) hc)))) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u2, u1} α β s f b (fun (x._@.Mathlib.Data.Finset.Basic._hyg.34901 : α) (hb : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x._@.Mathlib.Data.Finset.Basic._hyg.34901 (Finset.toSet.{u2} α s)) (x._@.Mathlib.Data.Finset.Basic._hyg.34904 : α) (hc : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x._@.Mathlib.Data.Finset.Basic._hyg.34904 (Finset.toSet.{u2} α s)) => H x._@.Mathlib.Data.Finset.Basic._hyg.34901 (Multiset.mem_cons_of_mem.{u2} α x._@.Mathlib.Data.Finset.Basic._hyg.34901 a (Finset.val.{u2} α s) hb) x._@.Mathlib.Data.Finset.Basic._hyg.34904 (Multiset.mem_cons_of_mem.{u2} α x._@.Mathlib.Data.Finset.Basic._hyg.34904 a (Finset.val.{u2} α s) hc))) h) (fun (w._@.Mathlib.Data.Finset.Basic._hyg.34949 : α) (hc : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) w._@.Mathlib.Data.Finset.Basic._hyg.34949 s) (h : Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (f w._@.Mathlib.Data.Finset.Basic._hyg.34949)) => Iff.mp (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (f a) (f w._@.Mathlib.Data.Finset.Basic._hyg.34949)) (forall {{a_1 : β}}, (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a_1 (f a)) -> (Not (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a_1 (f w._@.Mathlib.Data.Finset.Basic._hyg.34949)))) (Finset.disjoint_left.{u1} β (f a) (f w._@.Mathlib.Data.Finset.Basic._hyg.34949)) (H a (Finset.mem_cons_self.{u2} α a s ha) w._@.Mathlib.Data.Finset.Basic._hyg.34949 (Multiset.mem_cons_of_mem.{u2} α w._@.Mathlib.Data.Finset.Basic._hyg.34949 a (Finset.val.{u2} α s) hc) (Ne.symm.{succ u2} α w._@.Mathlib.Data.Finset.Basic._hyg.34949 a (ne_of_mem_of_not_mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) s w._@.Mathlib.Data.Finset.Basic._hyg.34949 a hc ha))) b hb h))))
Case conversion may be inaccurate. Consider using '#align finset.disj_Union_cons Finset.disjUnionᵢ_consₓ'. -/
@[simp]
theorem disjUnionᵢ_cons (a : α) (s : Finset α) (ha : a ∉ s) (f : α → Finset β) (H) :
    disjUnion (cons a s ha) f H =
      (f a).disjUnion (s.disjUnionₓ f fun b hb c hc => H (mem_cons_of_mem hb) (mem_cons_of_mem hc))
        (disjoint_left.mpr fun b hb h =>
          let ⟨c, hc, h⟩ := mem_disjUnionᵢ.mp h
          disjoint_left.mp
            (H (mem_cons_self a s) (mem_cons_of_mem hc) (ne_of_mem_of_not_mem hc ha).symm) hb h) :=
  eq_of_veq <| Multiset.cons_bind _ _ _
#align finset.disj_Union_cons Finset.disjUnionᵢ_cons

/- warning: finset.singleton_disj_Union -> Finset.singleton_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : α -> (Finset.{u2} β)} (a : α) {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) t}, Eq.{succ u2} (Finset.{u2} β) (Finset.disjUnionₓ.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t h) (t a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {t : α -> (Finset.{u2} β)} (a : α) {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (Finset.toSet.{u1} α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a)) t}, Eq.{succ u2} (Finset.{u2} β) (Finset.disjUnionᵢ.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t h) (t a)
Case conversion may be inaccurate. Consider using '#align finset.singleton_disj_Union Finset.singleton_disjUnionᵢₓ'. -/
@[simp]
theorem singleton_disjUnionᵢ (a : α) {h} : Finset.disjUnion {a} t h = t a :=
  eq_of_veq <| Multiset.singleton_bind _ _
#align finset.singleton_disj_Union Finset.singleton_disjUnionᵢ

/- warning: finset.disj_Union_disj_Union -> Finset.disjUnionᵢ_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (s : Finset.{u1} α) (f : α -> (Finset.{u2} β)) (g : β -> (Finset.{u3} γ)) (h1 : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) f) (h2 : Set.PairwiseDisjoint.{u3, u2} (Finset.{u3} γ) β (Finset.partialOrder.{u3} γ) (Finset.orderBot.{u3} γ) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.disjUnionₓ.{u1, u2} α β s f h1)) g), Eq.{succ u3} (Finset.{u3} γ) (Finset.disjUnionₓ.{u2, u3} β γ (Finset.disjUnionₓ.{u1, u2} α β s f h1) g h2) (Finset.disjUnionₓ.{u1, u3} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) γ (Finset.attach.{u1} α s) (fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) (fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) (ha : Membership.Mem.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.hasMem.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Finset.Set.hasCoeT.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) (Finset.attach.{u1} α s))) (b : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) (hb : Membership.Mem.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.hasMem.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Set.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))) (Finset.Set.hasCoeT.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) (Finset.attach.{u1} α s))) (hab : Ne.{succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) a b) => Iff.mpr (Disjoint.{u3} (Finset.{u3} γ) (Finset.partialOrder.{u3} γ) (Finset.orderBot.{u3} γ) ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) a) ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) b)) (forall {{a_1 : γ}}, (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) a_1 ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) a)) -> (Not (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) a_1 ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) b)))) (Finset.disjoint_left.{u3} γ ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) a) ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) b)) (fun (x : γ) (hxa : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) a)) (hxb : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x ((fun (a : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) b)) => Exists.dcases_on.{succ u2} β (fun (a_1 : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g a_1))) (fun (_fresh.476.110786 : Exists.{succ u2} β (fun (a_1 : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g a_1)))) => False) (Iff.mp (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc)))))) (Exists.{succ u2} β (fun (a_1 : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g a_1)))) (Finset.mem_disjUnionᵢ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) g x (fun (b : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) => h2 b (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hc))))) hxa) (fun (xa : β) (h : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xa))) => Exists.dcases_on.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xa)) (fun (h : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xa))) => False) h (fun (hfa : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (hga : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xa)) => Exists.dcases_on.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g a))) (fun (_fresh.476.110903 : Exists.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g a)))) => False) (Iff.mp (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (Finset.disjUnionₓ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b)) g (fun (b_1 : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b_1 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b)))) => h2 b_1 (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b_1 h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) b) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) b) hc)))))) (Exists.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g a)))) (Finset.mem_disjUnionᵢ.{u2, u3} β γ (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b)) g x (fun (b_1 : β) (hb : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b_1 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b)))) (c : β) (hc : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) c ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b)))) => h2 b_1 (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f b_1 h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) b) hb))) c (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f c h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) c (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) b) hc))))) hxb) (fun (xb : β) (h : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xb))) => Exists.dcases_on.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xb)) (fun (h : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) => Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xb))) => False) h (fun (hfb : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (hgb : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xb)) => Iff.mp (Disjoint.{u3} (Finset.{u3} γ) (Finset.partialOrder.{u3} γ) (Finset.orderBot.{u3} γ) (g xa) (g xb)) (forall {{a : γ}}, (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) a (g xa)) -> (Not (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) a (g xb)))) (Finset.disjoint_left.{u3} γ (g xa) (g xb)) (h2 xa (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f xa h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) hfa))) xb (Iff.mpr (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (Finset.disjUnionₓ.{u1, u2} α β s f h1)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f a)))) (Finset.mem_disjUnionᵢ.{u1, u2} α β s f xb h1) (Exists.intro.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f a))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) (Exists.intro.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) b) hfb))) (id.{0} (Ne.{succ u2} β xa xb) (fun (ᾰ : Eq.{succ u2} β xa xb) => Eq.ndrec.{0, succ u2} β xa (fun (xb : β) => (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) -> (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xb)) -> False) (fun (hfb : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (hgb : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (g xa)) => Iff.mp (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (forall {{a_1 : β}}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a))) -> (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))))) (Finset.disjoint_left.{u2} β (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)) (f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b))) (h1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) a) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) b) (Subtype.prop.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) b) (Function.Injective.ne.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)))))) (Subtype.coe_injective.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) a b hab)) xa hfa hfb) xb ᾰ hfb hgb))) x hga hgb)))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (s : Finset.{u3} α) (f : α -> (Finset.{u2} β)) (g : β -> (Finset.{u1} γ)) (h1 : Set.PairwiseDisjoint.{u2, u3} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (Finset.toSet.{u3} α s) f) (h2 : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} γ) β (Finset.partialOrder.{u1} γ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} γ) (Finset.toSet.{u2} β (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) g), Eq.{succ u1} (Finset.{u1} γ) (Finset.disjUnionᵢ.{u2, u1} β γ (Finset.disjUnionᵢ.{u3, u2} α β s f h1) g h2) (Finset.disjUnionᵢ.{u3, u1} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) γ (Finset.attach.{u3} α s) (fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) (fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) (ha : Membership.mem.{u3, u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) (Set.{u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s))) (Set.instMembershipSet.{u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s))) a (Finset.toSet.{u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) (Finset.attach.{u3} α s))) (b : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) (hb : Membership.mem.{u3, u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) (Set.{u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s))) (Set.instMembershipSet.{u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s))) b (Finset.toSet.{u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) (Finset.attach.{u3} α s))) (hab : Ne.{succ u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) a b) => Iff.mpr (Disjoint.{u1} (Finset.{u1} γ) (Finset.partialOrder.{u1} γ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} γ) ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) a) ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) b)) (forall {{a_1 : γ}}, (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) a_1 ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) a)) -> (Not (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) a_1 ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) b)))) (Finset.disjoint_left.{u1} γ ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) a) ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) b)) (fun (x : γ) (hxa : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) a)) (hxb : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x ((fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) b)) => Exists.casesOn.{succ u2} β (fun (a_1 : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g a_1))) (fun (_fresh.476.110786 : Exists.{succ u2} β (fun (a_1 : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g a_1)))) => False) (Iff.mp (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc)))))) (Exists.{succ u2} β (fun (a_1 : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g a_1)))) (Finset.mem_disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) g x (fun (b : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)))) => h2 b (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hc))))) hxa) (fun (xa : β) (h : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xa))) => And.casesOn.{0} (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xa)) (fun (h : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xa))) => False) h (fun (hfa : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (hga : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xa)) => Exists.casesOn.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g a))) (fun (_fresh.476.110903 : Exists.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g a)))) => False) (Iff.mp (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (Finset.disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b)) g (fun (b_1 : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b_1 (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b)))) => h2 b_1 (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b_1 h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) hc)))))) (Exists.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g a)))) (Finset.mem_disjUnionᵢ.{u2, u1} β γ (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b)) g x (fun (b_1 : β) (hb : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b_1 (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b)))) (c : β) (hc : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) c (Finset.toSet.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b)))) => h2 b_1 (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f b_1 h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) hb))) c (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f c h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) c (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) hc))))) hxb) (fun (xb : β) (h : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xb))) => And.casesOn.{0} (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xb)) (fun (h : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xb))) => False) h (fun (hfb : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (hgb : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xb)) => Iff.mp (Disjoint.{u1} (Finset.{u1} γ) (Finset.partialOrder.{u1} γ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} γ) (g xa) (g xb)) (forall {{a : γ}}, (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) a (g xa)) -> (Not (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) a (g xb)))) (Finset.disjoint_left.{u1} γ (g xa) (g xb)) (h2 xa (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f xa h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) hfa))) xb (Iff.mpr (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (Finset.disjUnionᵢ.{u3, u2} α β s f h1)) (Exists.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f a)))) (Finset.mem_disjUnionᵢ.{u3, u2} α β s f xb h1) (Exists.intro.{succ u3} α (fun (a : α) => And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f a))) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (And.intro (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) hfb))) (fun (a._@.Init.Prelude.139.Mathlib.Data.Finset.Basic._hyg.35178 : Eq.{succ u2} β xa xb) => Eq.ndrec.{0, succ u2} β xa (fun (xb : β) => (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) -> (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xb)) -> False) (fun (hfb : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (hgb : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (g xa)) => Iff.mp (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (forall {{a_1 : β}}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a))) -> (Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))))) (Finset.disjoint_left.{u2} β (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a)) (f (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b))) (h1 (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (Subtype.prop.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) b) (Function.Injective.ne.{succ u3, succ u3} (Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) α (fun (a : Subtype.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) => Subtype.val.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s) a) (Subtype.coe_injective.{succ u3} α (fun (x : α) => Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) x s)) a b hab)) xa hfa hfb) xb a._@.Init.Prelude.139.Mathlib.Data.Finset.Basic._hyg.35178 hfb hgb)) x hga hgb)))))))
Case conversion may be inaccurate. Consider using '#align finset.disj_Union_disj_Union Finset.disjUnionᵢ_disjUnionᵢₓ'. -/
theorem disjUnionᵢ_disjUnionᵢ (s : Finset α) (f : α → Finset β) (g : β → Finset γ) (h1 h2) :
    (s.disjUnionₓ f h1).disjUnionₓ g h2 =
      s.attach.disjUnionₓ
        (fun a =>
          (f a).disjUnionₓ g fun b hb c hc =>
            h2 (mem_disjUnionᵢ.mpr ⟨_, a.Prop, hb⟩) (mem_disjUnionᵢ.mpr ⟨_, a.Prop, hc⟩))
        fun a ha b hb hab =>
        disjoint_left.mpr fun x hxa hxb =>
          by
          obtain ⟨xa, hfa, hga⟩ := mem_disj_Union.mp hxa
          obtain ⟨xb, hfb, hgb⟩ := mem_disj_Union.mp hxb
          refine'
            disjoint_left.mp
              (h2 (mem_disj_Union.mpr ⟨_, a.prop, hfa⟩) (mem_disj_Union.mpr ⟨_, b.prop, hfb⟩) _) hga
              hgb
          rintro rfl
          exact disjoint_left.mp (h1 a.prop b.prop <| subtype.coe_injective.ne hab) hfa hfb :=
  eq_of_veq <| Multiset.bind_assoc.trans (Multiset.attach_bind_coe _ _).symm
#align finset.disj_Union_disj_Union Finset.disjUnionᵢ_disjUnionᵢ

#print Finset.disjUnionᵢ_filter_eq_of_maps_to /-
theorem disjUnionᵢ_filter_eq_of_maps_to [DecidableEq β] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) :
    (t.disjUnionₓ (fun a => s.filterₓ fun c => f c = a) fun x' hx y' hy hne =>
        disjoint_filter_filter' _ _
          (by
            simp_rw [Pi.disjoint_iff, Prop.disjoint_iff]
            rintro i ⟨rfl, rfl⟩
            exact hne rfl)) =
      s :=
  ext fun b => by simpa using h b
#align finset.disj_Union_filter_eq_of_maps_to Finset.disjUnionᵢ_filter_eq_of_maps_to
-/

end DisjUnion

section BUnion

/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/


variable [DecidableEq β] {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

#print Finset.bunionᵢ /-
/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bunionᵢ (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a => (t a).1).toFinset
#align finset.bUnion Finset.bunionᵢ
-/

/- warning: finset.bUnion_val -> Finset.bunionᵢ_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : α -> (Finset.{u2} β)), Eq.{succ u2} (Multiset.{u2} β) (Finset.val.{u2} β (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Multiset.dedup.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.bind.{u1, u2} α β (Finset.val.{u1} α s) (fun (a : α) => Finset.val.{u2} β (t a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (t : α -> (Finset.{u1} β)), Eq.{succ u1} (Multiset.{u1} β) (Finset.val.{u1} β (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Multiset.dedup.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.bind.{u2, u1} α β (Finset.val.{u2} α s) (fun (a : α) => Finset.val.{u1} β (t a))))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_val Finset.bunionᵢ_valₓ'. -/
@[simp]
theorem bunionᵢ_val (s : Finset α) (t : α → Finset β) :
    (s.bunionᵢ t).1 = (s.1.bind fun a => (t a).1).dedup :=
  rfl
#align finset.bUnion_val Finset.bunionᵢ_val

#print Finset.bunionᵢ_empty /-
@[simp]
theorem bunionᵢ_empty : Finset.bunionᵢ ∅ t = ∅ :=
  rfl
#align finset.bUnion_empty Finset.bunionᵢ_empty
-/

/- warning: finset.mem_bUnion -> Finset.mem_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (t a))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {b : β}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (t a))))
Case conversion may be inaccurate. Consider using '#align finset.mem_bUnion Finset.mem_bunionᵢₓ'. -/
@[simp]
theorem mem_bunionᵢ {b : β} : b ∈ s.bunionᵢ t ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [mem_def, bUnion_val, mem_dedup, mem_bind, exists_prop]
#align finset.mem_bUnion Finset.mem_bunionᵢ

#print Finset.coe_bunionᵢ /-
@[simp, norm_cast]
theorem coe_bunionᵢ : (s.bunionᵢ t : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp only [Set.ext_iff, mem_bUnion, Set.mem_unionᵢ, iff_self_iff, mem_coe, imp_true_iff]
#align finset.coe_bUnion Finset.coe_bunionᵢ
-/

/- warning: finset.bUnion_insert -> Finset.bunionᵢ_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} [_inst_2 : DecidableEq.{succ u1} α] {a : α}, Eq.{succ u2} (Finset.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s) t) (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (t a) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : α -> (Finset.{u1} β)} [_inst_2 : DecidableEq.{succ u2} α] {a : α}, Eq.{succ u1} (Finset.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s) t) (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (t a) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_insert Finset.bunionᵢ_insertₓ'. -/
@[simp]
theorem bunionᵢ_insert [DecidableEq α] {a : α} : (insert a s).bunionᵢ t = t a ∪ s.bunionᵢ t :=
  ext fun x => by
    simp only [mem_bUnion, exists_prop, mem_union, mem_insert, or_and_right, exists_or,
      exists_eq_left]
#align finset.bUnion_insert Finset.bunionᵢ_insert

/- warning: finset.bUnion_congr -> Finset.bunionᵢ_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {t₁ : α -> (Finset.{u2} β)} {t₂ : α -> (Finset.{u2} β)}, (Eq.{succ u1} (Finset.{u1} α) s₁ s₂) -> (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s₁) -> (Eq.{succ u2} (Finset.{u2} β) (t₁ a) (t₂ a))) -> (Eq.{succ u2} (Finset.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s₁ t₁) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {t₁ : α -> (Finset.{u1} β)} {t₂ : α -> (Finset.{u1} β)}, (Eq.{succ u2} (Finset.{u2} α) s₁ s₂) -> (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s₁) -> (Eq.{succ u1} (Finset.{u1} β) (t₁ a) (t₂ a))) -> (Eq.{succ u1} (Finset.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s₁ t₁) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_congr Finset.bunionᵢ_congrₓ'. -/
-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]
theorem bunionᵢ_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) : s₁.bunionᵢ t₁ = s₂.bunionᵢ t₂ :=
  ext fun x => by simp (config := { contextual := true }) [hs, ht]
#align finset.bUnion_congr Finset.bunionᵢ_congr

/- warning: finset.disj_Union_eq_bUnion -> Finset.disjUnionᵢ_eq_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Finset.{u2} β)) (hf : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) f), Eq.{succ u2} (Finset.{u2} β) (Finset.disjUnionₓ.{u1, u2} α β s f hf) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (f : α -> (Finset.{u1} β)) (hf : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} β) α (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.toSet.{u2} α s) f), Eq.{succ u1} (Finset.{u1} β) (Finset.disjUnionᵢ.{u2, u1} α β s f hf) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s f)
Case conversion may be inaccurate. Consider using '#align finset.disj_Union_eq_bUnion Finset.disjUnionᵢ_eq_bunionᵢₓ'. -/
@[simp]
theorem disjUnionᵢ_eq_bunionᵢ (s : Finset α) (f : α → Finset β) (hf) :
    s.disjUnionₓ f hf = s.bunionᵢ f :=
  by
  dsimp [disj_Union, Finset.bunionᵢ, Function.comp]
  generalize_proofs h
  exact eq_of_veq h.dedup.symm
#align finset.disj_Union_eq_bUnion Finset.disjUnionᵢ_eq_bunionᵢ

#print Finset.bunionᵢ_subset /-
theorem bunionᵢ_subset {s' : Finset β} : s.bunionᵢ t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' := by
  simp only [subset_iff, mem_bUnion] <;>
    exact ⟨fun H a ha b hb => H ⟨a, ha, hb⟩, fun H b ⟨a, ha, hb⟩ => H a ha hb⟩
#align finset.bUnion_subset Finset.bunionᵢ_subset
-/

#print Finset.singleton_bunionᵢ /-
@[simp]
theorem singleton_bunionᵢ {a : α} : Finset.bunionᵢ {a} t = t a := by
  classical rw [← insert_emptyc_eq, bUnion_insert, bUnion_empty, union_empty]
#align finset.singleton_bUnion Finset.singleton_bunionᵢ
-/

/- warning: finset.bUnion_inter -> Finset.bunionᵢ_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Finset.{u2} β)) (t : Finset.{u2} β), Eq.{succ u2} (Finset.{u2} β) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s f) t) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s (fun (x : α) => Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (f x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (f : α -> (Finset.{u1} β)) (t : Finset.{u1} β), Eq.{succ u1} (Finset.{u1} β) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s f) t) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s (fun (x : α) => Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (f x) t))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_inter Finset.bunionᵢ_interₓ'. -/
theorem bunionᵢ_inter (s : Finset α) (f : α → Finset β) (t : Finset β) :
    s.bunionᵢ f ∩ t = s.bunionᵢ fun x => f x ∩ t :=
  by
  ext x
  simp only [mem_bUnion, mem_inter]
  tauto
#align finset.bUnion_inter Finset.bunionᵢ_inter

#print Finset.inter_bunionᵢ /-
theorem inter_bunionᵢ (t : Finset β) (s : Finset α) (f : α → Finset β) :
    t ∩ s.bunionᵢ f = s.bunionᵢ fun x => t ∩ f x := by
  rw [inter_comm, bUnion_inter] <;> simp [inter_comm]
#align finset.inter_bUnion Finset.inter_bunionᵢ
-/

/- warning: finset.bUnion_bUnion -> Finset.bunionᵢ_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u3} γ] (s : Finset.{u1} α) (f : α -> (Finset.{u2} β)) (g : β -> (Finset.{u3} γ)), Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s f) g) (Finset.bunionᵢ.{u1, u3} α γ (fun (a : γ) (b : γ) => _inst_2 a b) s (fun (a : α) => Finset.bunionᵢ.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) (f a) g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u3} γ] (s : Finset.{u2} α) (f : α -> (Finset.{u1} β)) (g : β -> (Finset.{u3} γ)), Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s f) g) (Finset.bunionᵢ.{u2, u3} α γ (fun (a : γ) (b : γ) => _inst_2 a b) s (fun (a : α) => Finset.bunionᵢ.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) (f a) g))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_bUnion Finset.bunionᵢ_bunionᵢₓ'. -/
theorem bunionᵢ_bunionᵢ [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
    (s.bunionᵢ f).bunionᵢ g = s.bunionᵢ fun a => (f a).bunionᵢ g :=
  by
  ext
  simp only [Finset.mem_bunionᵢ, exists_prop]
  simp_rw [← exists_and_right, ← exists_and_left, and_assoc']
  rw [exists_comm]
#align finset.bUnion_bUnion Finset.bunionᵢ_bunionᵢ

/- warning: finset.bind_to_finset -> Finset.bind_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Multiset.{u1} α) (t : α -> (Multiset.{u2} β)), Eq.{succ u2} (Finset.{u2} β) (Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.bind.{u1, u2} α β s t)) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s) (fun (a : α) => Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (t a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Multiset.{u2} α) (t : α -> (Multiset.{u1} β)), Eq.{succ u1} (Finset.{u1} β) (Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.bind.{u2, u1} α β s t)) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.toFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s) (fun (a : α) => Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (t a)))
Case conversion may be inaccurate. Consider using '#align finset.bind_to_finset Finset.bind_toFinsetₓ'. -/
theorem bind_toFinset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).toFinset = s.toFinset.bunionᵢ fun a => (t a).toFinset :=
  ext fun x => by simp only [Multiset.mem_toFinset, mem_bUnion, Multiset.mem_bind, exists_prop]
#align finset.bind_to_finset Finset.bind_toFinset

/- warning: finset.bUnion_mono -> Finset.bunionᵢ_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t₁ : α -> (Finset.{u2} β)} {t₂ : α -> (Finset.{u2} β)}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (t₁ a) (t₂ a))) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t₁) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t₁ : α -> (Finset.{u1} β)} {t₂ : α -> (Finset.{u1} β)}, (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (t₁ a) (t₂ a))) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t₁) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t₂))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_mono Finset.bunionᵢ_monoₓ'. -/
theorem bunionᵢ_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.bunionᵢ t₁ ⊆ s.bunionᵢ t₂ :=
  by
  have : ∀ b a, a ∈ s → b ∈ t₁ a → ∃ a : α, a ∈ s ∧ b ∈ t₂ a := fun b a ha hb =>
    ⟨a, ha, Finset.mem_of_subset (h a ha) hb⟩
  simpa only [subset_iff, mem_bUnion, exists_imp, and_imp, exists_prop]
#align finset.bUnion_mono Finset.bunionᵢ_mono

#print Finset.bunionᵢ_subset_bunionᵢ_of_subset_left /-
theorem bunionᵢ_subset_bunionᵢ_of_subset_left (t : α → Finset β) (h : s₁ ⊆ s₂) :
    s₁.bunionᵢ t ⊆ s₂.bunionᵢ t := by
  intro x
  simp only [and_imp, mem_bUnion, exists_prop]
  exact Exists.imp fun a ha => ⟨h ha.1, ha.2⟩
#align finset.bUnion_subset_bUnion_of_subset_left Finset.bunionᵢ_subset_bunionᵢ_of_subset_left
-/

#print Finset.subset_bunionᵢ_of_mem /-
theorem subset_bunionᵢ_of_mem (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.bunionᵢ u :=
  singleton_bunionᵢ.Superset.trans <|
    bunionᵢ_subset_bunionᵢ_of_subset_left u <| singleton_subset_iff.2 xs
#align finset.subset_bUnion_of_mem Finset.subset_bunionᵢ_of_mem
-/

/- warning: finset.bUnion_subset_iff_forall_subset -> Finset.bunionᵢ_subset_iff_forall_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : Finset.{u2} β} {f : α -> (Finset.{u2} β)}, Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) s f) t) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (f x) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : Finset.{u1} β} {f : α -> (Finset.{u1} β)}, Iff (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_2 a b) s f) t) (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (f x) t))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_subset_iff_forall_subset Finset.bunionᵢ_subset_iff_forall_subsetₓ'. -/
@[simp]
theorem bunionᵢ_subset_iff_forall_subset {α β : Type _} [DecidableEq β] {s : Finset α}
    {t : Finset β} {f : α → Finset β} : s.bunionᵢ f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t :=
  ⟨fun h x hx => (subset_bunionᵢ_of_mem f hx).trans h, fun h x hx =>
    let ⟨a, ha₁, ha₂⟩ := mem_bunionᵢ.mp hx
    h _ ha₁ ha₂⟩
#align finset.bUnion_subset_iff_forall_subset Finset.bunionᵢ_subset_iff_forall_subset

#print Finset.bunionᵢ_singleton_eq_self /-
@[simp]
theorem bunionᵢ_singleton_eq_self [DecidableEq α] : s.bunionᵢ (singleton : α → Finset α) = s :=
  ext fun x => by simp only [mem_bUnion, mem_singleton, exists_prop, exists_eq_right']
#align finset.bUnion_singleton_eq_self Finset.bunionᵢ_singleton_eq_self
-/

/- warning: finset.filter_bUnion -> Finset.filter_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Finset.{u2} β)) (p : β -> Prop) [_inst_2 : DecidablePred.{succ u2} β p], Eq.{succ u2} (Finset.{u2} β) (Finset.filter.{u2} β p (fun (a : β) => _inst_2 a) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s f)) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s (fun (a : α) => Finset.filter.{u2} β p (fun (a : β) => _inst_2 a) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (f : α -> (Finset.{u1} β)) (p : β -> Prop) [_inst_2 : DecidablePred.{succ u1} β p], Eq.{succ u1} (Finset.{u1} β) (Finset.filter.{u1} β p (fun (a : β) => _inst_2 a) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s f)) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s (fun (a : α) => Finset.filter.{u1} β p (fun (a : β) => _inst_2 a) (f a)))
Case conversion may be inaccurate. Consider using '#align finset.filter_bUnion Finset.filter_bunionᵢₓ'. -/
theorem filter_bunionᵢ (s : Finset α) (f : α → Finset β) (p : β → Prop) [DecidablePred p] :
    (s.bunionᵢ f).filterₓ p = s.bunionᵢ fun a => (f a).filterₓ p :=
  by
  ext b
  simp only [mem_bUnion, exists_prop, mem_filter]
  constructor
  · rintro ⟨⟨a, ha, hba⟩, hb⟩
    exact ⟨a, ha, hba, hb⟩
  · rintro ⟨a, ha, hba, hb⟩
    exact ⟨⟨a, ha, hba⟩, hb⟩
#align finset.filter_bUnion Finset.filter_bunionᵢ

/- warning: finset.bUnion_filter_eq_of_maps_to -> Finset.bunionᵢ_filter_eq_of_maps_to is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u2} β} {f : α -> β}, (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f x) t)) -> (Eq.{succ u1} (Finset.{u1} α) (Finset.bunionᵢ.{u2, u1} β α (fun (a : α) (b : α) => _inst_2 a b) t (fun (a : β) => Finset.filter.{u1} α (fun (c : α) => Eq.{succ u2} β (f c) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] {s : Finset.{u2} α} {t : Finset.{u1} β} {f : α -> β}, (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (f x) t)) -> (Eq.{succ u2} (Finset.{u2} α) (Finset.bunionᵢ.{u1, u2} β α (fun (a : α) (b : α) => _inst_2 a b) t (fun (a : β) => Finset.filter.{u2} α (fun (c : α) => Eq.{succ u1} β (f c) a) (fun (a_1 : α) => _inst_1 (f a_1) a) s)) s)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_filter_eq_of_maps_to Finset.bunionᵢ_filter_eq_of_maps_toₓ'. -/
theorem bunionᵢ_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀ x ∈ s, f x ∈ t) : (t.bunionᵢ fun a => s.filterₓ fun c => f c = a) = s := by
  simpa only [disj_Union_eq_bUnion] using disj_Union_filter_eq_of_maps_to h
#align finset.bUnion_filter_eq_of_maps_to Finset.bunionᵢ_filter_eq_of_maps_to

#print Finset.erase_bunionᵢ /-
theorem erase_bunionᵢ (f : α → Finset β) (s : Finset α) (b : β) :
    (s.bunionᵢ f).eraseₓ b = s.bunionᵢ fun x => (f x).eraseₓ b :=
  by
  ext
  simp only [Finset.mem_bunionᵢ, iff_self_iff, exists_and_left, Finset.mem_erase]
#align finset.erase_bUnion Finset.erase_bunionᵢ
-/

/- warning: finset.bUnion_nonempty -> Finset.bunionᵢ_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)}, Iff (Finset.Nonempty.{u2} β (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => Finset.Nonempty.{u2} β (t x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)}, Iff (Finset.Nonempty.{u2} β (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (Finset.Nonempty.{u2} β (t x))))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_nonempty Finset.bunionᵢ_nonemptyₓ'. -/
@[simp]
theorem bunionᵢ_nonempty : (s.bunionᵢ t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty := by
  simp [Finset.Nonempty, ← exists_and_left, @exists_swap α]
#align finset.bUnion_nonempty Finset.bunionᵢ_nonempty

/- warning: finset.nonempty.bUnion -> Finset.Nonempty.bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)}, (Finset.Nonempty.{u1} α s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Finset.Nonempty.{u2} β (t x))) -> (Finset.Nonempty.{u2} β (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : α -> (Finset.{u1} β)}, (Finset.Nonempty.{u2} α s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Finset.Nonempty.{u1} β (t x))) -> (Finset.Nonempty.{u1} β (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.bUnion Finset.Nonempty.bunionᵢₓ'. -/
theorem Nonempty.bunionᵢ (hs : s.Nonempty) (ht : ∀ x ∈ s, (t x).Nonempty) :
    (s.bunionᵢ t).Nonempty :=
  bunionᵢ_nonempty.2 <| hs.imp fun x hx => ⟨hx, ht x hx⟩
#align finset.nonempty.bUnion Finset.Nonempty.bunionᵢ

/- warning: finset.disjoint_bUnion_left -> Finset.disjoint_bunionᵢ_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (f : α -> (Finset.{u2} β)) (t : Finset.{u2} β), Iff (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s f) t) (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (f i) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (f : α -> (Finset.{u1} β)) (t : Finset.{u1} β), Iff (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s f) t) (forall (i : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i s) -> (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (f i) t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_bUnion_left Finset.disjoint_bunionᵢ_leftₓ'. -/
theorem disjoint_bunionᵢ_left (s : Finset α) (f : α → Finset β) (t : Finset β) :
    Disjoint (s.bunionᵢ f) t ↔ ∀ i ∈ s, Disjoint (f i) t := by
  classical
    refine' s.induction _ _
    · simp only [forall_mem_empty_iff, bUnion_empty, disjoint_empty_left]
    · intro i s his ih
      simp only [disjoint_union_left, bUnion_insert, his, forall_mem_insert, ih]
#align finset.disjoint_bUnion_left Finset.disjoint_bunionᵢ_left

/- warning: finset.disjoint_bUnion_right -> Finset.disjoint_bunionᵢ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u2} β) (t : Finset.{u1} α) (f : α -> (Finset.{u2} β)), Iff (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) s (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) t f)) (forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i t) -> (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) s (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (s : Finset.{u2} β) (t : Finset.{u1} α) (f : α -> (Finset.{u2} β)), Iff (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) s (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) t f)) (forall (i : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) i t) -> (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) s (f i)))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_bUnion_right Finset.disjoint_bunionᵢ_rightₓ'. -/
theorem disjoint_bunionᵢ_right (s : Finset β) (t : Finset α) (f : α → Finset β) :
    Disjoint s (t.bunionᵢ f) ↔ ∀ i ∈ t, Disjoint s (f i) := by
  simpa only [disjoint_comm] using disjoint_bUnion_left t f s
#align finset.disjoint_bUnion_right Finset.disjoint_bunionᵢ_right

end BUnion

/-! ### choose -/


section Choose

variable (p : α → Prop) [DecidablePred p] (l : Finset α)

#print Finset.chooseX /-
/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  Multiset.chooseX p l.val hp
#align finset.choose_x Finset.chooseX
-/

#print Finset.choose /-
/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
#align finset.choose Finset.choose
-/

#print Finset.choose_spec /-
theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
#align finset.choose_spec Finset.choose_spec
-/

#print Finset.choose_mem /-
theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
#align finset.choose_mem Finset.choose_mem
-/

#print Finset.choose_property /-
theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
#align finset.choose_property Finset.choose_property
-/

end Choose

section Pairwise

variable {s : Finset α}

/- warning: finset.pairwise_subtype_iff_pairwise_finset' -> Finset.pairwise_subtype_iff_pairwise_finset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} (r : β -> β -> Prop) (f : α -> β), Iff (Pairwise.{u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) (Function.onFun.{succ u1, succ u2, 1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) β Prop r (fun (x : coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) x)))) (Set.Pairwise.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) (Function.onFun.{succ u1, succ u2, 1} α β Prop r f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} (r : β -> β -> Prop) (f : α -> β), Iff (Pairwise.{u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) (Function.onFun.{succ u2, succ u1, 1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) β Prop r (fun (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) x)))) (Set.Pairwise.{u2} α (Finset.toSet.{u2} α s) (Function.onFun.{succ u2, succ u1, 1} α β Prop r f))
Case conversion may be inaccurate. Consider using '#align finset.pairwise_subtype_iff_pairwise_finset' Finset.pairwise_subtype_iff_pairwise_finset'ₓ'. -/
theorem pairwise_subtype_iff_pairwise_finset' (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f) :=
  pairwise_subtype_iff_pairwise_set (s : Set α) (r on f)
#align finset.pairwise_subtype_iff_pairwise_finset' Finset.pairwise_subtype_iff_pairwise_finset'

#print Finset.pairwise_subtype_iff_pairwise_finset /-
theorem pairwise_subtype_iff_pairwise_finset (r : α → α → Prop) :
    Pairwise (r on fun x : s => x) ↔ (s : Set α).Pairwise r :=
  pairwise_subtype_iff_pairwise_finset' r id
#align finset.pairwise_subtype_iff_pairwise_finset Finset.pairwise_subtype_iff_pairwise_finset
-/

/- warning: finset.pairwise_cons' -> Finset.pairwise_cons' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {a : α} (ha : Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (r : β -> β -> Prop) (f : α -> β), Iff (Pairwise.{u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) (Function.onFun.{succ u1, succ u2, 1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) β Prop r (fun (a_1 : coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) (Finset.cons.{u1} α a s ha)) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Finset.cons.{u1} α a s ha)))))) a_1)))) (And (Pairwise.{u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) (Function.onFun.{succ u1, succ u2, 1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) β Prop r (fun (a : coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) a)))) (forall (b : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) -> (And (r (f a) (f b)) (r (f b) (f a)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {a : α} (ha : Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) (r : β -> β -> Prop) (f : α -> β), Iff (Pairwise.{u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.cons.{u2} α a s ha))) (Function.onFun.{succ u2, succ u1, 1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.cons.{u2} α a s ha))) β Prop r (fun (a_1 : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.cons.{u2} α a s ha))) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x (Finset.cons.{u2} α a s ha)) a_1)))) (And (Pairwise.{u2} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) (Function.onFun.{succ u2, succ u1, 1} (Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) β Prop r (fun (a : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) a)))) (forall (b : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) b s) -> (And (r (f a) (f b)) (r (f b) (f a)))))
Case conversion may be inaccurate. Consider using '#align finset.pairwise_cons' Finset.pairwise_cons'ₓ'. -/
theorem pairwise_cons' {a : α} (ha : a ∉ s) (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun a : s.cons a ha => f a) ↔
      Pairwise (r on fun a : s => f a) ∧ ∀ b ∈ s, r (f a) (f b) ∧ r (f b) (f a) :=
  by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert,
    Finset.mem_coe, and_congr_right_iff]
  exact fun hsr =>
    ⟨fun h b hb =>
      h b hb <| by
        rintro rfl
        contradiction,
      fun h b hb _ => h b hb⟩
#align finset.pairwise_cons' Finset.pairwise_cons'

#print Finset.pairwise_cons /-
theorem pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
    Pairwise (r on fun a : s.cons a ha => a) ↔
      Pairwise (r on fun a : s => a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_cons' ha r id
#align finset.pairwise_cons Finset.pairwise_cons
-/

end Pairwise

end Finset

namespace Equiv

#print Equiv.sigmaEquivOptionOfInhabited /-
/--
Inhabited types are equivalent to `option β` for some `β` by identifying `default α` with `none`.
-/
def sigmaEquivOptionOfInhabited (α : Type u) [Inhabited α] [DecidableEq α] :
    Σβ : Type u, α ≃ Option β :=
  ⟨{ x : α // x ≠ default },
    { toFun := fun x : α => if h : x = default then none else some ⟨x, h⟩
      invFun := Option.elim' default coe
      left_inv := fun x => by
        dsimp only
        split_ifs <;> simp [*]
      right_inv := by
        rintro (_ | ⟨x, h⟩)
        · simp
        · dsimp only
          split_ifs with hi
          · simpa [h] using hi
          · simp }⟩
#align equiv.sigma_equiv_option_of_inhabited Equiv.sigmaEquivOptionOfInhabited
-/

end Equiv

namespace Multiset

variable [DecidableEq α]

/- warning: multiset.disjoint_to_finset -> Multiset.disjoint_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m1 : Multiset.{u1} α} {m2 : Multiset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m1) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m2)) (Multiset.Disjoint.{u1} α m1 m2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {m1 : Multiset.{u1} α} {m2 : Multiset.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m1) (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m2)) (Multiset.Disjoint.{u1} α m1 m2)
Case conversion may be inaccurate. Consider using '#align multiset.disjoint_to_finset Multiset.disjoint_toFinsetₓ'. -/
theorem disjoint_toFinset {m1 m2 : Multiset α} :
    Disjoint m1.toFinset m2.toFinset ↔ m1.Disjoint m2 :=
  by
  rw [Finset.disjoint_iff_ne]
  refine' ⟨fun h a ha1 ha2 => _, _⟩
  · rw [← Multiset.mem_toFinset] at ha1 ha2
    exact h _ ha1 _ ha2 rfl
  · rintro h a ha b hb rfl
    rw [Multiset.mem_toFinset] at ha hb
    exact h ha hb
#align multiset.disjoint_to_finset Multiset.disjoint_toFinset

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

/- warning: list.disjoint_to_finset_iff_disjoint -> List.disjoint_toFinset_iff_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {l : List.{u1} α} {l' : List.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l')) (List.Disjoint.{u1} α l l')
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {l : List.{u1} α} {l' : List.{u1} α}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) l')) (List.Disjoint.{u1} α l l')
Case conversion may be inaccurate. Consider using '#align list.disjoint_to_finset_iff_disjoint List.disjoint_toFinset_iff_disjointₓ'. -/
theorem disjoint_toFinset_iff_disjoint : Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_toFinset
#align list.disjoint_to_finset_iff_disjoint List.disjoint_toFinset_iff_disjoint

end List

-- Assert that we define `finset` without the material on `list.sublists`.
-- Note that we cannot use `list.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen

assert_not_exists Multiset.powerset

