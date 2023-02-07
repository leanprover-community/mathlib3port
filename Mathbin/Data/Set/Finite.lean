/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller

! This file was ported from Lean 3 source module data.set.finite
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Set.Functor
import Mathbin.Data.Finite.Basic

/-!
# Finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines predicates for finite and infinite sets and provides
`fintype` instances for many set constructions. It also proves basic facts
about finite sets and gives ways to manipulate `set.finite` expressions.

## Main definitions

* `set.finite : set α → Prop`
* `set.infinite : set α → Prop`
* `set.to_finite` to prove `set.finite` for a `set` from a `finite` instance.
* `set.finite.to_finset` to noncomputably produce a `finset` from a `set.finite` proof.
  (See `set.to_finset` for a computable version.)

## Implementation

A finite set is defined to be a set whose coercion to a type has a `fintype` instance.
Since `set.finite` is `Prop`-valued, this is the mere fact that the `fintype` instance
exists.

There are two components to finiteness constructions. The first is `fintype` instances for each
construction. This gives a way to actually compute a `finset` that represents the set, and these
may be accessed using `set.to_finset`. This gets the `finset` in the correct form, since otherwise
`finset.univ : finset s` is a `finset` for the subtype for `s`. The second component is
"constructors" for `set.finite` that give proofs that `fintype` instances exist classically given
other `set.finite` proofs. Unlike the `fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/


open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

#print Set.Finite /-
/-- A set is finite if there is a `finset` with the same elements.
This is represented as there being a `fintype` instance for the set
coerced to a type.

Note: this is a custom inductive type rather than `nonempty (fintype s)`
so that it won't be frozen as a local instance. -/
@[protected]
inductive Finite (s : Set α) : Prop
  | intro : Fintype s → Finite
#align set.finite Set.Finite
-/

-- The `protected` attribute does not take effect within the same namespace block.
end Set

namespace Set

#print Set.finite_def /-
theorem finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s) :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩
#align set.finite_def Set.finite_def
-/

alias finite_def ↔ finite.nonempty_fintype _
#align set.finite.nonempty_fintype Set.Finite.nonempty_fintype

#print Set.finite_coe_iff /-
theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := by
  rw [finite_iff_nonempty_fintype, finite_def]
#align set.finite_coe_iff Set.finite_coe_iff
-/

#print Set.toFinite /-
/-- Constructor for `set.finite` using a `finite` instance. -/
theorem toFinite (s : Set α) [Finite s] : s.Finite :=
  finite_coe_iff.mp ‹_›
#align set.to_finite Set.toFinite
-/

#print Set.Finite.ofFinset /-
/-- Construct a `finite` instance for a `set` from a `finset` with the same elements. -/
protected theorem Finite.ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : p.Finite :=
  ⟨Fintype.ofFinset s H⟩
#align set.finite.of_finset Set.Finite.ofFinset
-/

#print Set.Finite.to_subtype /-
/-- Projection of `set.finite` to its `finite` instance.
This is intended to be used with dot notation.
See also `set.finite.fintype` and `set.finite.nonempty_fintype`. -/
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s :=
  finite_coe_iff.mpr h
#align set.finite.to_subtype Set.Finite.to_subtype
-/

#print Set.Finite.fintype /-
/-- A finite set coerced to a type is a `fintype`.
This is the `fintype` projection for a `set.finite`.

Note that because `finite` isn't a typeclass, this definition will not fire if it
is made into an instance -/
protected noncomputable def Finite.fintype {s : Set α} (h : s.Finite) : Fintype s :=
  h.nonempty_fintype.some
#align set.finite.fintype Set.Finite.fintype
-/

#print Set.Finite.toFinset /-
/-- Using choice, get the `finset` that represents this `set.` -/
protected noncomputable def Finite.toFinset {s : Set α} (h : s.Finite) : Finset α :=
  @Set.toFinset _ _ h.Fintype
#align set.finite.to_finset Set.Finite.toFinset
-/

#print Set.Finite.exists_finset /-
theorem Finite.exists_finset {s : Set α} (h : s.Finite) :
    ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s :=
  by
  cases h
  exact ⟨s.to_finset, fun _ => mem_to_finset⟩
#align set.finite.exists_finset Set.Finite.exists_finset
-/

#print Set.Finite.exists_finset_coe /-
theorem Finite.exists_finset_coe {s : Set α} (h : s.Finite) : ∃ s' : Finset α, ↑s' = s :=
  by
  cases h
  exact ⟨s.to_finset, s.coe_to_finset⟩
#align set.finite.exists_finset_coe Set.Finite.exists_finset_coe
-/

/-- Finite sets can be lifted to finsets. -/
instance : CanLift (Set α) (Finset α) coe Set.Finite where prf s hs := hs.exists_finset_coe

#print Set.Infinite /-
/-- A set is infinite if it is not finite.

This is protected so that it does not conflict with global `infinite`. -/
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite
#align set.infinite Set.Infinite
-/

#print Set.not_infinite /-
@[simp]
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  Classical.not_not
#align set.not_infinite Set.not_infinite
-/

#print Set.finite_or_infinite /-
/-- See also `finite_or_infinite`, `fintype_or_infinite`. -/
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _
#align set.finite_or_infinite Set.finite_or_infinite
-/

/-! ### Basic properties of `set.finite.to_finset` -/


namespace Finite

variable {s t : Set α} {a : α} {hs : s.Finite} {ht : t.Finite}

#print Set.Finite.mem_toFinset /-
@[simp]
protected theorem mem_toFinset (h : s.Finite) : a ∈ h.toFinset ↔ a ∈ s :=
  @mem_toFinset _ _ h.Fintype _
#align set.finite.mem_to_finset Set.Finite.mem_toFinset
-/

#print Set.Finite.coe_toFinset /-
@[simp]
protected theorem coe_toFinset (h : s.Finite) : (h.toFinset : Set α) = s :=
  @coe_toFinset _ _ h.Fintype
#align set.finite.coe_to_finset Set.Finite.coe_toFinset
-/

#print Set.Finite.toFinset_nonempty /-
@[simp]
protected theorem toFinset_nonempty (h : s.Finite) : h.toFinset.Nonempty ↔ s.Nonempty := by
  rw [← Finset.coe_nonempty, finite.coe_to_finset]
#align set.finite.to_finset_nonempty Set.Finite.toFinset_nonempty
-/

#print Set.Finite.coeSort_toFinset /-
/-- Note that this is an equality of types not holding definitionally. Use wisely. -/
theorem coeSort_toFinset (h : s.Finite) : ↥h.toFinset = ↥s := by
  rw [← Finset.coe_sort_coe _, h.coe_to_finset]
#align set.finite.coe_sort_to_finset Set.Finite.coeSort_toFinset
-/

#print Set.Finite.toFinset_inj /-
@[simp]
protected theorem toFinset_inj : hs.toFinset = ht.toFinset ↔ s = t :=
  @toFinset_inj _ _ _ hs.Fintype ht.Fintype
#align set.finite.to_finset_inj Set.Finite.toFinset_inj
-/

#print Set.Finite.toFinset_subset /-
@[simp]
theorem toFinset_subset {t : Finset α} : hs.toFinset ⊆ t ↔ s ⊆ t := by
  rw [← Finset.coe_subset, finite.coe_to_finset]
#align set.finite.to_finset_subset Set.Finite.toFinset_subset
-/

/- warning: set.finite.to_finset_ssubset -> Set.Finite.toFinset_sSubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {hs : Set.Finite.{u1} α s} {t : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.Finite.toFinset.{u1} α s hs) t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {hs : Set.Finite.{u1} α s} {t : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.Finite.toFinset.{u1} α s hs) t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Finset.toSet.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_ssubset Set.Finite.toFinset_sSubsetₓ'. -/
@[simp]
theorem toFinset_sSubset {t : Finset α} : hs.toFinset ⊂ t ↔ s ⊂ t := by
  rw [← Finset.coe_ssubset, finite.coe_to_finset]
#align set.finite.to_finset_ssubset Set.Finite.toFinset_sSubset

#print Set.Finite.subset_toFinset /-
@[simp]
theorem subset_toFinset {s : Finset α} : s ⊆ ht.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, finite.coe_to_finset]
#align set.finite.subset_to_finset Set.Finite.subset_toFinset
-/

/- warning: set.finite.ssubset_to_finset -> Set.Finite.sSubset_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : Set.{u1} α} {ht : Set.Finite.{u1} α t} {s : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) s (Set.Finite.toFinset.{u1} α t ht)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) t)
but is expected to have type
  forall {α : Type.{u1}} {t : Set.{u1} α} {ht : Set.Finite.{u1} α t} {s : Finset.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) s (Set.Finite.toFinset.{u1} α t ht)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (Finset.toSet.{u1} α s) t)
Case conversion may be inaccurate. Consider using '#align set.finite.ssubset_to_finset Set.Finite.sSubset_toFinsetₓ'. -/
@[simp]
theorem sSubset_toFinset {s : Finset α} : s ⊂ ht.toFinset ↔ ↑s ⊂ t := by
  rw [← Finset.coe_ssubset, finite.coe_to_finset]
#align set.finite.ssubset_to_finset Set.Finite.sSubset_toFinset

#print Set.Finite.toFinset_subset_toFinset /-
@[mono]
protected theorem toFinset_subset_toFinset : hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t := by
  simp only [← Finset.coe_subset, finite.coe_to_finset]
#align set.finite.to_finset_subset_to_finset Set.Finite.toFinset_subset_toFinset
-/

/- warning: set.finite.to_finset_ssubset_to_finset -> Set.Finite.toFinset_ssubset_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {hs : Set.Finite.{u1} α s} {ht : Set.Finite.{u1} α t}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {hs : Set.Finite.{u1} α s} {ht : Set.Finite.{u1} α t}, Iff (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_ssubset_to_finset Set.Finite.toFinset_ssubset_toFinsetₓ'. -/
@[mono]
protected theorem toFinset_ssubset_toFinset : hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  simp only [← Finset.coe_ssubset, finite.coe_to_finset]
#align set.finite.to_finset_ssubset_to_finset Set.Finite.toFinset_ssubset_toFinset

alias finite.to_finset_subset_to_finset ↔ _ to_finset_mono
#align set.finite.to_finset_mono Set.Finite.toFinset_mono

/- warning: set.finite.to_finset_strict_mono -> Set.Finite.toFinset_strictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {hs : Set.Finite.{u1} α s} {ht : Set.Finite.{u1} α t}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.hasSsubset.{u1} α) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {hs : Set.Finite.{u1} α s} {ht : Set.Finite.{u1} α t}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (HasSSubset.SSubset.{u1} (Finset.{u1} α) (Finset.instHasSSubsetFinset.{u1} α) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_strict_mono Set.Finite.toFinset_strictMonoₓ'. -/
alias finite.to_finset_ssubset_to_finset ↔ _ to_finset_strict_mono
#align set.finite.to_finset_strict_mono Set.Finite.toFinset_strictMono

attribute [protected] to_finset_mono to_finset_strict_mono

#print Set.Finite.toFinset_setOf /-
@[simp]
protected theorem toFinset_setOf [Fintype α] (p : α → Prop) [DecidablePred p]
    (h : { x | p x }.Finite) : h.toFinset = Finset.univ.filterₓ p :=
  by
  ext
  simp
#align set.finite.to_finset_set_of Set.Finite.toFinset_setOf
-/

/- warning: set.finite.disjoint_to_finset -> Set.Finite.disjoint_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {hs : Set.Finite.{u1} α s} {ht : Set.Finite.{u1} α t}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {hs : Set.Finite.{u1} α s} {ht : Set.Finite.{u1} α t}, Iff (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht)) (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t)
Case conversion may be inaccurate. Consider using '#align set.finite.disjoint_to_finset Set.Finite.disjoint_toFinsetₓ'. -/
@[simp]
theorem disjoint_toFinset {hs : s.Finite} {ht : t.Finite} :
    Disjoint hs.toFinset ht.toFinset ↔ Disjoint s t :=
  @disjoint_toFinset _ _ _ hs.Fintype ht.Fintype
#align set.finite.disjoint_to_finset Set.Finite.disjoint_toFinset

/- warning: set.finite.to_finset_inter -> Set.Finite.toFinset_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) h) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) h) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_inter Set.Finite.toFinset_interₓ'. -/
protected theorem toFinset_inter [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∩ t).Finite) : h.toFinset = hs.toFinset ∩ ht.toFinset :=
  by
  ext
  simp
#align set.finite.to_finset_inter Set.Finite.toFinset_inter

/- warning: set.finite.to_finset_union -> Set.Finite.toFinset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) h) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) h) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_union Set.Finite.toFinset_unionₓ'. -/
protected theorem toFinset_union [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∪ t).Finite) : h.toFinset = hs.toFinset ∪ ht.toFinset :=
  by
  ext
  simp
#align set.finite.to_finset_union Set.Finite.toFinset_union

/- warning: set.finite.to_finset_diff -> Set.Finite.toFinset_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) h) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) h) (SDiff.sdiff.{u1} (Finset.{u1} α) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_diff Set.Finite.toFinset_diffₓ'. -/
protected theorem toFinset_diff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s \ t).Finite) : h.toFinset = hs.toFinset \ ht.toFinset :=
  by
  ext
  simp
#align set.finite.to_finset_diff Set.Finite.toFinset_diff

/- warning: set.finite.to_finset_symm_diff -> Set.Finite.toFinset_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) h) (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.hasSdiff.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] (hs : Set.Finite.{u1} α s) (ht : Set.Finite.{u1} α t) (h : Set.Finite.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) h) (symmDiff.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Finset.instSDiffFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Set.Finite.toFinset.{u1} α s hs) (Set.Finite.toFinset.{u1} α t ht))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_symm_diff Set.Finite.toFinset_symmDiffₓ'. -/
protected theorem toFinset_symmDiff [DecidableEq α] (hs : s.Finite) (ht : t.Finite)
    (h : (s ∆ t).Finite) : h.toFinset = hs.toFinset ∆ ht.toFinset :=
  by
  ext
  simp [mem_symm_diff, Finset.mem_symmDiff]
#align set.finite.to_finset_symm_diff Set.Finite.toFinset_symmDiff

/- warning: set.finite.to_finset_compl -> Set.Finite.toFinset_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (hs : Set.Finite.{u1} α s) (h : Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) h) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.booleanAlgebra.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) (Set.Finite.toFinset.{u1} α s hs))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] (hs : Set.Finite.{u1} α s) (h : Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)), Eq.{succ u1} (Finset.{u1} α) (Set.Finite.toFinset.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) h) (HasCompl.compl.{u1} (Finset.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Finset.{u1} α) (Finset.instBooleanAlgebraFinset.{u1} α _inst_2 (fun (a : α) (b : α) => _inst_1 a b))) (Set.Finite.toFinset.{u1} α s hs))
Case conversion may be inaccurate. Consider using '#align set.finite.to_finset_compl Set.Finite.toFinset_complₓ'. -/
protected theorem toFinset_compl [DecidableEq α] [Fintype α] (hs : s.Finite) (h : sᶜ.Finite) :
    h.toFinset = hs.toFinsetᶜ := by
  ext
  simp
#align set.finite.to_finset_compl Set.Finite.toFinset_compl

#print Set.Finite.toFinset_empty /-
@[simp]
protected theorem toFinset_empty (h : (∅ : Set α).Finite) : h.toFinset = ∅ :=
  by
  ext
  simp
#align set.finite.to_finset_empty Set.Finite.toFinset_empty
-/

#print Set.Finite.toFinset_univ /-
-- Note: Not `simp` because `set.finite.to_finset_set_of` already proves it
@[simp]
protected theorem toFinset_univ [Fintype α] (h : (Set.univ : Set α).Finite) :
    h.toFinset = Finset.univ := by
  ext
  simp
#align set.finite.to_finset_univ Set.Finite.toFinset_univ
-/

#print Set.Finite.toFinset_eq_empty /-
@[simp]
protected theorem toFinset_eq_empty {h : s.Finite} : h.toFinset = ∅ ↔ s = ∅ :=
  @toFinset_eq_empty _ _ h.Fintype
#align set.finite.to_finset_eq_empty Set.Finite.toFinset_eq_empty
-/

#print Set.Finite.toFinset_eq_univ /-
@[simp]
protected theorem toFinset_eq_univ [Fintype α] {h : s.Finite} :
    h.toFinset = Finset.univ ↔ s = univ :=
  @toFinset_eq_univ _ _ _ h.Fintype
#align set.finite.to_finset_eq_univ Set.Finite.toFinset_eq_univ
-/

#print Set.Finite.toFinset_image /-
protected theorem toFinset_image [DecidableEq β] (f : α → β) (hs : s.Finite) (h : (f '' s).Finite) :
    h.toFinset = hs.toFinset.image f := by
  ext
  simp
#align set.finite.to_finset_image Set.Finite.toFinset_image
-/

#print Set.Finite.toFinset_range /-
@[simp]
protected theorem toFinset_range [DecidableEq α] [Fintype β] (f : β → α) (h : (range f).Finite) :
    h.toFinset = Finset.univ.image f := by
  ext
  simp
#align set.finite.to_finset_range Set.Finite.toFinset_range
-/

end Finite

/-! ### Fintype instances

Every instance here should have a corresponding `set.finite` constructor in the next section.
 -/


section FintypeInstances

#print Set.fintypeUniv /-
instance fintypeUniv [Fintype α] : Fintype (@univ α) :=
  Fintype.ofEquiv α (Equiv.Set.univ α).symm
#align set.fintype_univ Set.fintypeUniv
-/

#print Set.fintypeOfFiniteUniv /-
/-- If `(set.univ : set α)` is finite then `α` is a finite type. -/
noncomputable def fintypeOfFiniteUniv (H : (univ : Set α).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (univ : Set α) H.Fintype (Equiv.Set.univ _)
#align set.fintype_of_finite_univ Set.fintypeOfFiniteUniv
-/

/- warning: set.fintype_union -> Set.fintypeUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Set.{u1} α) (t : Set.{u1} α) [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Set.{u1} α) (t : Set.{u1} α) [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)], Fintype.{u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.fintype_union Set.fintypeUnionₓ'. -/
instance fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s ∪ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∪ t.toFinset) <| by simp
#align set.fintype_union Set.fintypeUnion

#print Set.fintypeSep /-
instance fintypeSep (s : Set α) (p : α → Prop) [Fintype s] [DecidablePred p] :
    Fintype ({ a ∈ s | p a } : Set α) :=
  Fintype.ofFinset (s.toFinset.filterₓ p) <| by simp
#align set.fintype_sep Set.fintypeSep
-/

/- warning: set.fintype_inter -> Set.fintypeInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)], Fintype.{u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.fintype_inter Set.fintypeInterₓ'. -/
instance fintypeInter (s t : Set α) [DecidableEq α] [Fintype s] [Fintype t] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∩ t.toFinset) <| by simp
#align set.fintype_inter Set.fintypeInter

/- warning: set.fintype_inter_of_left -> Set.fintypeInterOfLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x t)], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) _x t)], Fintype.{u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.fintype_inter_of_left Set.fintypeInterOfLeftₓ'. -/
/-- A `fintype` instance for set intersection where the left set has a `fintype` instance. -/
instance fintypeInterOfLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (s.toFinset.filterₓ (· ∈ t)) <| by simp
#align set.fintype_inter_of_left Set.fintypeInterOfLeft

/- warning: set.fintype_inter_of_right -> Set.fintypeInterOfRight is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)] [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α t)] [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) _x s)], Fintype.{u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.fintype_inter_of_right Set.fintypeInterOfRightₓ'. -/
/-- A `fintype` instance for set intersection where the right set has a `fintype` instance. -/
instance fintypeInterOfRight (s t : Set α) [Fintype t] [DecidablePred (· ∈ s)] :
    Fintype (s ∩ t : Set α) :=
  Fintype.ofFinset (t.toFinset.filterₓ (· ∈ s)) <| by simp [and_comm']
#align set.fintype_inter_of_right Set.fintypeInterOfRight

#print Set.fintypeSubset /-
/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· ∈ t)] (h : t ⊆ s) :
    Fintype t := by
  rw [← inter_eq_self_of_subset_right h]
  apply Set.fintypeInterOfLeft
#align set.fintype_subset Set.fintypeSubset
-/

/- warning: set.fintype_diff -> Set.fintypeDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Set.{u1} α) (t : Set.{u1} α) [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Set.{u1} α) (t : Set.{u1} α) [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_3 : Fintype.{u1} (Set.Elem.{u1} α t)], Fintype.{u1} (Set.Elem.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.fintype_diff Set.fintypeDiffₓ'. -/
instance fintypeDiff [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] :
    Fintype (s \ t : Set α) :=
  Fintype.ofFinset (s.toFinset \ t.toFinset) <| by simp
#align set.fintype_diff Set.fintypeDiff

/- warning: set.fintype_diff_left -> Set.fintypeDiffLeft is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x t)], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_2 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) _x t)], Fintype.{u1} (Set.Elem.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.fintype_diff_left Set.fintypeDiffLeftₓ'. -/
instance fintypeDiffLeft (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] :
    Fintype (s \ t : Set α) :=
  Set.fintypeSep s (· ∈ tᶜ)
#align set.fintype_diff_left Set.fintypeDiffLeft

#print Set.fintypeUnionᵢ /-
instance fintypeUnionᵢ [DecidableEq α] [Fintype (PLift ι)] (f : ι → Set α) [∀ i, Fintype (f i)] :
    Fintype (⋃ i, f i) :=
  Fintype.ofFinset (Finset.univ.bunionᵢ fun i : PLift ι => (f i.down).toFinset) <| by simp
#align set.fintype_Union Set.fintypeUnionᵢ
-/

#print Set.fintypeUnionₛ /-
instance fintypeUnionₛ [DecidableEq α] {s : Set (Set α)} [Fintype s]
    [H : ∀ t : s, Fintype (t : Set α)] : Fintype (⋃₀ s) :=
  by
  rw [sUnion_eq_Union]
  exact @Set.fintypeUnionᵢ _ _ _ _ _ H
#align set.fintype_sUnion Set.fintypeUnionₛ
-/

#print Set.fintypeBUnionᵢ /-
/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintypeBUnionᵢ [DecidableEq α] {ι : Type _} (s : Set ι) [Fintype s] (t : ι → Set α)
    (H : ∀ i ∈ s, Fintype (t i)) : Fintype (⋃ x ∈ s, t x) :=
  Fintype.ofFinset
      (s.toFinset.attach.bunionᵢ fun x =>
        haveI := H x (by simpa using x.property)
        (t x).toFinset) <|
    by simp
#align set.fintype_bUnion Set.fintypeBUnionᵢ
-/

#print Set.fintypeBUnionᵢ' /-
instance fintypeBUnionᵢ' [DecidableEq α] {ι : Type _} (s : Set ι) [Fintype s] (t : ι → Set α)
    [∀ i, Fintype (t i)] : Fintype (⋃ x ∈ s, t x) :=
  Fintype.ofFinset (s.toFinset.bunionᵢ fun x => (t x).toFinset) <| by simp
#align set.fintype_bUnion' Set.fintypeBUnionᵢ'
-/

#print Set.fintypeBind /-
/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    (H : ∀ a ∈ s, Fintype (f a)) : Fintype (s >>= f) :=
  Set.fintypeBUnionᵢ s f H
#align set.fintype_bind Set.fintypeBind
-/

#print Set.fintypeBind' /-
instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β)
    [H : ∀ a, Fintype (f a)] : Fintype (s >>= f) :=
  Set.fintypeBUnionᵢ' s f
#align set.fintype_bind' Set.fintypeBind'
-/

#print Set.fintypeEmpty /-
instance fintypeEmpty : Fintype (∅ : Set α) :=
  Fintype.ofFinset ∅ <| by simp
#align set.fintype_empty Set.fintypeEmpty
-/

#print Set.fintypeSingleton /-
instance fintypeSingleton (a : α) : Fintype ({a} : Set α) :=
  Fintype.ofFinset {a} <| by simp
#align set.fintype_singleton Set.fintypeSingleton
-/

#print Set.fintypePure /-
instance fintypePure : ∀ a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton
#align set.fintype_pure Set.fintypePure
-/

#print Set.fintypeInsert /-
/-- A `fintype` instance for inserting an element into a `set` using the
corresponding `insert` function on `finset`. This requires `decidable_eq α`.
There is also `set.fintype_insert'` when `a ∈ s` is decidable. -/
instance fintypeInsert (a : α) (s : Set α) [DecidableEq α] [Fintype s] :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset (insert a s.toFinset) <| by simp
#align set.fintype_insert Set.fintypeInsert
-/

#print Set.fintypeInsertOfNotMem /-
/-- A `fintype` structure on `insert a s` when inserting a new element. -/
def fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    Fintype (insert a s : Set α) :=
  Fintype.ofFinset ⟨a ::ₘ s.toFinset.1, s.toFinset.Nodup.cons (by simp [h])⟩ <| by simp
#align set.fintype_insert_of_not_mem Set.fintypeInsertOfNotMem
-/

#print Set.fintypeInsertOfMem /-
/-- A `fintype` structure on `insert a s` when inserting a pre-existing element. -/
def fintypeInsertOfMem {a : α} (s : Set α) [Fintype s] (h : a ∈ s) : Fintype (insert a s : Set α) :=
  Fintype.ofFinset s.toFinset <| by simp [h]
#align set.fintype_insert_of_mem Set.fintypeInsertOfMem
-/

#print Set.fintypeInsert' /-
/-- The `set.fintype_insert` instance requires decidable equality, but when `a ∈ s`
is decidable for this particular `a` we can still get a `fintype` instance by using
`set.fintype_insert_of_not_mem` or `set.fintype_insert_of_mem`.

This instance pre-dates `set.fintype_insert`, and it is less efficient.
When `decidable_mem_of_fintype` is made a local instance, then this instance would
override `set.fintype_insert` if not for the fact that its priority has been
adjusted. See Note [lower instance priority]. -/
instance (priority := 100) fintypeInsert' (a : α) (s : Set α) [Decidable <| a ∈ s] [Fintype s] :
    Fintype (insert a s : Set α) :=
  if h : a ∈ s then fintypeInsertOfMem s h else fintypeInsertOfNotMem s h
#align set.fintype_insert' Set.fintypeInsert'
-/

#print Set.fintypeImage /-
instance fintypeImage [DecidableEq β] (s : Set α) (f : α → β) [Fintype s] : Fintype (f '' s) :=
  Fintype.ofFinset (s.toFinset.image f) <| by simp
#align set.fintype_image Set.fintypeImage
-/

#print Set.fintypeOfFintypeImage /-
/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintypeOfFintypeImage (s : Set α) {f : α → β} {g} (I : IsPartialInv f g) [Fintype (f '' s)] :
    Fintype s :=
  Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g <| injective_of_isPartialInv_right I⟩
    fun a =>
    by
    suffices (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s by
      simpa [exists_and_distrib_left.symm, and_comm, and_left_comm, and_assoc]
    rw [exists_swap]
    suffices (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s by simpa [and_comm, and_left_comm, and_assoc]
    simp [I _, (injective_of_partial_inv I).eq_iff]
#align set.fintype_of_fintype_image Set.fintypeOfFintypeImage
-/

#print Set.fintypeRange /-
instance fintypeRange [DecidableEq α] (f : ι → α) [Fintype (PLift ι)] : Fintype (range f) :=
  Fintype.ofFinset (Finset.univ.image <| f ∘ PLift.down) <| by simp [equiv.plift.exists_congr_left]
#align set.fintype_range Set.fintypeRange
-/

#print Set.fintypeMap /-
instance fintypeMap {α β} [DecidableEq β] :
    ∀ (s : Set α) (f : α → β) [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage
#align set.fintype_map Set.fintypeMap
-/

#print Set.fintypeLtNat /-
instance fintypeLtNat (n : ℕ) : Fintype { i | i < n } :=
  Fintype.ofFinset (Finset.range n) <| by simp
#align set.fintype_lt_nat Set.fintypeLtNat
-/

#print Set.fintypeLeNat /-
instance fintypeLeNat (n : ℕ) : Fintype { i | i ≤ n } := by
  simpa [Nat.lt_succ_iff] using Set.fintypeLtNat (n + 1)
#align set.fintype_le_nat Set.fintypeLeNat
-/

#print Set.Nat.fintypeIio /-
/-- This is not an instance so that it does not conflict with the one
in src/order/locally_finite. -/
def Nat.fintypeIio (n : ℕ) : Fintype (Iio n) :=
  Set.fintypeLtNat n
#align set.nat.fintype_Iio Set.Nat.fintypeIio
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.fintypeProd /-
instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] :
    Fintype (s ×ˢ t : Set (α × β)) :=
  Fintype.ofFinset (s.toFinset ×ˢ t.toFinset) <| by simp
#align set.fintype_prod Set.fintypeProd
-/

#print Set.fintypeOffDiag /-
instance fintypeOffDiag [DecidableEq α] (s : Set α) [Fintype s] : Fintype s.offDiag :=
  Fintype.ofFinset s.toFinset.offDiag <| by simp
#align set.fintype_off_diag Set.fintypeOffDiag
-/

#print Set.fintypeImage2 /-
/-- `image2 f s t` is `fintype` if `s` and `t` are. -/
instance fintypeImage2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s]
    [ht : Fintype t] : Fintype (image2 f s t : Set γ) :=
  by
  rw [← image_prod]
  apply Set.fintypeImage
#align set.fintype_image2 Set.fintypeImage2
-/

#print Set.fintypeSeq /-
instance fintypeSeq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBUnionᵢ'
#align set.fintype_seq Set.fintypeSeq
-/

#print Set.fintypeSeq' /-
instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f]
    [Fintype s] : Fintype (f <*> s) :=
  Set.fintypeSeq f s
#align set.fintype_seq' Set.fintypeSeq'
-/

#print Set.fintypeMemFinset /-
instance fintypeMemFinset (s : Finset α) : Fintype { a | a ∈ s } :=
  Finset.fintypeCoeSort s
#align set.fintype_mem_finset Set.fintypeMemFinset
-/

end FintypeInstances

end Set

/-! ### Finset -/


namespace Finset

#print Finset.finite_toSet /-
/-- Gives a `set.finite` for the `finset` coerced to a `set`.
This is a wrapper around `set.to_finite`. -/
@[simp]
theorem finite_toSet (s : Finset α) : (s : Set α).Finite :=
  Set.toFinite _
#align finset.finite_to_set Finset.finite_toSet
-/

#print Finset.finite_toSet_toFinset /-
@[simp]
theorem finite_toSet_toFinset (s : Finset α) : s.finite_toSet.toFinset = s :=
  by
  ext
  rw [Set.Finite.mem_toFinset, mem_coe]
#align finset.finite_to_set_to_finset Finset.finite_toSet_toFinset
-/

end Finset

namespace Multiset

#print Multiset.finite_toSet /-
@[simp]
theorem finite_toSet (s : Multiset α) : { x | x ∈ s }.Finite := by
  classical simpa only [← Multiset.mem_toFinset] using s.to_finset.finite_to_set
#align multiset.finite_to_set Multiset.finite_toSet
-/

#print Multiset.finite_toSet_toFinset /-
@[simp]
theorem finite_toSet_toFinset [DecidableEq α] (s : Multiset α) :
    s.finite_toSet.toFinset = s.toFinset := by
  ext x
  simp
#align multiset.finite_to_set_to_finset Multiset.finite_toSet_toFinset
-/

end Multiset

#print List.finite_toSet /-
@[simp]
theorem List.finite_toSet (l : List α) : { x | x ∈ l }.Finite :=
  (show Multiset α from ⟦l⟧).finite_toSet
#align list.finite_to_set List.finite_toSet
-/

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `fintype` instances
in `data.set.finite`. While every `fintype` instance gives a `finite` instance, those
instances that depend on `fintype` or `decidable` instances need an additional `finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`subtype.finite` for subsets of a finite type.
-/


namespace Finite.Set

open Classical

example {s : Set α} [Finite α] : Finite s :=
  inferInstance

example : Finite (∅ : Set α) :=
  inferInstance

example (a : α) : Finite ({a} : Set α) :=
  inferInstance

/- warning: finite.set.finite_union -> Finite.Set.finite_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (Set.Elem.{u1} α s)] [_inst_2 : Finite.{succ u1} (Set.Elem.{u1} α t)], Finite.{succ u1} (Set.Elem.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finite.set.finite_union Finite.Set.finite_unionₓ'. -/
instance finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s ∪ t : Set α) :=
  by
  cases nonempty_fintype s
  cases nonempty_fintype t
  infer_instance
#align finite.set.finite_union Finite.Set.finite_union

#print Finite.Set.finite_sep /-
instance finite_sep (s : Set α) (p : α → Prop) [Finite s] : Finite ({ a ∈ s | p a } : Set α) :=
  by
  cases nonempty_fintype s
  infer_instance
#align finite.set.finite_sep Finite.Set.finite_sep
-/

#print Finite.Set.subset /-
protected theorem subset (s : Set α) {t : Set α} [Finite s] (h : t ⊆ s) : Finite t :=
  by
  rw [← sep_eq_of_subset h]
  infer_instance
#align finite.set.subset Finite.Set.subset
-/

/- warning: finite.set.finite_inter_of_right -> Finite.Set.finite_inter_of_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (Set.Elem.{u1} α t)], Finite.{succ u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finite.set.finite_inter_of_right Finite.Set.finite_inter_of_rightₓ'. -/
instance finite_inter_of_right (s t : Set α) [Finite t] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset t (inter_subset_right s t)
#align finite.set.finite_inter_of_right Finite.Set.finite_inter_of_right

/- warning: finite.set.finite_inter_of_left -> Finite.Set.finite_inter_of_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (Set.Elem.{u1} α s)], Finite.{succ u1} (Set.Elem.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finite.set.finite_inter_of_left Finite.Set.finite_inter_of_leftₓ'. -/
instance finite_inter_of_left (s t : Set α) [Finite s] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset s (inter_subset_left s t)
#align finite.set.finite_inter_of_left Finite.Set.finite_inter_of_left

/- warning: finite.set.finite_diff -> Finite.Set.finite_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)], Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) [_inst_1 : Finite.{succ u1} (Set.Elem.{u1} α s)], Finite.{succ u1} (Set.Elem.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align finite.set.finite_diff Finite.Set.finite_diffₓ'. -/
instance finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α) :=
  Finite.Set.subset s (diff_subset s t)
#align finite.set.finite_diff Finite.Set.finite_diff

#print Finite.Set.finite_range /-
instance finite_range (f : ι → α) [Finite ι] : Finite (range f) :=
  by
  haveI := Fintype.ofFinite (PLift ι)
  infer_instance
#align finite.set.finite_range Finite.Set.finite_range
-/

#print Finite.Set.finite_unionᵢ /-
instance finite_unionᵢ [Finite ι] (f : ι → Set α) [∀ i, Finite (f i)] : Finite (⋃ i, f i) :=
  by
  rw [Union_eq_range_psigma]
  apply Set.finite_range
#align finite.set.finite_Union Finite.Set.finite_unionᵢ
-/

#print Finite.Set.finite_unionₛ /-
instance finite_unionₛ {s : Set (Set α)} [Finite s] [H : ∀ t : s, Finite (t : Set α)] :
    Finite (⋃₀ s) := by
  rw [sUnion_eq_Union]
  exact @Finite.Set.finite_unionᵢ _ _ _ _ H
#align finite.set.finite_sUnion Finite.Set.finite_unionₛ
-/

/- warning: finite.set.finite_bUnion -> Finite.Set.finite_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} (s : Set.{u2} ι) [_inst_1 : Finite.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) s)] (t : ι -> (Set.{u1} α)), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (t i)))) -> (Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι (fun (x : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x s) => t x)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} (s : Set.{u1} ι) [_inst_1 : Finite.{succ u1} (Set.Elem.{u1} ι s)] (t : ι -> (Set.{u2} α)), (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Finite.{succ u2} (Set.Elem.{u2} α (t i)))) -> (Finite.{succ u2} (Set.Elem.{u2} α (Set.unionᵢ.{u2, succ u1} α ι (fun (x : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) => t x)))))
Case conversion may be inaccurate. Consider using '#align finite.set.finite_bUnion Finite.Set.finite_bunionᵢₓ'. -/
theorem finite_bunionᵢ {ι : Type _} (s : Set ι) [Finite s] (t : ι → Set α)
    (H : ∀ i ∈ s, Finite (t i)) : Finite (⋃ x ∈ s, t x) :=
  by
  rw [bUnion_eq_Union]
  haveI : ∀ i : s, Finite (t i) := fun i => H i i.property
  infer_instance
#align finite.set.finite_bUnion Finite.Set.finite_bunionᵢ

#print Finite.Set.finite_bunionᵢ' /-
instance finite_bunionᵢ' {ι : Type _} (s : Set ι) [Finite s] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋃ x ∈ s, t x) :=
  finite_bunionᵢ s t fun i h => inferInstance
#align finite.set.finite_bUnion' Finite.Set.finite_bunionᵢ'
-/

#print Finite.Set.finite_bunionᵢ'' /-
/-- Example: `finite (⋃ (i < n), f i)` where `f : ℕ → set α` and `[∀ i, finite (f i)]`
(when given instances from `data.nat.interval`).
-/
instance finite_bunionᵢ'' {ι : Type _} (p : ι → Prop) [h : Finite { x | p x }] (t : ι → Set α)
    [∀ i, Finite (t i)] : Finite (⋃ (x) (h : p x), t x) :=
  @Finite.Set.finite_bunionᵢ' _ _ (setOf p) h t _
#align finite.set.finite_bUnion'' Finite.Set.finite_bunionᵢ''
-/

#print Finite.Set.finite_interᵢ /-
instance finite_interᵢ {ι : Sort _} [Nonempty ι] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋂ i, t i) :=
  Finite.Set.subset (t <| Classical.arbitrary ι) (interᵢ_subset _ _)
#align finite.set.finite_Inter Finite.Set.finite_interᵢ
-/

#print Finite.Set.finite_insert /-
instance finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α) :=
  Finite.Set.finite_union {a} s
#align finite.set.finite_insert Finite.Set.finite_insert
-/

#print Finite.Set.finite_image /-
instance finite_image (s : Set α) (f : α → β) [Finite s] : Finite (f '' s) :=
  by
  cases nonempty_fintype s
  infer_instance
#align finite.set.finite_image Finite.Set.finite_image
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:369:4: unsupported set replacement {(f x) | x : α} -/
#print Finite.Set.finite_replacement /-
instance finite_replacement [Finite α] (f : α → β) :
    Finite
      "./././Mathport/Syntax/Translate/Expr.lean:369:4: unsupported set replacement {(f x) | x : α}" :=
  Finite.Set.finite_range f
#align finite.set.finite_replacement Finite.Set.finite_replacement
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finite.Set.finite_prod /-
instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (s ×ˢ t : Set (α × β)) :=
  Finite.of_equiv _ (Equiv.Set.prod s t).symm
#align finite.set.finite_prod Finite.Set.finite_prod
-/

#print Finite.Set.finite_image2 /-
instance finite_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Finite s] [Finite t] :
    Finite (image2 f s t : Set γ) := by
  rw [← image_prod]
  infer_instance
#align finite.set.finite_image2 Finite.Set.finite_image2
-/

#print Finite.Set.finite_seq /-
instance finite_seq (f : Set (α → β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) :=
  by
  rw [seq_def]
  infer_instance
#align finite.set.finite_seq Finite.Set.finite_seq
-/

end Finite.Set

namespace Set

/-! ### Constructors for `set.finite`

Every constructor here should have a corresponding `fintype` instance in the previous section
(or in the `fintype` module).

The implementation of these constructors ideally should be no more than `set.to_finite`,
after possibly setting up some `fintype` and classical `decidable` instances.
-/


section SetFiniteConstructors

#print Set.Finite.of_subsingleton /-
@[nontriviality]
theorem Finite.of_subsingleton [Subsingleton α] (s : Set α) : s.Finite :=
  s.toFinite
#align set.finite.of_subsingleton Set.Finite.of_subsingleton
-/

#print Set.finite_univ /-
theorem finite_univ [Finite α] : (@univ α).Finite :=
  Set.toFinite _
#align set.finite_univ Set.finite_univ
-/

#print Set.finite_univ_iff /-
theorem finite_univ_iff : (@univ α).Finite ↔ Finite α :=
  finite_coe_iff.symm.trans (Equiv.Set.univ α).finite_iff
#align set.finite_univ_iff Set.finite_univ_iff
-/

alias finite_univ_iff ↔ _root_.finite.of_finite_univ _
#align finite.of_finite_univ Finite.of_finite_univ

/- warning: set.finite.union -> Set.Finite.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Set.Finite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Set.Finite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.finite.union Set.Finite.unionₓ'. -/
theorem Finite.union {s t : Set α} (hs : s.Finite) (ht : t.Finite) : (s ∪ t).Finite :=
  by
  cases hs
  cases ht
  apply to_finite
#align set.finite.union Set.Finite.union

/- warning: set.finite.finite_of_compl -> Set.Finite.finite_of_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> (Finite.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) -> (Finite.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align set.finite.finite_of_compl Set.Finite.finite_of_complₓ'. -/
theorem Finite.finite_of_compl {s : Set α} (hs : s.Finite) (hsc : sᶜ.Finite) : Finite α :=
  by
  rw [← finite_univ_iff, ← union_compl_self s]
  exact hs.union hsc
#align set.finite.finite_of_compl Set.Finite.finite_of_compl

/- warning: set.finite.sup -> Set.Finite.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Set.Finite.{u1} α (HasSup.sup.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Set.Finite.{u1} α (HasSup.sup.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s t))
Case conversion may be inaccurate. Consider using '#align set.finite.sup Set.Finite.supₓ'. -/
theorem Finite.sup {s t : Set α} : s.Finite → t.Finite → (s ⊔ t).Finite :=
  Finite.union
#align set.finite.sup Set.Finite.sup

#print Set.Finite.sep /-
theorem Finite.sep {s : Set α} (hs : s.Finite) (p : α → Prop) : { a ∈ s | p a }.Finite :=
  by
  cases hs
  apply to_finite
#align set.finite.sep Set.Finite.sep
-/

/- warning: set.finite.inter_of_left -> Set.Finite.inter_of_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.finite.inter_of_left Set.Finite.inter_of_leftₓ'. -/
theorem Finite.inter_of_left {s : Set α} (hs : s.Finite) (t : Set α) : (s ∩ t).Finite :=
  by
  cases hs
  apply to_finite
#align set.finite.inter_of_left Set.Finite.inter_of_left

/- warning: set.finite.inter_of_right -> Set.Finite.inter_of_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s))
Case conversion may be inaccurate. Consider using '#align set.finite.inter_of_right Set.Finite.inter_of_rightₓ'. -/
theorem Finite.inter_of_right {s : Set α} (hs : s.Finite) (t : Set α) : (t ∩ s).Finite :=
  by
  cases hs
  apply to_finite
#align set.finite.inter_of_right Set.Finite.inter_of_right

/- warning: set.finite.inf_of_left -> Set.Finite.inf_of_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (HasInf.inf.{u1} (Set.{u1} α) (SemilatticeInf.toHasInf.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (HasInf.inf.{u1} (Set.{u1} α) (Lattice.toHasInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s t))
Case conversion may be inaccurate. Consider using '#align set.finite.inf_of_left Set.Finite.inf_of_leftₓ'. -/
theorem Finite.inf_of_left {s : Set α} (h : s.Finite) (t : Set α) : (s ⊓ t).Finite :=
  h.inter_of_left t
#align set.finite.inf_of_left Set.Finite.inf_of_left

/- warning: set.finite.inf_of_right -> Set.Finite.inf_of_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (HasInf.inf.{u1} (Set.{u1} α) (SemilatticeInf.toHasInf.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) t s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (HasInf.inf.{u1} (Set.{u1} α) (Lattice.toHasInf.{u1} (Set.{u1} α) (CompleteLattice.toLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) t s))
Case conversion may be inaccurate. Consider using '#align set.finite.inf_of_right Set.Finite.inf_of_rightₓ'. -/
theorem Finite.inf_of_right {s : Set α} (h : s.Finite) (t : Set α) : (t ⊓ s).Finite :=
  h.inter_of_right t
#align set.finite.inf_of_right Set.Finite.inf_of_right

#print Set.Finite.subset /-
theorem Finite.subset {s : Set α} (hs : s.Finite) {t : Set α} (ht : t ⊆ s) : t.Finite :=
  by
  cases hs
  haveI := Finite.Set.subset _ ht
  apply to_finite
#align set.finite.subset Set.Finite.subset
-/

/- warning: set.finite.diff -> Set.Finite.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall (t : Set.{u1} α), Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.finite.diff Set.Finite.diffₓ'. -/
theorem Finite.diff {s : Set α} (hs : s.Finite) (t : Set α) : (s \ t).Finite :=
  by
  cases hs
  apply to_finite
#align set.finite.diff Set.Finite.diff

/- warning: set.finite.of_diff -> Set.Finite.of_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) -> (Set.Finite.{u1} α t) -> (Set.Finite.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) -> (Set.Finite.{u1} α t) -> (Set.Finite.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.finite.of_diff Set.Finite.of_diffₓ'. -/
theorem Finite.of_diff {s t : Set α} (hd : (s \ t).Finite) (ht : t.Finite) : s.Finite :=
  (hd.union ht).Subset <| subset_diff_union _ _
#align set.finite.of_diff Set.Finite.of_diff

#print Set.finite_unionᵢ /-
theorem finite_unionᵢ [Finite ι] {f : ι → Set α} (H : ∀ i, (f i).Finite) : (⋃ i, f i).Finite :=
  by
  haveI := fun i => (H i).Fintype
  apply to_finite
#align set.finite_Union Set.finite_unionᵢ
-/

#print Set.Finite.unionₛ /-
theorem Finite.unionₛ {s : Set (Set α)} (hs : s.Finite) (H : ∀ t ∈ s, Set.Finite t) :
    (⋃₀ s).Finite := by
  cases hs
  haveI := fun i : s => (H i i.2).to_subtype
  apply to_finite
#align set.finite.sUnion Set.Finite.unionₛ
-/

/- warning: set.finite.bUnion -> Set.Finite.bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι}, (Set.Finite.{u2} ι s) -> (forall {t : ι -> (Set.{u1} α)}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Set.Finite.{u1} α (t i))) -> (Set.Finite.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => t i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : Set.{u1} ι}, (Set.Finite.{u1} ι s) -> (forall {t : ι -> (Set.{u2} α)}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Set.Finite.{u2} α (t i))) -> (Set.Finite.{u2} α (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => t i)))))
Case conversion may be inaccurate. Consider using '#align set.finite.bUnion Set.Finite.bunionᵢₓ'. -/
theorem Finite.bunionᵢ {ι} {s : Set ι} (hs : s.Finite) {t : ι → Set α}
    (ht : ∀ i ∈ s, (t i).Finite) : (⋃ i ∈ s, t i).Finite := by
  classical
    cases hs
    haveI := fintype_bUnion s t fun i hi => (ht i hi).Fintype
    apply to_finite
#align set.finite.bUnion Set.Finite.bunionᵢ

/- warning: set.finite.bUnion' -> Set.Finite.bunionᵢ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : Set.{u2} ι}, (Set.Finite.{u2} ι s) -> (forall {t : forall (i : ι), (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) -> (Set.{u1} α)}, (forall (i : ι) (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s), Set.Finite.{u1} α (t i H)) -> (Set.Finite.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i s) => t i H)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : Set.{u1} ι}, (Set.Finite.{u1} ι s) -> (forall {t : forall (i : ι), (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) -> (Set.{u2} α)}, (forall (i : ι) (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s), Set.Finite.{u2} α (t i H)) -> (Set.Finite.{u2} α (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s) => t i H)))))
Case conversion may be inaccurate. Consider using '#align set.finite.bUnion' Set.Finite.bunionᵢ'ₓ'. -/
/-- Dependent version of `finite.bUnion`. -/
theorem Finite.bunionᵢ' {ι} {s : Set ι} (hs : s.Finite) {t : ∀ i ∈ s, Set α}
    (ht : ∀ i ∈ s, (t i ‹_›).Finite) : (⋃ i ∈ s, t i ‹_›).Finite :=
  by
  cases hs
  rw [bUnion_eq_Union]
  apply finite_Union fun i : s => ht i.1 i.2
#align set.finite.bUnion' Set.Finite.bunionᵢ'

#print Set.Finite.interₛ /-
theorem Finite.interₛ {α : Type _} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Finite) :
    (⋂₀ s).Finite :=
  hf.Subset (interₛ_subset_of_mem ht)
#align set.finite.sInter Set.Finite.interₛ
-/

#print Set.Finite.bind /-
theorem Finite.bind {α β} {s : Set α} {f : α → Set β} (h : s.Finite) (hf : ∀ a ∈ s, (f a).Finite) :
    (s >>= f).Finite :=
  h.bunionᵢ hf
#align set.finite.bind Set.Finite.bind
-/

#print Set.finite_empty /-
@[simp]
theorem finite_empty : (∅ : Set α).Finite :=
  toFinite _
#align set.finite_empty Set.finite_empty
-/

#print Set.finite_singleton /-
@[simp]
theorem finite_singleton (a : α) : ({a} : Set α).Finite :=
  toFinite _
#align set.finite_singleton Set.finite_singleton
-/

#print Set.finite_pure /-
theorem finite_pure (a : α) : (pure a : Set α).Finite :=
  toFinite _
#align set.finite_pure Set.finite_pure
-/

#print Set.Finite.insert /-
@[simp]
theorem Finite.insert (a : α) {s : Set α} (hs : s.Finite) : (insert a s).Finite :=
  by
  cases hs
  apply to_finite
#align set.finite.insert Set.Finite.insert
-/

#print Set.Finite.image /-
theorem Finite.image {s : Set α} (f : α → β) (hs : s.Finite) : (f '' s).Finite :=
  by
  cases hs
  apply to_finite
#align set.finite.image Set.Finite.image
-/

#print Set.finite_range /-
theorem finite_range (f : ι → α) [Finite ι] : (range f).Finite :=
  toFinite _
#align set.finite_range Set.finite_range
-/

#print Set.Finite.dependent_image /-
theorem Finite.dependent_image {s : Set α} (hs : s.Finite) (F : ∀ i ∈ s, β) :
    { y : β | ∃ (x : _)(hx : x ∈ s), y = F x hx }.Finite :=
  by
  cases hs
  simpa [range, eq_comm] using finite_range fun x : s => F x x.2
#align set.finite.dependent_image Set.Finite.dependent_image
-/

#print Set.Finite.map /-
theorem Finite.map {α β} {s : Set α} : ∀ f : α → β, s.Finite → (f <$> s).Finite :=
  Finite.image
#align set.finite.map Set.Finite.map
-/

#print Set.Finite.of_finite_image /-
theorem Finite.of_finite_image {s : Set α} {f : α → β} (h : (f '' s).Finite) (hi : Set.InjOn f s) :
    s.Finite := by
  cases h
  exact
    ⟨Fintype.ofInjective (fun a => (⟨f a.1, mem_image_of_mem f a.2⟩ : f '' s)) fun a b eq =>
        Subtype.eq <| hi a.2 b.2 <| Subtype.ext_iff_val.1 Eq⟩
#align set.finite.of_finite_image Set.Finite.of_finite_image
-/

#print Set.finite_of_finite_preimage /-
theorem finite_of_finite_preimage {f : α → β} {s : Set β} (h : (f ⁻¹' s).Finite)
    (hs : s ⊆ range f) : s.Finite :=
  by
  rw [← image_preimage_eq_of_subset hs]
  exact finite.image f h
#align set.finite_of_finite_preimage Set.finite_of_finite_preimage
-/

#print Set.Finite.of_preimage /-
theorem Finite.of_preimage {f : α → β} {s : Set β} (h : (f ⁻¹' s).Finite) (hf : Surjective f) :
    s.Finite :=
  hf.image_preimage s ▸ h.image _
#align set.finite.of_preimage Set.Finite.of_preimage
-/

#print Set.Finite.preimage /-
theorem Finite.preimage {s : Set β} {f : α → β} (I : Set.InjOn f (f ⁻¹' s)) (h : s.Finite) :
    (f ⁻¹' s).Finite :=
  (h.Subset (image_preimage_subset f s)).of_finite_image I
#align set.finite.preimage Set.Finite.preimage
-/

#print Set.Finite.preimage_embedding /-
theorem Finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.Finite) : (f ⁻¹' s).Finite :=
  h.Preimage fun _ _ _ _ h' => f.Injective h'
#align set.finite.preimage_embedding Set.Finite.preimage_embedding
-/

#print Set.finite_lt_nat /-
theorem finite_lt_nat (n : ℕ) : Set.Finite { i | i < n } :=
  toFinite _
#align set.finite_lt_nat Set.finite_lt_nat
-/

#print Set.finite_le_nat /-
theorem finite_le_nat (n : ℕ) : Set.Finite { i | i ≤ n } :=
  toFinite _
#align set.finite_le_nat Set.finite_le_nat
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.Finite.prod /-
theorem Finite.prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    (s ×ˢ t : Set (α × β)).Finite := by
  cases hs
  cases ht
  apply to_finite
#align set.finite.prod Set.Finite.prod
-/

#print Set.Finite.offDiag /-
theorem Finite.offDiag {s : Set α} (hs : s.Finite) : s.offDiag.Finite := by
  classical
    cases hs
    apply Set.toFinite
#align set.finite.off_diag Set.Finite.offDiag
-/

#print Set.Finite.image2 /-
theorem Finite.image2 (f : α → β → γ) {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    (image2 f s t).Finite := by
  cases hs
  cases ht
  apply to_finite
#align set.finite.image2 Set.Finite.image2
-/

#print Set.Finite.seq /-
theorem Finite.seq {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f.seq s).Finite := by
  classical
    cases hf
    cases hs
    apply to_finite
#align set.finite.seq Set.Finite.seq
-/

#print Set.Finite.seq' /-
theorem Finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : f.Finite) (hs : s.Finite) :
    (f <*> s).Finite :=
  hf.seq hs
#align set.finite.seq' Set.Finite.seq'
-/

#print Set.finite_mem_finset /-
theorem finite_mem_finset (s : Finset α) : { a | a ∈ s }.Finite :=
  toFinite _
#align set.finite_mem_finset Set.finite_mem_finset
-/

#print Set.Subsingleton.finite /-
theorem Subsingleton.finite {s : Set α} (h : s.Subsingleton) : s.Finite :=
  h.inductionOn finite_empty finite_singleton
#align set.subsingleton.finite Set.Subsingleton.finite
-/

#print Set.finite_preimage_inl_and_inr /-
theorem finite_preimage_inl_and_inr {s : Set (Sum α β)} :
    (Sum.inl ⁻¹' s).Finite ∧ (Sum.inr ⁻¹' s).Finite ↔ s.Finite :=
  ⟨fun h => image_preimage_inl_union_image_preimage_inr s ▸ (h.1.image _).union (h.2.image _),
    fun h => ⟨h.Preimage (Sum.inl_injective.InjOn _), h.Preimage (Sum.inr_injective.InjOn _)⟩⟩
#align set.finite_preimage_inl_and_inr Set.finite_preimage_inl_and_inr
-/

#print Set.exists_finite_iff_finset /-
theorem exists_finite_iff_finset {p : Set α → Prop} :
    (∃ s : Set α, s.Finite ∧ p s) ↔ ∃ s : Finset α, p ↑s :=
  ⟨fun ⟨s, hs, hps⟩ => ⟨hs.toFinset, hs.coe_toFinset.symm ▸ hps⟩, fun ⟨s, hs⟩ =>
    ⟨s, s.finite_toSet, hs⟩⟩
#align set.exists_finite_iff_finset Set.exists_finite_iff_finset
-/

#print Set.Finite.finite_subsets /-
/-- There are finitely many subsets of a given finite set -/
theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : a.Finite) : { b | b ⊆ a }.Finite :=
  ⟨Fintype.ofFinset ((Finset.powerset h.toFinset).map Finset.coeEmb.1) fun s => by
      simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, finite.subset_to_finset, ←
        and_assoc] using h.subset⟩
#align set.finite.finite_subsets Set.Finite.finite_subsets
-/

/- warning: set.finite.pi -> Set.Finite.pi is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} [_inst_1 : Finite.{succ u1} δ] {κ : δ -> Type.{u2}} {t : forall (d : δ), Set.{u2} (κ d)}, (forall (d : δ), Set.Finite.{u2} (κ d) (t d)) -> (Set.Finite.{max u1 u2} (forall (i : δ), κ i) (Set.pi.{u1, u2} δ (fun (d : δ) => κ d) (Set.univ.{u1} δ) t))
but is expected to have type
  forall {δ : Type.{u2}} [_inst_1 : Finite.{succ u2} δ] {κ : δ -> Type.{u1}} {t : forall (d : δ), Set.{u1} (κ d)}, (forall (d : δ), Set.Finite.{u1} (κ d) (t d)) -> (Set.Finite.{max u2 u1} (forall (i : δ), κ i) (Set.pi.{u2, u1} δ (fun (d : δ) => κ d) (Set.univ.{u2} δ) t))
Case conversion may be inaccurate. Consider using '#align set.finite.pi Set.Finite.piₓ'. -/
/-- Finite product of finite sets is finite -/
theorem Finite.pi {δ : Type _} [Finite δ] {κ : δ → Type _} {t : ∀ d, Set (κ d)}
    (ht : ∀ d, (t d).Finite) : (pi univ t).Finite :=
  by
  cases nonempty_fintype δ
  lift t to ∀ d, Finset (κ d) using ht
  classical
    rw [← Fintype.coe_piFinset]
    apply Finset.finite_toSet
#align set.finite.pi Set.Finite.pi

#print Set.union_finset_finite_of_range_finite /-
/-- A finite union of finsets is finite. -/
theorem union_finset_finite_of_range_finite (f : α → Finset β) (h : (range f).Finite) :
    (⋃ a, (f a : Set β)).Finite := by
  rw [← bUnion_range]
  exact h.bUnion fun y hy => y.finite_toSet
#align set.union_finset_finite_of_range_finite Set.union_finset_finite_of_range_finite
-/

#print Set.finite_range_ite /-
theorem finite_range_ite {p : α → Prop} [DecidablePred p] {f g : α → β} (hf : (range f).Finite)
    (hg : (range g).Finite) : (range fun x => if p x then f x else g x).Finite :=
  (hf.union hg).Subset range_ite_subset
#align set.finite_range_ite Set.finite_range_ite
-/

#print Set.finite_range_const /-
theorem finite_range_const {c : β} : (range fun x : α => c).Finite :=
  (finite_singleton c).Subset range_const_subset
#align set.finite_range_const Set.finite_range_const
-/

end SetFiniteConstructors

/-! ### Properties -/


#print Set.Finite.inhabited /-
instance Finite.inhabited : Inhabited { s : Set α // s.Finite } :=
  ⟨⟨∅, finite_empty⟩⟩
#align set.finite.inhabited Set.Finite.inhabited
-/

/- warning: set.finite_union -> Set.finite_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Finite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (And (Set.Finite.{u1} α s) (Set.Finite.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Finite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (And (Set.Finite.{u1} α s) (Set.Finite.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.finite_union Set.finite_unionₓ'. -/
@[simp]
theorem finite_union {s t : Set α} : (s ∪ t).Finite ↔ s.Finite ∧ t.Finite :=
  ⟨fun h => ⟨h.Subset (subset_union_left _ _), h.Subset (subset_union_right _ _)⟩, fun ⟨hs, ht⟩ =>
    hs.union ht⟩
#align set.finite_union Set.finite_union

#print Set.finite_image_iff /-
theorem finite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) : (f '' s).Finite ↔ s.Finite :=
  ⟨fun h => h.of_finite_image hi, Finite.image _⟩
#align set.finite_image_iff Set.finite_image_iff
-/

#print Set.univ_finite_iff_nonempty_fintype /-
theorem univ_finite_iff_nonempty_fintype : (univ : Set α).Finite ↔ Nonempty (Fintype α) :=
  ⟨fun h => ⟨fintypeOfFiniteUniv h⟩, fun ⟨_i⟩ => finite_univ⟩
#align set.univ_finite_iff_nonempty_fintype Set.univ_finite_iff_nonempty_fintype
-/

#print Set.Finite.toFinset_singleton /-
@[simp]
theorem Finite.toFinset_singleton {a : α} (ha : ({a} : Set α).Finite := finite_singleton _) :
    ha.toFinset = {a} :=
  Finset.ext <| by simp
#align set.finite.to_finset_singleton Set.Finite.toFinset_singleton
-/

#print Set.Finite.toFinset_insert /-
@[simp]
theorem Finite.toFinset_insert [DecidableEq α] {s : Set α} {a : α} (hs : (insert a s).Finite) :
    hs.toFinset = insert a (hs.Subset <| subset_insert _ _).toFinset :=
  Finset.ext <| by simp
#align set.finite.to_finset_insert Set.Finite.toFinset_insert
-/

#print Set.Finite.toFinset_insert' /-
theorem Finite.toFinset_insert' [DecidableEq α] {a : α} {s : Set α} (hs : s.Finite) :
    (hs.insert a).toFinset = insert a hs.toFinset :=
  Finite.toFinset_insert _
#align set.finite.to_finset_insert' Set.Finite.toFinset_insert'
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.Finite.toFinset_prod /-
theorem Finite.toFinset_prod {s : Set α} {t : Set β} (hs : s.Finite) (ht : t.Finite) :
    hs.toFinset ×ˢ ht.toFinset = (hs.Prod ht).toFinset :=
  Finset.ext <| by simp
#align set.finite.to_finset_prod Set.Finite.toFinset_prod
-/

#print Set.Finite.toFinset_offDiag /-
theorem Finite.toFinset_offDiag {s : Set α} [DecidableEq α] (hs : s.Finite) :
    hs.offDiag.toFinset = hs.toFinset.offDiag :=
  Finset.ext <| by simp
#align set.finite.to_finset_off_diag Set.Finite.toFinset_offDiag
-/

#print Set.Finite.fin_embedding /-
theorem Finite.fin_embedding {s : Set α} (h : s.Finite) : ∃ (n : ℕ)(f : Fin n ↪ α), range f = s :=
  ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by simp⟩
#align set.finite.fin_embedding Set.Finite.fin_embedding
-/

#print Set.Finite.fin_param /-
theorem Finite.fin_param {s : Set α} (h : s.Finite) :
    ∃ (n : ℕ)(f : Fin n → α), Injective f ∧ range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.Injective, hf⟩
#align set.finite.fin_param Set.Finite.fin_param
-/

#print Set.finite_option /-
theorem finite_option {s : Set (Option α)} : s.Finite ↔ { x : α | some x ∈ s }.Finite :=
  ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.image some).insert none).Subset fun x =>
      Option.casesOn x (fun _ => Or.inl rfl) fun x hx => Or.inr <| mem_image_of_mem _ hx⟩
#align set.finite_option Set.finite_option
-/

#print Set.finite_image_fst_and_snd_iff /-
theorem finite_image_fst_and_snd_iff {s : Set (α × β)} :
    (Prod.fst '' s).Finite ∧ (Prod.snd '' s).Finite ↔ s.Finite :=
  ⟨fun h => (h.1.Prod h.2).Subset fun x h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩, fun h =>
    ⟨h.image _, h.image _⟩⟩
#align set.finite_image_fst_and_snd_iff Set.finite_image_fst_and_snd_iff
-/

/- warning: set.forall_finite_image_eval_iff -> Set.forall_finite_image_eval_iff is a dubious translation:
lean 3 declaration is
  forall {δ : Type.{u1}} [_inst_1 : Finite.{succ u1} δ] {κ : δ -> Type.{u2}} {s : Set.{max u1 u2} (forall (d : δ), κ d)}, Iff (forall (d : δ), Set.Finite.{u2} (κ d) (Set.image.{max u1 u2, u2} (forall (x : δ), κ x) (κ d) (Function.eval.{succ u1, succ u2} δ (fun (d : δ) => κ d) d) s)) (Set.Finite.{max u1 u2} (forall (d : δ), κ d) s)
but is expected to have type
  forall {δ : Type.{u2}} [_inst_1 : Finite.{succ u2} δ] {κ : δ -> Type.{u1}} {s : Set.{max u2 u1} (forall (d : δ), κ d)}, Iff (forall (d : δ), Set.Finite.{u1} (κ d) (Set.image.{max u2 u1, u1} (forall (x : δ), κ x) (κ d) (Function.eval.{succ u2, succ u1} δ (fun (d : δ) => κ d) d) s)) (Set.Finite.{max u2 u1} (forall (d : δ), κ d) s)
Case conversion may be inaccurate. Consider using '#align set.forall_finite_image_eval_iff Set.forall_finite_image_eval_iffₓ'. -/
theorem forall_finite_image_eval_iff {δ : Type _} [Finite δ] {κ : δ → Type _} {s : Set (∀ d, κ d)} :
    (∀ d, (eval d '' s).Finite) ↔ s.Finite :=
  ⟨fun h => (Finite.pi h).Subset <| subset_pi_eval_image _ _, fun h d => h.image _⟩
#align set.forall_finite_image_eval_iff Set.forall_finite_image_eval_iff

/- warning: set.finite_subset_Union -> Set.finite_subset_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (forall {ι : Type.{u2}} {t : ι -> (Set.{u1} α)}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => t i))) -> (Exists.{succ u2} (Set.{u2} ι) (fun (I : Set.{u2} ι) => And (Set.Finite.{u2} ι I) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) (fun (H : Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I) => t i)))))))
but is expected to have type
  forall {α : Type.{u2}} {s : Set.{u2} α}, (Set.Finite.{u2} α s) -> (forall {ι : Type.{u1}} {t : ι -> (Set.{u2} α)}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => t i))) -> (Exists.{succ u1} (Set.{u1} ι) (fun (I : Set.{u1} ι) => And (Set.Finite.{u1} ι I) (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) (fun (H : Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I) => t i)))))))
Case conversion may be inaccurate. Consider using '#align set.finite_subset_Union Set.finite_subset_unionᵢₓ'. -/
theorem finite_subset_unionᵢ {s : Set α} (hs : s.Finite) {ι} {t : ι → Set α} (h : s ⊆ ⋃ i, t i) :
    ∃ I : Set ι, I.Finite ∧ s ⊆ ⋃ i ∈ I, t i :=
  by
  cases hs
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i by simpa [subset_def] using h
  refine' ⟨range f, finite_range f, fun x hx => _⟩
  rw [bUnion_range, mem_Union]
  exact ⟨⟨x, hx⟩, hf _⟩
#align set.finite_subset_Union Set.finite_subset_unionᵢ

/- warning: set.eq_finite_Union_of_finite_subset_Union -> Set.eq_finite_unionᵢ_of_finite_subset_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : ι -> (Set.{u1} α)} {t : Set.{u1} α}, (Set.Finite.{u1} α t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => s i))) -> (Exists.{succ u2} (Set.{u2} ι) (fun (I : Set.{u2} ι) => And (Set.Finite.{u2} ι I) (Exists.{max (succ u2) (succ u1)} ((coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) -> (Set.{u1} α)) (fun (σ : (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) -> (Set.{u1} α)) => And (forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))), Set.Finite.{u1} α (σ i)) (And (forall (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (σ i) (s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) ι (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) ι (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) ι (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) ι (coeSubtype.{succ u2} ι (fun (x : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) x (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))))))) i))) (Eq.{succ u1} (Set.{u1} α) t (Set.unionᵢ.{u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) (fun (i : coeSort.{succ u2, succ (succ u2)} (Set.{u2} ι) Type.{u2} (Set.hasCoeToSort.{u2} ι) (setOf.{u2} ι (fun (i : ι) => Membership.Mem.{u2, u2} ι (Set.{u2} ι) (Set.hasMem.{u2} ι) i I))) => σ i))))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : ι -> (Set.{u2} α)} {t : Set.{u2} α}, (Set.Finite.{u2} α t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => s i))) -> (Exists.{succ u1} (Set.{u1} ι) (fun (I : Set.{u1} ι) => And (Set.Finite.{u1} ι I) (Exists.{max (succ u2) (succ u1)} ((Set.Elem.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))) -> (Set.{u2} α)) (fun (σ : (Set.Elem.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))) -> (Set.{u2} α)) => And (forall (i : Set.Elem.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))), Set.Finite.{u2} α (σ i)) (And (forall (i : Set.Elem.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (σ i) (s (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))) i))) (Eq.{succ u2} (Set.{u2} α) t (Set.unionᵢ.{u2, succ u1} α (Set.Elem.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))) (fun (i : Set.Elem.{u1} ι (setOf.{u1} ι (fun (i : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i I))) => σ i))))))))
Case conversion may be inaccurate. Consider using '#align set.eq_finite_Union_of_finite_subset_Union Set.eq_finite_unionᵢ_of_finite_subset_unionᵢₓ'. -/
theorem eq_finite_unionᵢ_of_finite_subset_unionᵢ {ι} {s : ι → Set α} {t : Set α} (tfin : t.Finite)
    (h : t ⊆ ⋃ i, s i) :
    ∃ I : Set ι,
      I.Finite ∧
        ∃ σ : { i | i ∈ I } → Set α, (∀ i, (σ i).Finite) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_unionᵢ tfin h
  ⟨I, Ifin, fun x => s x ∩ t, fun i => tfin.Subset (inter_subset_right _ _), fun i =>
    inter_subset_left _ _, by
    ext x
    rw [mem_Union]
    constructor
    · intro x_in
      rcases mem_Union.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      use i, hi, H, x_in
    · rintro ⟨i, hi, H⟩
      exact H⟩
#align set.eq_finite_Union_of_finite_subset_Union Set.eq_finite_unionᵢ_of_finite_subset_unionᵢ

#print Set.Finite.induction_on /-
@[elab_as_elim]
theorem Finite.induction_on {C : Set α → Prop} {s : Set α} (h : s.Finite) (H0 : C ∅)
    (H1 : ∀ {a s}, a ∉ s → Set.Finite s → C s → C (insert a s)) : C s :=
  by
  lift s to Finset α using h
  induction' s using Finset.cons_induction_on with a s ha hs
  · rwa [Finset.coe_empty]
  · rw [Finset.coe_cons]
    exact @H1 a s ha (Set.toFinite _) hs
#align set.finite.induction_on Set.Finite.induction_on
-/

#print Set.Finite.induction_on' /-
/-- Analogous to `finset.induction_on'`. -/
@[elab_as_elim]
theorem Finite.induction_on' {C : Set α → Prop} {S : Set α} (h : S.Finite) (H0 : C ∅)
    (H1 : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → C s → C (insert a s)) : C S :=
  by
  refine' @Set.Finite.induction_on α (fun s => s ⊆ S → C s) S h (fun _ => H0) _ subset.rfl
  intro a s has hsf hCs haS
  rw [insert_subset] at haS
  exact H1 haS.1 haS.2 has (hCs haS.2)
#align set.finite.induction_on' Set.Finite.induction_on'
-/

#print Set.Finite.dinduction_on /-
@[elab_as_elim]
theorem Finite.dinduction_on {C : ∀ s : Set α, s.Finite → Prop} {s : Set α} (h : s.Finite)
    (H0 : C ∅ finite_empty)
    (H1 : ∀ {a s}, a ∉ s → ∀ h : Set.Finite s, C s h → C (insert a s) (h.insert a)) : C s h :=
  have : ∀ h : s.Finite, C s h :=
    Finite.induction_on h (fun h => H0) fun a s has hs ih h => H1 has hs (ih _)
  this h
#align set.finite.dinduction_on Set.Finite.dinduction_on
-/

section

attribute [local instance] nat.fintype_Iio

#print Set.seq_of_forall_finite_exists /-
/-- If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
theorem seq_of_forall_finite_exists {γ : Type _} {P : γ → Set γ → Prop}
    (h : ∀ t : Set γ, t.Finite → ∃ c, P c t) : ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) :=
  ⟨fun n =>
    @Nat.strongRecOn' (fun _ => γ) n fun n ih =>
      Classical.choose <| h (range fun m : Iio n => ih m.1 m.2) (finite_range _),
    fun n => by
    classical
      refine' Nat.strongRecOn' n fun n ih => _
      rw [Nat.strongRecOn'_beta]
      convert Classical.choose_spec (h _ _)
      ext x
      constructor
      · rintro ⟨m, hmn, rfl⟩
        exact ⟨⟨m, hmn⟩, rfl⟩
      · rintro ⟨⟨m, hmn⟩, rfl⟩
        exact ⟨m, hmn, rfl⟩⟩
#align set.seq_of_forall_finite_exists Set.seq_of_forall_finite_exists
-/

end

/-! ### Cardinality -/


#print Set.empty_card /-
theorem empty_card : Fintype.card (∅ : Set α) = 0 :=
  rfl
#align set.empty_card Set.empty_card
-/

#print Set.empty_card' /-
@[simp]
theorem empty_card' {h : Fintype.{u} (∅ : Set α)} : @Fintype.card (∅ : Set α) h = 0 :=
  Eq.trans (by congr ) empty_card
#align set.empty_card' Set.empty_card'
-/

#print Set.card_fintypeInsertOfNotMem /-
theorem card_fintypeInsertOfNotMem {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintypeInsertOfNotMem s h) = Fintype.card s + 1 := by
  rw [fintype_insert_of_not_mem, Fintype.card_ofFinset] <;> simp [Finset.card, to_finset] <;> rfl
#align set.card_fintype_insert_of_not_mem Set.card_fintypeInsertOfNotMem
-/

#print Set.card_insert /-
@[simp]
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s)
    {d : Fintype.{u} (insert a s : Set α)} : @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintype_insert_of_not_mem s h] <;> congr
#align set.card_insert Set.card_insert
-/

#print Set.card_image_of_inj_on /-
theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) : Fintype.card (f '' s) = Fintype.card s :=
  haveI := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.to_finset.image f).card := Fintype.card_of_finset' _ (by simp)
    _ = s.to_finset.card :=
      Finset.card_image_of_injOn fun x hx y hy hxy =>
        H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun a => mem_to_finset).symm
    
#align set.card_image_of_inj_on Set.card_image_of_inj_on
-/

#print Set.card_image_of_injective /-
theorem card_image_of_injective (s : Set α) [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : Function.Injective f) : Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on fun _ _ _ _ h => H h
#align set.card_image_of_injective Set.card_image_of_injective
-/

#print Set.card_singleton /-
@[simp]
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  Fintype.card_ofSubsingleton _
#align set.card_singleton Set.card_singleton
-/

/- warning: set.card_lt_card -> Set.card_lt_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)] [_inst_2 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)], (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (LT.lt.{0} Nat Nat.hasLt (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) _inst_1) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} [_inst_1 : Fintype.{u1} (Set.Elem.{u1} α s)] [_inst_2 : Fintype.{u1} (Set.Elem.{u1} α t)], (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (LT.lt.{0} Nat instLTNat (Fintype.card.{u1} (Set.Elem.{u1} α s) _inst_1) (Fintype.card.{u1} (Set.Elem.{u1} α t) _inst_2))
Case conversion may be inaccurate. Consider using '#align set.card_lt_card Set.card_lt_cardₓ'. -/
theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) :
    Fintype.card s < Fintype.card t :=
  Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)
    fun hst => (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)
#align set.card_lt_card Set.card_lt_card

#print Set.card_le_of_subset /-
theorem card_le_of_subset {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t) :
    Fintype.card s ≤ Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
#align set.card_le_of_subset Set.card_le_of_subset
-/

#print Set.eq_of_subset_of_card_le /-
theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t)
    (hcard : Fintype.card t ≤ Fintype.card s) : s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard <| not_le_of_lt <| card_lt_card h
#align set.eq_of_subset_of_card_le Set.eq_of_subset_of_card_le
-/

#print Set.card_range_of_injective /-
theorem card_range_of_injective [Fintype α] {f : α → β} (hf : Injective f) [Fintype (range f)] :
    Fintype.card (range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equiv.ofInjective f hf
#align set.card_range_of_injective Set.card_range_of_injective
-/

#print Set.Finite.card_toFinset /-
theorem Finite.card_toFinset {s : Set α} [Fintype s] (h : s.Finite) :
    h.toFinset.card = Fintype.card s :=
  by
  rw [← Finset.card_attach, Finset.attach_eq_univ, ← Fintype.card]
  refine' Fintype.card_congr (Equiv.setCongr _)
  ext x
  show x ∈ h.to_finset ↔ x ∈ s
  simp
#align set.finite.card_to_finset Set.Finite.card_toFinset
-/

#print Set.card_ne_eq /-
theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    Fintype.card { x : α | x ≠ a } = Fintype.card α - 1 :=
  by
  haveI := Classical.decEq α
  rw [← to_finset_card, to_finset_set_of, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
#align set.card_ne_eq Set.card_ne_eq
-/

/-! ### Infinite sets -/


#print Set.infinite_univ_iff /-
theorem infinite_univ_iff : (@univ α).Infinite ↔ Infinite α := by
  rw [Set.Infinite, finite_univ_iff, not_finite_iff_infinite]
#align set.infinite_univ_iff Set.infinite_univ_iff
-/

#print Set.infinite_univ /-
theorem infinite_univ [h : Infinite α] : (@univ α).Infinite :=
  infinite_univ_iff.2 h
#align set.infinite_univ Set.infinite_univ
-/

#print Set.infinite_coe_iff /-
theorem infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite :=
  not_finite_iff_infinite.symm.trans finite_coe_iff.Not
#align set.infinite_coe_iff Set.infinite_coe_iff
-/

alias infinite_coe_iff ↔ _ infinite.to_subtype
#align set.infinite.to_subtype Set.Infinite.to_subtype

#print Set.Infinite.natEmbedding /-
/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def Infinite.natEmbedding (s : Set α) (h : s.Infinite) : ℕ ↪ s :=
  haveI := h.to_subtype
  Infinite.natEmbedding s
#align set.infinite.nat_embedding Set.Infinite.natEmbedding
-/

#print Set.Infinite.exists_subset_card_eq /-
theorem Infinite.exists_subset_card_eq {s : Set α} (hs : s.Infinite) (n : ℕ) :
    ∃ t : Finset α, ↑t ⊆ s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by simp⟩
#align set.infinite.exists_subset_card_eq Set.Infinite.exists_subset_card_eq
-/

#print Set.Infinite.nonempty /-
theorem Infinite.nonempty {s : Set α} (h : s.Infinite) : s.Nonempty :=
  let a := Infinite.natEmbedding s h 37
  ⟨a.1, a.2⟩
#align set.infinite.nonempty Set.Infinite.nonempty
-/

/- warning: set.infinite_of_finite_compl -> Set.infinite_of_finite_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> (Set.Infinite.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) -> (Set.Infinite.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.infinite_of_finite_compl Set.infinite_of_finite_complₓ'. -/
theorem infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Infinite := fun h =>
  Set.infinite_univ (by simpa using hs.union h)
#align set.infinite_of_finite_compl Set.infinite_of_finite_compl

/- warning: set.finite.infinite_compl -> Set.Finite.infinite_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Infinite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {s : Set.{u1} α}, (Set.Finite.{u1} α s) -> (Set.Infinite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.finite.infinite_compl Set.Finite.infinite_complₓ'. -/
theorem Finite.infinite_compl [Infinite α] {s : Set α} (hs : s.Finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ (by simpa using hs.union h)
#align set.finite.infinite_compl Set.Finite.infinite_compl

#print Set.Infinite.mono /-
protected theorem Infinite.mono {s t : Set α} (h : s ⊆ t) : s.Infinite → t.Infinite :=
  mt fun ht => ht.Subset h
#align set.infinite.mono Set.Infinite.mono
-/

/- warning: set.infinite.diff -> Set.Infinite.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Infinite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Set.Infinite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Infinite.{u1} α s) -> (Set.Finite.{u1} α t) -> (Set.Infinite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.infinite.diff Set.Infinite.diffₓ'. -/
theorem Infinite.diff {s t : Set α} (hs : s.Infinite) (ht : t.Finite) : (s \ t).Infinite := fun h =>
  hs <| h.of_diff ht
#align set.infinite.diff Set.Infinite.diff

/- warning: set.infinite_union -> Set.infinite_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Infinite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Or (Set.Infinite.{u1} α s) (Set.Infinite.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Infinite.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Or (Set.Infinite.{u1} α s) (Set.Infinite.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.infinite_union Set.infinite_unionₓ'. -/
@[simp]
theorem infinite_union {s t : Set α} : (s ∪ t).Infinite ↔ s.Infinite ∨ t.Infinite := by
  simp only [Set.Infinite, finite_union, not_and_or]
#align set.infinite_union Set.infinite_union

#print Set.infinite_of_infinite_image /-
theorem infinite_of_infinite_image (f : α → β) {s : Set α} (hs : (f '' s).Infinite) : s.Infinite :=
  mt (Finite.image f) hs
#align set.infinite_of_infinite_image Set.infinite_of_infinite_image
-/

#print Set.infinite_image_iff /-
theorem infinite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) :
    (f '' s).Infinite ↔ s.Infinite :=
  not_congr <| finite_image_iff hi
#align set.infinite_image_iff Set.infinite_image_iff
-/

#print Set.infinite_of_injOn_mapsTo /-
theorem infinite_of_injOn_mapsTo {s : Set α} {t : Set β} {f : α → β} (hi : InjOn f s)
    (hm : MapsTo f s t) (hs : s.Infinite) : t.Infinite :=
  ((infinite_image_iff hi).2 hs).mono (mapsTo'.mp hm)
#align set.infinite_of_inj_on_maps_to Set.infinite_of_injOn_mapsTo
-/

/- warning: set.infinite.exists_ne_map_eq_of_maps_to -> Set.Infinite.exists_ne_map_eq_of_mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.Infinite.{u1} α s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.Finite.{u2} β t) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => And (Ne.{succ u1} α x y) (Eq.{succ u2} β (f x) (f y)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.Infinite.{u1} α s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.Finite.{u2} β t) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (And (Ne.{succ u1} α x y) (Eq.{succ u2} β (f x) (f y)))))))
Case conversion may be inaccurate. Consider using '#align set.infinite.exists_ne_map_eq_of_maps_to Set.Infinite.exists_ne_map_eq_of_mapsToₓ'. -/
theorem Infinite.exists_ne_map_eq_of_mapsTo {s : Set α} {t : Set β} {f : α → β} (hs : s.Infinite)
    (hf : MapsTo f s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y :=
  by
  contrapose! ht
  exact infinite_of_inj_on_maps_to (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs
#align set.infinite.exists_ne_map_eq_of_maps_to Set.Infinite.exists_ne_map_eq_of_mapsTo

#print Set.infinite_range_of_injective /-
theorem infinite_range_of_injective [Infinite α] {f : α → β} (hi : Injective f) :
    (range f).Infinite :=
  by
  rw [← image_univ, infinite_image_iff (inj_on_of_injective hi _)]
  exact infinite_univ
#align set.infinite_range_of_injective Set.infinite_range_of_injective
-/

#print Set.infinite_of_injective_forall_mem /-
theorem infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α → β} (hi : Injective f)
    (hf : ∀ x : α, f x ∈ s) : s.Infinite :=
  by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf
#align set.infinite_of_injective_forall_mem Set.infinite_of_injective_forall_mem
-/

/- warning: set.infinite.exists_nat_lt -> Set.Infinite.exists_nat_lt is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Nat}, (Set.Infinite.{0} Nat s) -> (forall (n : Nat), Exists.{1} Nat (fun (m : Nat) => Exists.{0} (Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) m s) (fun (H : Membership.Mem.{0, 0} Nat (Set.{0} Nat) (Set.hasMem.{0} Nat) m s) => LT.lt.{0} Nat Nat.hasLt n m)))
but is expected to have type
  forall {s : Set.{0} Nat}, (Set.Infinite.{0} Nat s) -> (forall (n : Nat), Exists.{1} Nat (fun (m : Nat) => And (Membership.mem.{0, 0} Nat (Set.{0} Nat) (Set.instMembershipSet.{0} Nat) m s) (LT.lt.{0} Nat instLTNat n m)))
Case conversion may be inaccurate. Consider using '#align set.infinite.exists_nat_lt Set.Infinite.exists_nat_ltₓ'. -/
theorem Infinite.exists_nat_lt {s : Set ℕ} (hs : s.Infinite) (n : ℕ) : ∃ m ∈ s, n < m :=
  let ⟨m, hm⟩ := (hs.diffₓ <| Set.finite_le_nat n).Nonempty
  ⟨m, by simpa using hm⟩
#align set.infinite.exists_nat_lt Set.Infinite.exists_nat_lt

/- warning: set.infinite.exists_not_mem_finset -> Set.Infinite.exists_not_mem_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Infinite.{u1} α s) -> (forall (f : Finset.{u1} α), Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a f))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Infinite.{u1} α s) -> (forall (f : Finset.{u1} α), Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a f))))
Case conversion may be inaccurate. Consider using '#align set.infinite.exists_not_mem_finset Set.Infinite.exists_not_mem_finsetₓ'. -/
theorem Infinite.exists_not_mem_finset {s : Set α} (hs : s.Infinite) (f : Finset α) :
    ∃ a ∈ s, a ∉ f :=
  let ⟨a, has, haf⟩ := (hs.diffₓ (toFinite f)).Nonempty
  ⟨a, has, fun h => haf <| Finset.mem_coe.1 h⟩
#align set.infinite.exists_not_mem_finset Set.Infinite.exists_not_mem_finset

#print Set.not_injOn_infinite_finite_image /-
theorem not_injOn_infinite_finite_image {f : α → β} {s : Set α} (h_inf : s.Infinite)
    (h_fin : (f '' s).Finite) : ¬InjOn f s :=
  by
  haveI : Finite (f '' s) := finite_coe_iff.mpr h_fin
  haveI : Infinite s := infinite_coe_iff.mpr h_inf
  have :=
    not_injective_infinite_finite
      ((f '' s).codRestrict (s.restrict f) fun x => ⟨x, x.property, rfl⟩)
  contrapose! this
  rwa [injective_cod_restrict, ← inj_on_iff_injective]
#align set.not_inj_on_infinite_finite_image Set.not_injOn_infinite_finite_image
-/

/-! ### Order properties -/


#print Set.finite_isTop /-
theorem finite_isTop (α : Type _) [PartialOrder α] : { x : α | IsTop x }.Finite :=
  (subsingleton_isTop α).Finite
#align set.finite_is_top Set.finite_isTop
-/

#print Set.finite_isBot /-
theorem finite_isBot (α : Type _) [PartialOrder α] : { x : α | IsBot x }.Finite :=
  (subsingleton_isBot α).Finite
#align set.finite_is_bot Set.finite_isBot
-/

/- warning: set.infinite.exists_lt_map_eq_of_maps_to -> Set.Infinite.exists_lt_map_eq_of_mapsTo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.Infinite.{u1} α s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.Finite.{u2} β t) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x y) (Eq.{succ u2} β (f x) (f y)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u1} α] {s : Set.{u1} α} {t : Set.{u2} β} {f : α -> β}, (Set.Infinite.{u1} α s) -> (Set.MapsTo.{u1, u2} α β f s t) -> (Set.Finite.{u2} β t) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (And (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x y) (Eq.{succ u2} β (f x) (f y)))))))
Case conversion may be inaccurate. Consider using '#align set.infinite.exists_lt_map_eq_of_maps_to Set.Infinite.exists_lt_map_eq_of_mapsToₓ'. -/
theorem Infinite.exists_lt_map_eq_of_mapsTo [LinearOrder α] {s : Set α} {t : Set β} {f : α → β}
    (hs : s.Infinite) (hf : MapsTo f s t) (ht : t.Finite) : ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_mapsTo hf ht
  hxy.lt_or_lt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩
#align set.infinite.exists_lt_map_eq_of_maps_to Set.Infinite.exists_lt_map_eq_of_mapsTo

#print Set.Finite.exists_lt_map_eq_of_forall_mem /-
theorem Finite.exists_lt_map_eq_of_forall_mem [LinearOrder α] [Infinite α] {t : Set β} {f : α → β}
    (hf : ∀ a, f a ∈ t) (ht : t.Finite) : ∃ a b, a < b ∧ f a = f b :=
  by
  rw [← maps_univ_to] at hf
  obtain ⟨a, -, b, -, h⟩ := (@infinite_univ α _).exists_lt_map_eq_of_mapsTo hf ht
  exact ⟨a, b, h⟩
#align set.finite.exists_lt_map_eq_of_forall_mem Set.Finite.exists_lt_map_eq_of_forall_mem
-/

/- warning: set.exists_min_image -> Set.exists_min_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] (s : Set.{u1} α) (f : α -> β), (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] (s : Set.{u1} α) (f : α -> β), (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f a) (f b)))))
Case conversion may be inaccurate. Consider using '#align set.exists_min_image Set.exists_min_imageₓ'. -/
theorem exists_min_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, finite.mem_to_finset] using
      h1.to_finset.exists_min_image f ⟨x, h1.mem_to_finset.2 hx⟩
#align set.exists_min_image Set.exists_min_image

/- warning: set.exists_max_image -> Set.exists_max_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] (s : Set.{u1} α) (f : α -> β), (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => forall (b : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f b) (f a)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] (s : Set.{u1} α) (f : α -> β), (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (forall (b : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f b) (f a)))))
Case conversion may be inaccurate. Consider using '#align set.exists_max_image Set.exists_max_imageₓ'. -/
theorem exists_max_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) :
    s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, finite.mem_to_finset] using
      h1.to_finset.exists_max_image f ⟨x, h1.mem_to_finset.2 hx⟩
#align set.exists_max_image Set.exists_max_image

#print Set.exists_lower_bound_image /-
theorem exists_lower_bound_image [hα : Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f a ≤ f b :=
  by
  by_cases hs : Set.Nonempty s
  ·
    exact
      let ⟨x₀, H, hx₀⟩ := Set.exists_min_image s f h hs
      ⟨x₀, fun x hx => hx₀ x hx⟩
  · exact Nonempty.elim hα fun a => ⟨a, fun x hx => absurd (Set.nonempty_of_mem hx) hs⟩
#align set.exists_lower_bound_image Set.exists_lower_bound_image
-/

#print Set.exists_upper_bound_image /-
theorem exists_upper_bound_image [hα : Nonempty α] [LinearOrder β] (s : Set α) (f : α → β)
    (h : s.Finite) : ∃ a : α, ∀ b ∈ s, f b ≤ f a :=
  by
  by_cases hs : Set.Nonempty s
  ·
    exact
      let ⟨x₀, H, hx₀⟩ := Set.exists_max_image s f h hs
      ⟨x₀, fun x hx => hx₀ x hx⟩
  · exact Nonempty.elim hα fun a => ⟨a, fun x hx => absurd (Set.nonempty_of_mem hx) hs⟩
#align set.exists_upper_bound_image Set.exists_upper_bound_image
-/

/- warning: set.finite.supr_binfi_of_monotone -> Set.Finite.supᵢ_binfi_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1))] [_inst_4 : Order.Frame.{u3} α] {s : Set.{u1} ι}, (Set.Finite.{u1} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Monotone.{u2, u3} ι' α _inst_1 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4)))) (f i))) -> (Eq.{succ u3} α (supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => infᵢ.{u3, 0} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i j)))) (infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => infᵢ.{u3, 0} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => f i j))))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (fun (x._@.Mathlib.Data.Set.Finite._hyg.11729 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.11731 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1) x._@.Mathlib.Data.Set.Finite._hyg.11729 x._@.Mathlib.Data.Set.Finite._hyg.11731)] [_inst_4 : Order.Frame.{u1} α] {s : Set.{u3} ι}, (Set.Finite.{u3} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) -> (Monotone.{u2, u1} ι' α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)))) (f i))) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => f i j)))) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => f i j))))))
Case conversion may be inaccurate. Consider using '#align set.finite.supr_binfi_of_monotone Set.Finite.supᵢ_binfi_of_monotoneₓ'. -/
theorem Finite.supᵢ_binfi_of_monotone {ι ι' α : Type _} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : (⨆ j, ⨅ i ∈ s, f i j) = ⨅ i ∈ s, ⨆ j, f i j :=
  by
  revert hf
  refine' hs.induction_on _ _
  · intro hf
    simp [supᵢ_const]
  · intro a s has hs ihs hf
    rw [ball_insert_iff] at hf
    simp only [infᵢ_insert, ← ihs hf.2]
    exact supᵢ_inf_of_monotone hf.1 fun j₁ j₂ hj => infᵢ₂_mono fun i hi => hf.2 i hi hj
#align set.finite.supr_binfi_of_monotone Set.Finite.supᵢ_binfi_of_monotone

/- warning: set.finite.supr_binfi_of_antitone -> Set.Finite.supᵢ_binfi_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1)))] [_inst_4 : Order.Frame.{u3} α] {s : Set.{u1} ι}, (Set.Finite.{u1} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Antitone.{u2, u3} ι' α _inst_1 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4)))) (f i))) -> (Eq.{succ u3} α (supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => infᵢ.{u3, 0} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i j)))) (infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => infᵢ.{u3, 0} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => f i j))))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (fun (x._@.Mathlib.Data.Set.Finite._hyg.11951 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.11953 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1) x._@.Mathlib.Data.Set.Finite._hyg.11951 x._@.Mathlib.Data.Set.Finite._hyg.11953))] [_inst_4 : Order.Frame.{u1} α] {s : Set.{u3} ι}, (Set.Finite.{u3} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) -> (Antitone.{u2, u1} ι' α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)))) (f i))) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => f i j)))) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => infᵢ.{u1, 0} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => f i j))))))
Case conversion may be inaccurate. Consider using '#align set.finite.supr_binfi_of_antitone Set.Finite.supᵢ_binfi_of_antitoneₓ'. -/
theorem Finite.supᵢ_binfi_of_antitone {ι ι' α : Type _} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Frame α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : (⨆ j, ⨅ i ∈ s, f i j) = ⨅ i ∈ s, ⨆ j, f i j :=
  @Finite.supᵢ_binfi_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ hs _ fun i hi => (hf i hi).dual_left
#align set.finite.supr_binfi_of_antitone Set.Finite.supᵢ_binfi_of_antitone

/- warning: set.finite.infi_bsupr_of_monotone -> Set.Finite.infᵢ_bsupᵢ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1)))] [_inst_4 : Order.Coframe.{u3} α] {s : Set.{u1} ι}, (Set.Finite.{u1} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Monotone.{u2, u3} ι' α _inst_1 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4)))) (f i))) -> (Eq.{succ u3} α (infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => supᵢ.{u3, 0} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i j)))) (supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => supᵢ.{u3, 0} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => f i j))))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (fun (x._@.Mathlib.Data.Set.Finite._hyg.12131 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.12133 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1) x._@.Mathlib.Data.Set.Finite._hyg.12131 x._@.Mathlib.Data.Set.Finite._hyg.12133))] [_inst_4 : Order.Coframe.{u1} α] {s : Set.{u3} ι}, (Set.Finite.{u3} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) -> (Monotone.{u2, u1} ι' α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)))) (f i))) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => f i j)))) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => f i j))))))
Case conversion may be inaccurate. Consider using '#align set.finite.infi_bsupr_of_monotone Set.Finite.infᵢ_bsupᵢ_of_monotoneₓ'. -/
theorem Finite.infᵢ_bsupᵢ_of_monotone {ι ι' α : Type _} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Coframe α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Monotone (f i)) : (⨅ j, ⨆ i ∈ s, f i j) = ⨆ i ∈ s, ⨅ j, f i j :=
  hs.supᵢ_binfi_of_antitone fun i hi => (hf i hi).dual_right
#align set.finite.infi_bsupr_of_monotone Set.Finite.infᵢ_bsupᵢ_of_monotone

/- warning: set.finite.infi_bsupr_of_antitone -> Set.Finite.infᵢ_bsupᵢ_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1))] [_inst_4 : Order.Coframe.{u3} α] {s : Set.{u1} ι}, (Set.Finite.{u1} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Antitone.{u2, u3} ι' α _inst_1 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4)))) (f i))) -> (Eq.{succ u3} α (infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => supᵢ.{u3, 0} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i j)))) (supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι (fun (i : ι) => supᵢ.{u3, 0} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_4))) ι' (fun (j : ι') => f i j))))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Preorder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : IsDirected.{u2} ι' (fun (x._@.Mathlib.Data.Set.Finite._hyg.12303 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.12305 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_1) x._@.Mathlib.Data.Set.Finite._hyg.12303 x._@.Mathlib.Data.Set.Finite._hyg.12305)] [_inst_4 : Order.Coframe.{u1} α] {s : Set.{u3} ι}, (Set.Finite.{u3} ι s) -> (forall {f : ι -> ι' -> α}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) -> (Antitone.{u2, u1} ι' α _inst_1 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)))) (f i))) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => f i j)))) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι (fun (i : ι) => supᵢ.{u1, 0} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) (fun (H : Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_4)) ι' (fun (j : ι') => f i j))))))
Case conversion may be inaccurate. Consider using '#align set.finite.infi_bsupr_of_antitone Set.Finite.infᵢ_bsupᵢ_of_antitoneₓ'. -/
theorem Finite.infᵢ_bsupᵢ_of_antitone {ι ι' α : Type _} [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Coframe α] {s : Set ι} (hs : s.Finite) {f : ι → ι' → α}
    (hf : ∀ i ∈ s, Antitone (f i)) : (⨅ j, ⨆ i ∈ s, f i j) = ⨆ i ∈ s, ⨅ j, f i j :=
  hs.supᵢ_binfi_of_monotone fun i hi => (hf i hi).dual_right
#align set.finite.infi_bsupr_of_antitone Set.Finite.infᵢ_bsupᵢ_of_antitone

/- warning: supr_infi_of_monotone -> Set.supᵢ_infᵢ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2))] [_inst_5 : Order.Frame.{u3} α] {f : ι -> ι' -> α}, (forall (i : ι), Monotone.{u2, u3} ι' α _inst_2 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5)))) (f i)) -> (Eq.{succ u3} α (supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => f i j))) (infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => f i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (fun (x._@.Mathlib.Data.Set.Finite._hyg.12475 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.12477 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.12475 x._@.Mathlib.Data.Set.Finite._hyg.12477)] [_inst_5 : Order.Frame.{u1} α] {f : ι -> ι' -> α}, (forall (i : ι), Monotone.{u2, u1} ι' α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)))) (f i)) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => f i j))) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => f i j))))
Case conversion may be inaccurate. Consider using '#align supr_infi_of_monotone Set.supᵢ_infᵢ_of_monotoneₓ'. -/
theorem Set.supᵢ_infᵢ_of_monotone {ι ι' α : Type _} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    (⨆ j, ⨅ i, f i j) = ⨅ i, ⨆ j, f i j := by
  simpa only [infᵢ_univ] using finite_univ.supr_binfi_of_monotone fun i hi => hf i
#align supr_infi_of_monotone Set.supᵢ_infᵢ_of_monotone

/- warning: supr_infi_of_antitone -> Set.supᵢ_infᵢ_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2)))] [_inst_5 : Order.Frame.{u3} α] {f : ι -> ι' -> α}, (forall (i : ι), Antitone.{u2, u3} ι' α _inst_2 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5)))) (f i)) -> (Eq.{succ u3} α (supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => f i j))) (infᵢ.{u3, succ u1} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => supᵢ.{u3, succ u2} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Frame.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => f i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (fun (x._@.Mathlib.Data.Set.Finite._hyg.12612 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.12614 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.12612 x._@.Mathlib.Data.Set.Finite._hyg.12614))] [_inst_5 : Order.Frame.{u1} α] {f : ι -> ι' -> α}, (forall (i : ι), Antitone.{u2, u1} ι' α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)))) (f i)) -> (Eq.{succ u1} α (supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => f i j))) (infᵢ.{u1, succ u3} α (CompleteLattice.toInfSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => supᵢ.{u1, succ u2} α (CompleteLattice.toSupSet.{u1} α (Order.Frame.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => f i j))))
Case conversion may be inaccurate. Consider using '#align supr_infi_of_antitone Set.supᵢ_infᵢ_of_antitoneₓ'. -/
theorem Set.supᵢ_infᵢ_of_antitone {ι ι' α : Type _} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Frame α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    (⨆ j, ⨅ i, f i j) = ⨅ i, ⨆ j, f i j :=
  @Set.supᵢ_infᵢ_of_monotone ι ι'ᵒᵈ α _ _ _ _ _ _ fun i => (hf i).dual_left
#align supr_infi_of_antitone Set.supᵢ_infᵢ_of_antitone

/- warning: infi_supr_of_monotone -> Set.infᵢ_supᵢ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2)))] [_inst_5 : Order.Coframe.{u3} α] {f : ι -> ι' -> α}, (forall (i : ι), Monotone.{u2, u3} ι' α _inst_2 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5)))) (f i)) -> (Eq.{succ u3} α (infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => f i j))) (supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => f i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (fun (x._@.Mathlib.Data.Set.Finite._hyg.12750 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.12752 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.12750 x._@.Mathlib.Data.Set.Finite._hyg.12752))] [_inst_5 : Order.Coframe.{u1} α] {f : ι -> ι' -> α}, (forall (i : ι), Monotone.{u2, u1} ι' α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)))) (f i)) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => f i j))) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => f i j))))
Case conversion may be inaccurate. Consider using '#align infi_supr_of_monotone Set.infᵢ_supᵢ_of_monotoneₓ'. -/
theorem Set.infᵢ_supᵢ_of_monotone {ι ι' α : Type _} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (swap (· ≤ ·))] [Order.Coframe α] {f : ι → ι' → α} (hf : ∀ i, Monotone (f i)) :
    (⨅ j, ⨆ i, f i j) = ⨆ i, ⨅ j, f i j :=
  Set.supᵢ_infᵢ_of_antitone fun i => (hf i).dual_right
#align infi_supr_of_monotone Set.infᵢ_supᵢ_of_monotone

/- warning: infi_supr_of_antitone -> Set.infᵢ_supᵢ_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2))] [_inst_5 : Order.Coframe.{u3} α] {f : ι -> ι' -> α}, (forall (i : ι), Antitone.{u2, u3} ι' α _inst_2 (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5)))) (f i)) -> (Eq.{succ u3} α (infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => f i j))) (supᵢ.{u3, succ u1} α (CompleteSemilatticeSup.toHasSup.{u3} α (CompleteLattice.toCompleteSemilatticeSup.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι (fun (i : ι) => infᵢ.{u3, succ u2} α (CompleteSemilatticeInf.toHasInf.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α (Order.Coframe.toCompleteLattice.{u3} α _inst_5))) ι' (fun (j : ι') => f i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : Nonempty.{succ u2} ι'] [_inst_4 : IsDirected.{u2} ι' (fun (x._@.Mathlib.Data.Set.Finite._hyg.12882 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.12884 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.12882 x._@.Mathlib.Data.Set.Finite._hyg.12884)] [_inst_5 : Order.Coframe.{u1} α] {f : ι -> ι' -> α}, (forall (i : ι), Antitone.{u2, u1} ι' α _inst_2 (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)))) (f i)) -> (Eq.{succ u1} α (infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => f i j))) (supᵢ.{u1, succ u3} α (CompleteLattice.toSupSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι (fun (i : ι) => infᵢ.{u1, succ u2} α (CompleteLattice.toInfSet.{u1} α (Order.Coframe.toCompleteLattice.{u1} α _inst_5)) ι' (fun (j : ι') => f i j))))
Case conversion may be inaccurate. Consider using '#align infi_supr_of_antitone Set.infᵢ_supᵢ_of_antitoneₓ'. -/
theorem Set.infᵢ_supᵢ_of_antitone {ι ι' α : Type _} [Finite ι] [Preorder ι'] [Nonempty ι']
    [IsDirected ι' (· ≤ ·)] [Order.Coframe α] {f : ι → ι' → α} (hf : ∀ i, Antitone (f i)) :
    (⨅ j, ⨆ i, f i j) = ⨆ i, ⨅ j, f i j :=
  Set.supᵢ_infᵢ_of_monotone fun i => (hf i).dual_right
#align infi_supr_of_antitone Set.infᵢ_supᵢ_of_antitone

/- warning: set.Union_Inter_of_monotone -> Set.unionᵢ_interᵢ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2))] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u3} α)}, (forall (i : ι), Monotone.{u2, u3} ι' (Set.{u3} α) _inst_2 (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.completeBooleanAlgebra.{u3} α))))))) (s i)) -> (Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι' (fun (j : ι') => Set.interᵢ.{u3, succ u1} α ι (fun (i : ι) => s i j))) (Set.interᵢ.{u3, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u3, succ u2} α ι' (fun (j : ι') => s i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (fun (x._@.Mathlib.Data.Set.Finite._hyg.13011 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.13013 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.13011 x._@.Mathlib.Data.Set.Finite._hyg.13013)] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u1} α)}, (forall (i : ι), Monotone.{u2, u1} ι' (Set.{u1} α) _inst_2 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (s i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι' (fun (j : ι') => Set.interᵢ.{u1, succ u3} α ι (fun (i : ι) => s i j))) (Set.interᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, succ u2} α ι' (fun (j : ι') => s i j))))
Case conversion may be inaccurate. Consider using '#align set.Union_Inter_of_monotone Set.unionᵢ_interᵢ_of_monotoneₓ'. -/
/-- An increasing union distributes over finite intersection. -/
theorem unionᵢ_interᵢ_of_monotone {ι ι' α : Type _} [Finite ι] [Preorder ι'] [IsDirected ι' (· ≤ ·)]
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j :=
  Set.supᵢ_infᵢ_of_monotone hs
#align set.Union_Inter_of_monotone Set.unionᵢ_interᵢ_of_monotone

/- warning: set.Union_Inter_of_antitone -> Set.unionᵢ_interᵢ_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2)))] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u3} α)}, (forall (i : ι), Antitone.{u2, u3} ι' (Set.{u3} α) _inst_2 (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.completeBooleanAlgebra.{u3} α))))))) (s i)) -> (Eq.{succ u3} (Set.{u3} α) (Set.unionᵢ.{u3, succ u2} α ι' (fun (j : ι') => Set.interᵢ.{u3, succ u1} α ι (fun (i : ι) => s i j))) (Set.interᵢ.{u3, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u3, succ u2} α ι' (fun (j : ι') => s i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (fun (x._@.Mathlib.Data.Set.Finite._hyg.13133 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.13135 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.13133 x._@.Mathlib.Data.Set.Finite._hyg.13135))] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u1} α)}, (forall (i : ι), Antitone.{u2, u1} ι' (Set.{u1} α) _inst_2 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (s i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α ι' (fun (j : ι') => Set.interᵢ.{u1, succ u3} α ι (fun (i : ι) => s i j))) (Set.interᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, succ u2} α ι' (fun (j : ι') => s i j))))
Case conversion may be inaccurate. Consider using '#align set.Union_Inter_of_antitone Set.unionᵢ_interᵢ_of_antitoneₓ'. -/
/-- A decreasing union distributes over finite intersection. -/
theorem unionᵢ_interᵢ_of_antitone {ι ι' α : Type _} [Finite ι] [Preorder ι']
    [IsDirected ι' (swap (· ≤ ·))] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j :=
  Set.supᵢ_infᵢ_of_antitone hs
#align set.Union_Inter_of_antitone Set.unionᵢ_interᵢ_of_antitone

/- warning: set.Inter_Union_of_monotone -> Set.interᵢ_unionᵢ_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2)))] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u3} α)}, (forall (i : ι), Monotone.{u2, u3} ι' (Set.{u3} α) _inst_2 (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.completeBooleanAlgebra.{u3} α))))))) (s i)) -> (Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, succ u2} α ι' (fun (j : ι') => Set.unionᵢ.{u3, succ u1} α ι (fun (i : ι) => s i j))) (Set.unionᵢ.{u3, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u3, succ u2} α ι' (fun (j : ι') => s i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (Function.swap.{succ u2, succ u2, 1} ι' ι' (fun (ᾰ : ι') (ᾰ : ι') => Prop) (fun (x._@.Mathlib.Data.Set.Finite._hyg.13255 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.13257 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.13255 x._@.Mathlib.Data.Set.Finite._hyg.13257))] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u1} α)}, (forall (i : ι), Monotone.{u2, u1} ι' (Set.{u1} α) _inst_2 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (s i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α ι' (fun (j : ι') => Set.unionᵢ.{u1, succ u3} α ι (fun (i : ι) => s i j))) (Set.unionᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.interᵢ.{u1, succ u2} α ι' (fun (j : ι') => s i j))))
Case conversion may be inaccurate. Consider using '#align set.Inter_Union_of_monotone Set.interᵢ_unionᵢ_of_monotoneₓ'. -/
/-- An increasing intersection distributes over finite union. -/
theorem interᵢ_unionᵢ_of_monotone {ι ι' α : Type _} [Finite ι] [Preorder ι']
    [IsDirected ι' (swap (· ≤ ·))] [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Monotone (s i)) :
    (⋂ j : ι', ⋃ i : ι, s i j) = ⋃ i : ι, ⋂ j : ι', s i j :=
  Set.infᵢ_supᵢ_of_monotone hs
#align set.Inter_Union_of_monotone Set.interᵢ_unionᵢ_of_monotone

/- warning: set.Inter_Union_of_antitone -> Set.interᵢ_unionᵢ_of_antitone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {α : Type.{u3}} [_inst_1 : Finite.{succ u1} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2))] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u3} α)}, (forall (i : ι), Antitone.{u2, u3} ι' (Set.{u3} α) _inst_2 (PartialOrder.toPreorder.{u3} (Set.{u3} α) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} α) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.completeBooleanAlgebra.{u3} α))))))) (s i)) -> (Eq.{succ u3} (Set.{u3} α) (Set.interᵢ.{u3, succ u2} α ι' (fun (j : ι') => Set.unionᵢ.{u3, succ u1} α ι (fun (i : ι) => s i j))) (Set.unionᵢ.{u3, succ u1} α ι (fun (i : ι) => Set.interᵢ.{u3, succ u2} α ι' (fun (j : ι') => s i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} {α : Type.{u1}} [_inst_1 : Finite.{succ u3} ι] [_inst_2 : Preorder.{u2} ι'] [_inst_3 : IsDirected.{u2} ι' (fun (x._@.Mathlib.Data.Set.Finite._hyg.13374 : ι') (x._@.Mathlib.Data.Set.Finite._hyg.13376 : ι') => LE.le.{u2} ι' (Preorder.toLE.{u2} ι' _inst_2) x._@.Mathlib.Data.Set.Finite._hyg.13374 x._@.Mathlib.Data.Set.Finite._hyg.13376)] [_inst_4 : Nonempty.{succ u2} ι'] {s : ι -> ι' -> (Set.{u1} α)}, (forall (i : ι), Antitone.{u2, u1} ι' (Set.{u1} α) _inst_2 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (s i)) -> (Eq.{succ u1} (Set.{u1} α) (Set.interᵢ.{u1, succ u2} α ι' (fun (j : ι') => Set.unionᵢ.{u1, succ u3} α ι (fun (i : ι) => s i j))) (Set.unionᵢ.{u1, succ u3} α ι (fun (i : ι) => Set.interᵢ.{u1, succ u2} α ι' (fun (j : ι') => s i j))))
Case conversion may be inaccurate. Consider using '#align set.Inter_Union_of_antitone Set.interᵢ_unionᵢ_of_antitoneₓ'. -/
/-- A decreasing intersection distributes over finite union. -/
theorem interᵢ_unionᵢ_of_antitone {ι ι' α : Type _} [Finite ι] [Preorder ι'] [IsDirected ι' (· ≤ ·)]
    [Nonempty ι'] {s : ι → ι' → Set α} (hs : ∀ i, Antitone (s i)) :
    (⋂ j : ι', ⋃ i : ι, s i j) = ⋃ i : ι, ⋂ j : ι', s i j :=
  Set.infᵢ_supᵢ_of_antitone hs
#align set.Inter_Union_of_antitone Set.interᵢ_unionᵢ_of_antitone

/- warning: set.Union_pi_of_monotone -> Set.unionᵢ_pi_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} [_inst_1 : LinearOrder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] {α : ι -> Type.{u3}} {I : Set.{u1} ι} {s : forall (i : ι), ι' -> (Set.{u3} (α i))}, (Set.Finite.{u1} ι I) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i I) -> (Monotone.{u2, u3} ι' (Set.{u3} (α i)) (PartialOrder.toPreorder.{u2} ι' (SemilatticeInf.toPartialOrder.{u2} ι' (Lattice.toSemilatticeInf.{u2} ι' (LinearOrder.toLattice.{u2} ι' _inst_1)))) (PartialOrder.toPreorder.{u3} (Set.{u3} (α i)) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} (α i)) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} (α i)) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} (α i)) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} (α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} (α i)) (Set.completeBooleanAlgebra.{u3} (α i)))))))) (s i))) -> (Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : ι), α i)) (Set.unionᵢ.{max u1 u3, succ u2} (forall (i : ι), α i) ι' (fun (j : ι') => Set.pi.{u1, u3} ι (fun (i : ι) => α i) I (fun (i : ι) => s i j))) (Set.pi.{u1, u3} ι (fun (i : ι) => α i) I (fun (i : ι) => Set.unionᵢ.{u3, succ u2} (α i) ι' (fun (j : ι') => s i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : LinearOrder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] {α : ι -> Type.{u1}} {I : Set.{u3} ι} {s : forall (i : ι), ι' -> (Set.{u1} (α i))}, (Set.Finite.{u3} ι I) -> (forall (i : ι), (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i I) -> (Monotone.{u2, u1} ι' (Set.{u1} (α i)) (PartialOrder.toPreorder.{u2} ι' (SemilatticeInf.toPartialOrder.{u2} ι' (Lattice.toSemilatticeInf.{u2} ι' (DistribLattice.toLattice.{u2} ι' (instDistribLattice.{u2} ι' _inst_1))))) (PartialOrder.toPreorder.{u1} (Set.{u1} (α i)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (α i)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (α i)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (α i)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (α i)) (Set.instCompleteBooleanAlgebraSet.{u1} (α i)))))))) (s i))) -> (Eq.{max (succ u3) (succ u1)} (Set.{max u3 u1} (forall (i : ι), α i)) (Set.unionᵢ.{max u3 u1, succ u2} (forall (i : ι), α i) ι' (fun (j : ι') => Set.pi.{u3, u1} ι (fun (i : ι) => α i) I (fun (i : ι) => s i j))) (Set.pi.{u3, u1} ι (fun (i : ι) => α i) I (fun (i : ι) => Set.unionᵢ.{u1, succ u2} (α i) ι' (fun (j : ι') => s i j))))
Case conversion may be inaccurate. Consider using '#align set.Union_pi_of_monotone Set.unionᵢ_pi_of_monotoneₓ'. -/
theorem unionᵢ_pi_of_monotone {ι ι' : Type _} [LinearOrder ι'] [Nonempty ι'] {α : ι → Type _}
    {I : Set ι} {s : ∀ i, ι' → Set (α i)} (hI : I.Finite) (hs : ∀ i ∈ I, Monotone (s i)) :
    (⋃ j : ι', I.pi fun i => s i j) = I.pi fun i => ⋃ j, s i j :=
  by
  simp only [pi_def, bInter_eq_Inter, preimage_Union]
  haveI := hI.fintype
  exact Union_Inter_of_monotone fun i j₁ j₂ h => preimage_mono <| hs i i.2 h
#align set.Union_pi_of_monotone Set.unionᵢ_pi_of_monotone

/- warning: set.Union_univ_pi_of_monotone -> Set.unionᵢ_univ_pi_of_monotone is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} [_inst_1 : LinearOrder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : Finite.{succ u1} ι] {α : ι -> Type.{u3}} {s : forall (i : ι), ι' -> (Set.{u3} (α i))}, (forall (i : ι), Monotone.{u2, u3} ι' (Set.{u3} (α i)) (PartialOrder.toPreorder.{u2} ι' (SemilatticeInf.toPartialOrder.{u2} ι' (Lattice.toSemilatticeInf.{u2} ι' (LinearOrder.toLattice.{u2} ι' _inst_1)))) (PartialOrder.toPreorder.{u3} (Set.{u3} (α i)) (CompleteSemilatticeInf.toPartialOrder.{u3} (Set.{u3} (α i)) (CompleteLattice.toCompleteSemilatticeInf.{u3} (Set.{u3} (α i)) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} (α i)) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} (α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} (α i)) (Set.completeBooleanAlgebra.{u3} (α i)))))))) (s i)) -> (Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : ι), α i)) (Set.unionᵢ.{max u1 u3, succ u2} (forall (i : ι), α i) ι' (fun (j : ι') => Set.pi.{u1, u3} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => s i j))) (Set.pi.{u1, u3} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Set.unionᵢ.{u3, succ u2} (α i) ι' (fun (j : ι') => s i j))))
but is expected to have type
  forall {ι : Type.{u3}} {ι' : Type.{u2}} [_inst_1 : LinearOrder.{u2} ι'] [_inst_2 : Nonempty.{succ u2} ι'] [_inst_3 : Finite.{succ u3} ι] {α : ι -> Type.{u1}} {s : forall (i : ι), ι' -> (Set.{u1} (α i))}, (forall (i : ι), Monotone.{u2, u1} ι' (Set.{u1} (α i)) (PartialOrder.toPreorder.{u2} ι' (SemilatticeInf.toPartialOrder.{u2} ι' (Lattice.toSemilatticeInf.{u2} ι' (DistribLattice.toLattice.{u2} ι' (instDistribLattice.{u2} ι' _inst_1))))) (PartialOrder.toPreorder.{u1} (Set.{u1} (α i)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (α i)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (α i)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (α i)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (α i)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (α i)) (Set.instCompleteBooleanAlgebraSet.{u1} (α i)))))))) (s i)) -> (Eq.{max (succ u3) (succ u1)} (Set.{max u1 u3} (forall (i : ι), α i)) (Set.unionᵢ.{max u1 u3, succ u2} (forall (i : ι), α i) ι' (fun (j : ι') => Set.pi.{u3, u1} ι (fun (i : ι) => α i) (Set.univ.{u3} ι) (fun (i : ι) => s i j))) (Set.pi.{u3, u1} ι (fun (i : ι) => α i) (Set.univ.{u3} ι) (fun (i : ι) => Set.unionᵢ.{u1, succ u2} (α i) ι' (fun (j : ι') => s i j))))
Case conversion may be inaccurate. Consider using '#align set.Union_univ_pi_of_monotone Set.unionᵢ_univ_pi_of_monotoneₓ'. -/
theorem unionᵢ_univ_pi_of_monotone {ι ι' : Type _} [LinearOrder ι'] [Nonempty ι'] [Finite ι]
    {α : ι → Type _} {s : ∀ i, ι' → Set (α i)} (hs : ∀ i, Monotone (s i)) :
    (⋃ j : ι', pi univ fun i => s i j) = pi univ fun i => ⋃ j, s i j :=
  unionᵢ_pi_of_monotone finite_univ fun i _ => hs i
#align set.Union_univ_pi_of_monotone Set.unionᵢ_univ_pi_of_monotone

#print Set.finite_range_findGreatest /-
theorem finite_range_findGreatest {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    (range fun x => Nat.findGreatest (P x) b).Finite :=
  (finite_le_nat b).Subset <| range_subset_iff.2 fun x => Nat.findGreatest_le _
#align set.finite_range_find_greatest Set.finite_range_findGreatest
-/

/- warning: set.finite.exists_maximal_wrt -> Set.Finite.exists_maximal_wrt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] (f : α -> β) (s : Set.{u1} α), (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => forall (a' : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a' s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f a) (f a')) -> (Eq.{succ u2} β (f a) (f a')))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u2} β] (f : α -> β) (s : Set.{u1} α), (Set.Finite.{u1} α s) -> (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (forall (a' : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a' s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β _inst_1)) (f a) (f a')) -> (Eq.{succ u2} β (f a) (f a')))))
Case conversion may be inaccurate. Consider using '#align set.finite.exists_maximal_wrt Set.Finite.exists_maximal_wrtₓ'. -/
theorem Finite.exists_maximal_wrt [PartialOrder β] (f : α → β) (s : Set α) (h : Set.Finite s) :
    s.Nonempty → ∃ a ∈ s, ∀ a' ∈ s, f a ≤ f a' → f a = f a' :=
  by
  refine' h.induction_on _ _
  · exact fun h => absurd h not_nonempty_empty
  intro a s his _ ih _
  cases' s.eq_empty_or_nonempty with h h
  · use a
    simp [h]
  rcases ih h with ⟨b, hb, ih⟩
  by_cases f b ≤ f a
  · refine' ⟨a, Set.mem_insert _ _, fun c hc hac => le_antisymm hac _⟩
    rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
    · rfl
    · rwa [← ih c hcs (le_trans h hac)]
  · refine' ⟨b, Set.mem_insert_of_mem _ hb, fun c hc hbc => _⟩
    rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
    · exact (h hbc).elim
    · exact ih c hcs hbc
#align set.finite.exists_maximal_wrt Set.Finite.exists_maximal_wrt

section

variable [SemilatticeSup α] [Nonempty α] {s : Set α}

#print Set.Finite.bddAbove /-
/-- A finite set is bounded above.-/
protected theorem Finite.bddAbove (hs : s.Finite) : BddAbove s :=
  Finite.induction_on hs bddAbove_empty fun a s _ _ h => h.insert a
#align set.finite.bdd_above Set.Finite.bddAbove
-/

#print Set.Finite.bddAbove_bunionᵢ /-
/-- A finite union of sets which are all bounded above is still bounded above.-/
theorem Finite.bddAbove_bunionᵢ {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddAbove (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddAbove (S i) :=
  Finite.induction_on H (by simp only [bUnion_empty, bddAbove_empty, ball_empty_iff])
    fun a s ha _ hs => by simp only [bUnion_insert, ball_insert_iff, bddAbove_union, hs]
#align set.finite.bdd_above_bUnion Set.Finite.bddAbove_bunionᵢ
-/

#print Set.infinite_of_not_bddAbove /-
theorem infinite_of_not_bddAbove : ¬BddAbove s → s.Infinite :=
  mt Finite.bddAbove
#align set.infinite_of_not_bdd_above Set.infinite_of_not_bddAbove
-/

end

section

variable [SemilatticeInf α] [Nonempty α] {s : Set α}

#print Set.Finite.bddBelow /-
/-- A finite set is bounded below.-/
protected theorem Finite.bddBelow (hs : s.Finite) : BddBelow s :=
  @Finite.bddAbove αᵒᵈ _ _ _ hs
#align set.finite.bdd_below Set.Finite.bddBelow
-/

#print Set.Finite.bddBelow_bunionᵢ /-
/-- A finite union of sets which are all bounded below is still bounded below.-/
theorem Finite.bddBelow_bunionᵢ {I : Set β} {S : β → Set α} (H : I.Finite) :
    BddBelow (⋃ i ∈ I, S i) ↔ ∀ i ∈ I, BddBelow (S i) :=
  @Finite.bddAbove_bunionᵢ αᵒᵈ _ _ _ _ _ H
#align set.finite.bdd_below_bUnion Set.Finite.bddBelow_bunionᵢ
-/

#print Set.infinite_of_not_bddBelow /-
theorem infinite_of_not_bddBelow : ¬BddBelow s → s.Infinite :=
  by
  contrapose!
  rw [not_infinite]
  apply finite.bdd_below
#align set.infinite_of_not_bdd_below Set.infinite_of_not_bddBelow
-/

end

end Set

namespace Finset

#print Finset.bddAbove /-
/-- A finset is bounded above. -/
protected theorem bddAbove [SemilatticeSup α] [Nonempty α] (s : Finset α) : BddAbove (↑s : Set α) :=
  s.finite_toSet.BddAbove
#align finset.bdd_above Finset.bddAbove
-/

#print Finset.bddBelow /-
/-- A finset is bounded below. -/
protected theorem bddBelow [SemilatticeInf α] [Nonempty α] (s : Finset α) : BddBelow (↑s : Set α) :=
  s.finite_toSet.BddBelow
#align finset.bdd_below Finset.bddBelow
-/

end Finset

variable [LinearOrder α]

#print Finite.of_forall_not_lt_lt /-
/-- If a linear order does not contain any triple of elements `x < y < z`, then this type
is finite. -/
theorem Finite.of_forall_not_lt_lt (h : ∀ ⦃x y z : α⦄, x < y → y < z → False) : Finite α :=
  by
  nontriviality α
  rcases exists_pair_ne α with ⟨x, y, hne⟩
  refine' @Finite.of_fintype α ⟨{x, y}, fun z => _⟩
  simpa [hne] using eq_or_eq_or_eq_of_forall_not_lt_lt h z x y
#align finite.of_forall_not_lt_lt Finite.of_forall_not_lt_lt
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x y z «expr ∈ » s) -/
#print Set.finite_of_forall_not_lt_lt /-
/-- If a set `s` does not contain any triple of elements `x < y < z`, then `s` is finite. -/
theorem Set.finite_of_forall_not_lt_lt {s : Set α}
    (h : ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s) (z) (_ : z ∈ s), x < y → y < z → False) : Set.Finite s :=
  @Set.toFinite _ s <| Finite.of_forall_not_lt_lt <| by simpa only [SetCoe.forall'] using h
#align set.finite_of_forall_not_lt_lt Set.finite_of_forall_not_lt_lt
-/

/- warning: set.finite_diff_Union_Ioo -> Set.finite_diff_unionᵢ_Ioo is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Set.{u1} α), Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) x y))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Set.{u1} α), Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α α (fun (x : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) => Set.unionᵢ.{u1, succ u1} α α (fun (y : α) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (fun (H : Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) => Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) x y))))))
Case conversion may be inaccurate. Consider using '#align set.finite_diff_Union_Ioo Set.finite_diff_unionᵢ_Iooₓ'. -/
theorem Set.finite_diff_unionᵢ_Ioo (s : Set α) : (s \ ⋃ (x ∈ s) (y ∈ s), Ioo x y).Finite :=
  Set.finite_of_forall_not_lt_lt fun x hx y hy z hz hxy hyz =>
    hy.2 <| mem_unionᵢ₂_of_mem hx.1 <| mem_unionᵢ₂_of_mem hz.1 ⟨hxy, hyz⟩
#align set.finite_diff_Union_Ioo Set.finite_diff_unionᵢ_Ioo

/- warning: set.finite_diff_Union_Ioo' -> Set.finite_diff_unionᵢ_Ioo' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Set.{u1} α), Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (fun (x : Prod.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) => Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) (Prod.fst.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) (Prod.snd.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] (s : Set.{u1} α), Set.Finite.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Set.unionᵢ.{u1, succ u1} α (Prod.{u1, u1} (Set.Elem.{u1} α s) (Set.Elem.{u1} α s)) (fun (x : Prod.{u1, u1} (Set.Elem.{u1} α s) (Set.Elem.{u1} α s)) => Set.Ioo.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Prod.fst.{u1, u1} (Set.Elem.{u1} α s) (Set.Elem.{u1} α s) x)) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Prod.snd.{u1, u1} (Set.Elem.{u1} α s) (Set.Elem.{u1} α s) x)))))
Case conversion may be inaccurate. Consider using '#align set.finite_diff_Union_Ioo' Set.finite_diff_unionᵢ_Ioo'ₓ'. -/
theorem Set.finite_diff_unionᵢ_Ioo' (s : Set α) : (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite := by
  simpa only [Union, supᵢ_prod, supᵢ_subtype] using s.finite_diff_Union_Ioo
#align set.finite_diff_Union_Ioo' Set.finite_diff_unionᵢ_Ioo'

