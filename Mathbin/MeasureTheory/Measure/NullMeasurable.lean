/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.measure.null_measurable
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeDisjoint

/-!
# Null measurable sets and complete measures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

### Null measurable sets and functions

A set `s : set α` is called *null measurable* (`measure_theory.null_measurable_set`) if it satisfies
any of the following equivalent conditions:

* there exists a measurable set `t` such that `s =ᵐ[μ] t` (this is used as a definition);
* `measure_theory.to_measurable μ s =ᵐ[μ] s`;
* there exists a measurable subset `t ⊆ s` such that `t =ᵐ[μ] s` (in this case the latter equality
  means that `μ (s \ t) = 0`);
* `s` can be represented as a union of a measurable set and a set of measure zero;
* `s` can be represented as a difference of a measurable set and a set of measure zero.

Null measurable sets form a σ-algebra that is registered as a `measurable_space` instance on
`measure_theory.null_measurable_space α μ`. We also say that `f : α → β` is
`measure_theory.null_measurable` if the preimage of a measurable set is a null measurable set.
In other words, `f : α → β` is null measurable if it is measurable as a function
`measure_theory.null_measurable_space α μ → β`.

### Complete measures

We say that a measure `μ` is complete w.r.t. the `measurable_space α` σ-algebra (or the σ-algebra is
complete w.r.t measure `μ`) if every set of measure zero is measurable. In this case all null
measurable sets and functions are measurable.

For each measure `μ`, we define `measure_theory.measure.completion μ` to be the same measure
interpreted as a measure on `measure_theory.null_measurable_space α μ` and prove that this is a
complete measure.

## Implementation notes

We define `measure_theory.null_measurable_set` as `@measurable_set (null_measurable_space α μ) _` so
that theorems about `measurable_set`s like `measurable_set.union` can be applied to
`null_measurable_set`s. However, these lemmas output terms of the same form
`@measurable_set (null_measurable_space α μ) _ _`. While this is definitionally equal to the
expected output `null_measurable_set s μ`, it looks different and may be misleading. So we copy all
standard lemmas about measurable sets to the `measure_theory.null_measurable_set` namespace and fix
the output type.

## Tags

measurable, measure, null measurable, completion
-/


open Filter Set Encodable

variable {ι α β γ : Type _}

namespace MeasureTheory

#print MeasureTheory.NullMeasurableSpace /-
/-- A type tag for `α` with `measurable_set` given by `null_measurable_set`. -/
@[nolint unused_arguments]
def NullMeasurableSpace (α : Type _) [MeasurableSpace α]
    (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Type _ :=
  α
#align measure_theory.null_measurable_space MeasureTheory.NullMeasurableSpace
-/

section

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

instance [h : Inhabited α] : Inhabited (NullMeasurableSpace α μ) :=
  h

instance [h : Subsingleton α] : Subsingleton (NullMeasurableSpace α μ) :=
  h

instance : MeasurableSpace (NullMeasurableSpace α μ)
    where
  MeasurableSet' s := ∃ t, MeasurableSet t ∧ s =ᵐ[μ] t
  measurable_set_empty := ⟨∅, MeasurableSet.empty, ae_eq_refl _⟩
  measurable_set_compl := fun s ⟨t, htm, hts⟩ => ⟨tᶜ, htm.compl, hts.compl⟩
  measurable_set_iUnion s hs := by
    choose t htm hts using hs
    exact ⟨⋃ i, t i, MeasurableSet.iUnion htm, EventuallyEq.countable_iUnion hts⟩

#print MeasureTheory.NullMeasurableSet /-
/-- A set is called `null_measurable_set` if it can be approximated by a measurable set up to
a set of null measure. -/
def NullMeasurableSet [MeasurableSpace α] (s : Set α)
    (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  @MeasurableSet (NullMeasurableSpace α μ) _ s
#align measure_theory.null_measurable_set MeasureTheory.NullMeasurableSet
-/

#print MeasurableSet.nullMeasurableSet /-
@[simp]
theorem MeasurableSet.nullMeasurableSet (h : MeasurableSet s) : NullMeasurableSet s μ :=
  ⟨s, h, ae_eq_refl _⟩
#align measurable_set.null_measurable_set MeasurableSet.nullMeasurableSet
-/

#print MeasureTheory.nullMeasurableSet_empty /-
@[simp]
theorem nullMeasurableSet_empty : NullMeasurableSet ∅ μ :=
  MeasurableSet.empty
#align measure_theory.null_measurable_set_empty MeasureTheory.nullMeasurableSet_empty
-/

#print MeasureTheory.nullMeasurableSet_univ /-
@[simp]
theorem nullMeasurableSet_univ : NullMeasurableSet univ μ :=
  MeasurableSet.univ
#align measure_theory.null_measurable_set_univ MeasureTheory.nullMeasurableSet_univ
-/

namespace NullMeasurableSet

/- warning: measure_theory.null_measurable_set.of_null -> MeasureTheory.NullMeasurableSet.of_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.of_null MeasureTheory.NullMeasurableSet.of_nullₓ'. -/
theorem of_null (h : μ s = 0) : NullMeasurableSet s μ :=
  ⟨∅, MeasurableSet.empty, ae_eq_empty.2 h⟩
#align measure_theory.null_measurable_set.of_null MeasureTheory.NullMeasurableSet.of_null

/- warning: measure_theory.null_measurable_set.compl -> MeasureTheory.NullMeasurableSet.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.compl MeasureTheory.NullMeasurableSet.complₓ'. -/
theorem compl (h : NullMeasurableSet s μ) : NullMeasurableSet (sᶜ) μ :=
  h.compl
#align measure_theory.null_measurable_set.compl MeasureTheory.NullMeasurableSet.compl

/- warning: measure_theory.null_measurable_set.of_compl -> MeasureTheory.NullMeasurableSet.of_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.of_compl MeasureTheory.NullMeasurableSet.of_complₓ'. -/
theorem of_compl (h : NullMeasurableSet (sᶜ) μ) : NullMeasurableSet s μ :=
  h.ofCompl
#align measure_theory.null_measurable_set.of_compl MeasureTheory.NullMeasurableSet.of_compl

/- warning: measure_theory.null_measurable_set.compl_iff -> MeasureTheory.NullMeasurableSet.compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, Iff (MeasureTheory.NullMeasurableSet.{u1} α m0 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) μ) (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, Iff (MeasureTheory.NullMeasurableSet.{u1} α m0 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) μ) (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.compl_iff MeasureTheory.NullMeasurableSet.compl_iffₓ'. -/
@[simp]
theorem compl_iff : NullMeasurableSet (sᶜ) μ ↔ NullMeasurableSet s μ :=
  MeasurableSet.compl_iff
#align measure_theory.null_measurable_set.compl_iff MeasureTheory.NullMeasurableSet.compl_iff

#print MeasureTheory.NullMeasurableSet.of_subsingleton /-
@[nontriviality]
theorem of_subsingleton [Subsingleton α] : NullMeasurableSet s μ :=
  Subsingleton.measurableSet
#align measure_theory.null_measurable_set.of_subsingleton MeasureTheory.NullMeasurableSet.of_subsingleton
-/

#print MeasureTheory.NullMeasurableSet.congr /-
protected theorem congr (hs : NullMeasurableSet s μ) (h : s =ᵐ[μ] t) : NullMeasurableSet t μ :=
  let ⟨s', hm, hs'⟩ := hs
  ⟨s', hm, h.symm.trans hs'⟩
#align measure_theory.null_measurable_set.congr MeasureTheory.NullMeasurableSet.congr
-/

#print MeasureTheory.NullMeasurableSet.iUnion /-
protected theorem iUnion {ι : Sort _} [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) : NullMeasurableSet (⋃ i, s i) μ :=
  MeasurableSet.iUnion h
#align measure_theory.null_measurable_set.Union MeasureTheory.NullMeasurableSet.iUnion
-/

/- warning: measure_theory.null_measurable_set.bUnion_decode₂ -> MeasureTheory.NullMeasurableSet.biUnion_decode₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_1 : Encodable.{u1} ι] {{f : ι -> (Set.{u2} α)}}, (forall (i : ι), MeasureTheory.NullMeasurableSet.{u2} α m0 (f i) μ) -> (forall (n : Nat), MeasureTheory.NullMeasurableSet.{u2} α m0 (Set.iUnion.{u2, succ u1} α ι (fun (b : ι) => Set.iUnion.{u2, 0} α (Membership.Mem.{u1, u1} ι (Option.{u1} ι) (Option.hasMem.{u1} ι) b (Encodable.decode₂.{u1} ι _inst_1 n)) (fun (H : Membership.Mem.{u1, u1} ι (Option.{u1} ι) (Option.hasMem.{u1} ι) b (Encodable.decode₂.{u1} ι _inst_1 n)) => f b))) μ)
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_1 : Encodable.{u2} ι] {{f : ι -> (Set.{u1} α)}}, (forall (i : ι), MeasureTheory.NullMeasurableSet.{u1} α m0 (f i) μ) -> (forall (n : Nat), MeasureTheory.NullMeasurableSet.{u1} α m0 (Set.iUnion.{u1, succ u2} α ι (fun (b : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Option.{u2} ι) (Option.instMembershipOption.{u2} ι) b (Encodable.decode₂.{u2} ι _inst_1 n)) (fun (H : Membership.mem.{u2, u2} ι (Option.{u2} ι) (Option.instMembershipOption.{u2} ι) b (Encodable.decode₂.{u2} ι _inst_1 n)) => f b))) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.bUnion_decode₂ MeasureTheory.NullMeasurableSet.biUnion_decode₂ₓ'. -/
protected theorem biUnion_decode₂ [Encodable ι] ⦃f : ι → Set α⦄ (h : ∀ i, NullMeasurableSet (f i) μ)
    (n : ℕ) : NullMeasurableSet (⋃ b ∈ Encodable.decode₂ ι n, f b) μ :=
  MeasurableSet.biUnion_decode₂ h n
#align measure_theory.null_measurable_set.bUnion_decode₂ MeasureTheory.NullMeasurableSet.biUnion_decode₂

#print MeasureTheory.NullMeasurableSet.biUnion /-
protected theorem biUnion {f : ι → Set α} {s : Set ι} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  MeasurableSet.biUnion hs h
#align measure_theory.null_measurable_set.bUnion MeasureTheory.NullMeasurableSet.biUnion
-/

#print MeasureTheory.NullMeasurableSet.sUnion /-
protected theorem sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋃₀ s) μ := by rw [sUnion_eq_bUnion]; exact MeasurableSet.biUnion hs h
#align measure_theory.null_measurable_set.sUnion MeasureTheory.NullMeasurableSet.sUnion
-/

#print MeasureTheory.NullMeasurableSet.iInter /-
protected theorem iInter {ι : Sort _} [Countable ι] {f : ι → Set α}
    (h : ∀ i, NullMeasurableSet (f i) μ) : NullMeasurableSet (⋂ i, f i) μ :=
  MeasurableSet.iInter h
#align measure_theory.null_measurable_set.Inter MeasureTheory.NullMeasurableSet.iInter
-/

/- warning: measure_theory.null_measurable_set.bInter -> MeasureTheory.NullMeasurableSet.biInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : β -> (Set.{u1} α)} {s : Set.{u2} β}, (Set.Countable.{u2} β s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (f b) μ)) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Set.iInter.{u1, succ u2} α β (fun (b : β) => Set.iInter.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s) => f b))) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} {f : β -> (Set.{u2} α)} {s : Set.{u1} β}, (Set.Countable.{u1} β s) -> (forall (b : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b s) -> (MeasureTheory.NullMeasurableSet.{u2} α m0 (f b) μ)) -> (MeasureTheory.NullMeasurableSet.{u2} α m0 (Set.iInter.{u2, succ u1} α β (fun (b : β) => Set.iInter.{u2, 0} α (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b s) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b s) => f b))) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.bInter MeasureTheory.NullMeasurableSet.biInterₓ'. -/
protected theorem biInter {f : β → Set α} {s : Set β} (hs : s.Countable)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  MeasurableSet.biInter hs h
#align measure_theory.null_measurable_set.bInter MeasureTheory.NullMeasurableSet.biInter

#print MeasureTheory.NullMeasurableSet.sInter /-
protected theorem sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, NullMeasurableSet t μ) :
    NullMeasurableSet (⋂₀ s) μ :=
  MeasurableSet.sInter hs h
#align measure_theory.null_measurable_set.sInter MeasureTheory.NullMeasurableSet.sInter
-/

/- warning: measure_theory.null_measurable_set.union -> MeasureTheory.NullMeasurableSet.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.union MeasureTheory.NullMeasurableSet.unionₓ'. -/
@[simp]
protected theorem union (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∪ t) μ :=
  hs.union ht
#align measure_theory.null_measurable_set.union MeasureTheory.NullMeasurableSet.union

/- warning: measure_theory.null_measurable_set.union_null -> MeasureTheory.NullMeasurableSet.union_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ t) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) t) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.union_null MeasureTheory.NullMeasurableSet.union_nullₓ'. -/
protected theorem union_null (hs : NullMeasurableSet s μ) (ht : μ t = 0) :
    NullMeasurableSet (s ∪ t) μ :=
  hs.union (of_null ht)
#align measure_theory.null_measurable_set.union_null MeasureTheory.NullMeasurableSet.union_null

/- warning: measure_theory.null_measurable_set.inter -> MeasureTheory.NullMeasurableSet.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.inter MeasureTheory.NullMeasurableSet.interₓ'. -/
@[simp]
protected theorem inter (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s ∩ t) μ :=
  hs.inter ht
#align measure_theory.null_measurable_set.inter MeasureTheory.NullMeasurableSet.inter

/- warning: measure_theory.null_measurable_set.diff -> MeasureTheory.NullMeasurableSet.diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.diff MeasureTheory.NullMeasurableSet.diffₓ'. -/
@[simp]
protected theorem diff (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    NullMeasurableSet (s \ t) μ :=
  hs.diffₓ ht
#align measure_theory.null_measurable_set.diff MeasureTheory.NullMeasurableSet.diff

/- warning: measure_theory.null_measurable_set.disjointed -> MeasureTheory.NullMeasurableSet.disjointed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.NullMeasurableSet.{u1} α m0 (f i) μ) -> (forall (n : Nat), MeasureTheory.NullMeasurableSet.{u1} α m0 (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) f n) μ)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : Nat -> (Set.{u1} α)}, (forall (i : Nat), MeasureTheory.NullMeasurableSet.{u1} α m0 (f i) μ) -> (forall (n : Nat), MeasureTheory.NullMeasurableSet.{u1} α m0 (disjointed.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) f n) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.disjointed MeasureTheory.NullMeasurableSet.disjointedₓ'. -/
@[simp]
protected theorem disjointed {f : ℕ → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (n) :
    NullMeasurableSet (disjointed f n) μ :=
  MeasurableSet.disjointed h n
#align measure_theory.null_measurable_set.disjointed MeasureTheory.NullMeasurableSet.disjointed

#print MeasureTheory.NullMeasurableSet.const /-
@[simp]
protected theorem const (p : Prop) : NullMeasurableSet { a : α | p } μ :=
  MeasurableSet.const p
#align measure_theory.null_measurable_set.const MeasureTheory.NullMeasurableSet.const
-/

instance [MeasurableSingletonClass α] : MeasurableSingletonClass (NullMeasurableSpace α μ) :=
  ⟨fun x => (@measurableSet_singleton α _ _ x).NullMeasurableSet⟩

#print MeasureTheory.NullMeasurableSet.insert /-
protected theorem insert [MeasurableSingletonClass (NullMeasurableSpace α μ)]
    (hs : NullMeasurableSet s μ) (a : α) : NullMeasurableSet (insert a s) μ :=
  hs.insert a
#align measure_theory.null_measurable_set.insert MeasureTheory.NullMeasurableSet.insert
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊇ » s) -/
#print MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq /-
theorem exists_measurable_superset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ (t : _)(_ : t ⊇ s), MeasurableSet t ∧ t =ᵐ[μ] s :=
  by
  rcases h with ⟨t, htm, hst⟩
  refine' ⟨t ∪ to_measurable μ (s \ t), _, htm.union (measurable_set_to_measurable _ _), _⟩
  · exact diff_subset_iff.1 (subset_to_measurable _ _)
  · have : to_measurable μ (s \ t) =ᵐ[μ] (∅ : Set α) := by simp [ae_le_set.1 hst.le]
    simpa only [union_empty] using hst.symm.union this
#align measure_theory.null_measurable_set.exists_measurable_superset_ae_eq MeasureTheory.NullMeasurableSet.exists_measurable_superset_ae_eq
-/

#print MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq /-
theorem toMeasurable_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ s =ᵐ[μ] s :=
  by
  rw [to_measurable, dif_pos]
  exact h.exists_measurable_superset_ae_eq.some_spec.snd.2
#align measure_theory.null_measurable_set.to_measurable_ae_eq MeasureTheory.NullMeasurableSet.toMeasurable_ae_eq
-/

/- warning: measure_theory.null_measurable_set.compl_to_measurable_compl_ae_eq -> MeasureTheory.NullMeasurableSet.compl_toMeasurable_compl_ae_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m0 μ) (HasCompl.compl.{u1} (α -> Prop) (Pi.hasCompl.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.hasCompl)) (MeasureTheory.toMeasurable.{u1} α m0 μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) s)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m0 μ) (HasCompl.compl.{u1} (α -> Prop) (Pi.hasCompl.{u1, 0} α (fun (ᾰ : α) => Prop) (fun (i : α) => Prop.hasCompl)) (MeasureTheory.toMeasurable.{u1} α m0 μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) s)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable_set.compl_to_measurable_compl_ae_eq MeasureTheory.NullMeasurableSet.compl_toMeasurable_compl_ae_eqₓ'. -/
theorem compl_toMeasurable_compl_ae_eq (h : NullMeasurableSet s μ) : toMeasurable μ (sᶜ)ᶜ =ᵐ[μ] s :=
  by simpa only [compl_compl] using h.compl.to_measurable_ae_eq.compl
#align measure_theory.null_measurable_set.compl_to_measurable_compl_ae_eq MeasureTheory.NullMeasurableSet.compl_toMeasurable_compl_ae_eq

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq /-
theorem exists_measurable_subset_ae_eq (h : NullMeasurableSet s μ) :
    ∃ (t : _)(_ : t ⊆ s), MeasurableSet t ∧ t =ᵐ[μ] s :=
  ⟨toMeasurable μ (sᶜ)ᶜ, compl_subset_comm.2 <| subset_toMeasurable _ _,
    (measurableSet_toMeasurable _ _).compl, h.compl_toMeasurable_compl_ae_eq⟩
#align measure_theory.null_measurable_set.exists_measurable_subset_ae_eq MeasureTheory.NullMeasurableSet.exists_measurable_subset_ae_eq
-/

end NullMeasurableSet

/- warning: measure_theory.exists_subordinate_pairwise_disjoint -> MeasureTheory.exists_subordinate_pairwise_disjoint is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_1 : Countable.{succ u1} ι] {s : ι -> (Set.{u2} α)}, (forall (i : ι), MeasureTheory.NullMeasurableSet.{u2} α m0 (s i) μ) -> (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m0 μ) s)) -> (Exists.{max (succ u1) (succ u2)} (ι -> (Set.{u2} α)) (fun (t : ι -> (Set.{u2} α)) => And (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (t i) (s i)) (And (forall (i : ι), Filter.EventuallyEq.{u2, 0} α Prop (MeasureTheory.Measure.ae.{u2} α m0 μ) (s i) (t i)) (And (forall (i : ι), MeasurableSet.{u2} α m0 (t i)) (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α)))) t))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_1 : Countable.{succ u2} ι] {s : ι -> (Set.{u1} α)}, (forall (i : ι), MeasureTheory.NullMeasurableSet.{u1} α m0 (s i) μ) -> (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m0 μ) s)) -> (Exists.{max (succ u2) (succ u1)} (ι -> (Set.{u1} α)) (fun (t : ι -> (Set.{u1} α)) => And (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (t i) (s i)) (And (forall (i : ι), Filter.EventuallyEq.{u1, 0} α Prop (MeasureTheory.Measure.ae.{u1} α m0 μ) (s i) (t i)) (And (forall (i : ι), MeasurableSet.{u1} α m0 (t i)) (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (Disjoint.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) t))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.exists_subordinate_pairwise_disjoint MeasureTheory.exists_subordinate_pairwise_disjointₓ'. -/
/-- If `sᵢ` is a countable family of (null) measurable pairwise `μ`-a.e. disjoint sets, then there
exists a subordinate family `tᵢ ⊆ sᵢ` of measurable pairwise disjoint sets such that
`tᵢ =ᵐ[μ] sᵢ`. -/
theorem exists_subordinate_pairwise_disjoint [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) :
    ∃ t : ι → Set α,
      (∀ i, t i ⊆ s i) ∧
        (∀ i, s i =ᵐ[μ] t i) ∧ (∀ i, MeasurableSet (t i)) ∧ Pairwise (Disjoint on t) :=
  by
  choose t ht_sub htm ht_eq using fun i => (h i).exists_measurable_subset_ae_eq
  rcases exists_null_pairwise_disjoint_diff hd with ⟨u, hum, hu₀, hud⟩
  exact
    ⟨fun i => t i \ u i, fun i => (diff_subset _ _).trans (ht_sub _), fun i =>
      (ht_eq _).symm.trans (diff_null_ae_eq_self (hu₀ i)).symm, fun i => (htm i).diffₓ (hum i),
      hud.mono fun i j h =>
        h.mono (diff_subset_diff_left (ht_sub i)) (diff_subset_diff_left (ht_sub j))⟩
#align measure_theory.exists_subordinate_pairwise_disjoint MeasureTheory.exists_subordinate_pairwise_disjoint

/- warning: measure_theory.measure_Union -> MeasureTheory.measure_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_1 : Countable.{succ u1} ι] {f : ι -> (Set.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α)))) f)) -> (forall (i : ι), MeasurableSet.{u2} α m0 (f i)) -> (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} α m0) (fun (_x : MeasureTheory.Measure.{u2} α m0) => (Set.{u2} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} α m0) μ (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => f i))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} α m0) (fun (_x : MeasureTheory.Measure.{u2} α m0) => (Set.{u2} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} α m0) μ (f i))))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_1 : Countable.{succ u1} ι] {f : ι -> (Set.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (Disjoint.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) f)) -> (forall (i : ι), MeasurableSet.{u2} α m0 (f i)) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m0 μ) (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => f i))) (tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m0 μ) (f i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union MeasureTheory.measure_iUnionₓ'. -/
theorem measure_iUnion {m0 : MeasurableSpace α} {μ : Measure α} [Countable ι] {f : ι → Set α}
    (hn : Pairwise (Disjoint on f)) (h : ∀ i, MeasurableSet (f i)) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
  by
  rw [measure_eq_extend (MeasurableSet.iUnion h),
    extend_Union MeasurableSet.empty _ MeasurableSet.iUnion _ hn h]
  · simp [measure_eq_extend, h]
  · exact μ.empty
  · exact μ.m_Union
#align measure_theory.measure_Union MeasureTheory.measure_iUnion

/- warning: measure_theory.measure_Union₀ -> MeasureTheory.measure_iUnion₀ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_1 : Countable.{succ u1} ι] {f : ι -> (Set.{u2} α)}, (Pairwise.{u1} ι (Function.onFun.{succ u1, succ u2, 1} ι (Set.{u2} α) Prop (MeasureTheory.AEDisjoint.{u2} α m0 μ) f)) -> (forall (i : ι), MeasureTheory.NullMeasurableSet.{u2} α m0 (f i) μ) -> (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} α m0) (fun (_x : MeasureTheory.Measure.{u2} α m0) => (Set.{u2} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} α m0) μ (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => f i))) (tsum.{0, u1} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} α m0) (fun (_x : MeasureTheory.Measure.{u2} α m0) => (Set.{u2} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} α m0) μ (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_1 : Countable.{succ u2} ι] {f : ι -> (Set.{u1} α)}, (Pairwise.{u2} ι (Function.onFun.{succ u2, succ u1, 1} ι (Set.{u1} α) Prop (MeasureTheory.AEDisjoint.{u1} α m0 μ) f)) -> (forall (i : ι), MeasureTheory.NullMeasurableSet.{u1} α m0 (f i) μ) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => f i))) (tsum.{0, u2} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (f i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_Union₀ MeasureTheory.measure_iUnion₀ₓ'. -/
theorem measure_iUnion₀ [Countable ι] {f : ι → Set α} (hd : Pairwise (AEDisjoint μ on f))
    (h : ∀ i, NullMeasurableSet (f i) μ) : μ (⋃ i, f i) = ∑' i, μ (f i) :=
  by
  rcases exists_subordinate_pairwise_disjoint h hd with ⟨t, ht_sub, ht_eq, htm, htd⟩
  calc
    μ (⋃ i, f i) = μ (⋃ i, t i) := measure_congr (EventuallyEq.countable_iUnion ht_eq)
    _ = ∑' i, μ (t i) := (measure_Union htd htm)
    _ = ∑' i, μ (f i) := tsum_congr fun i => measure_congr (ht_eq _).symm
    
#align measure_theory.measure_Union₀ MeasureTheory.measure_iUnion₀

/- warning: measure_theory.measure_union₀_aux -> MeasureTheory.measure_union₀_aux is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.AEDisjoint.{u1} α m0 μ s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ t)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.AEDisjoint.{u1} α m0 μ s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union₀_aux MeasureTheory.measure_union₀_auxₓ'. -/
theorem measure_union₀_aux (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ)
    (hd : AEDisjoint μ s t) : μ (s ∪ t) = μ s + μ t :=
  by
  rw [union_eq_Union, measure_Union₀, tsum_fintype, Fintype.sum_bool, cond, cond]
  exacts[(pairwise_on_bool ae_disjoint.symmetric).2 hd, fun b => Bool.casesOn b ht hs]
#align measure_theory.measure_union₀_aux MeasureTheory.measure_union₀_aux

/- warning: measure_theory.measure_inter_add_diff₀ -> MeasureTheory.measure_inter_add_diff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {t : Set.{u1} α} (s : Set.{u1} α), (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {t : Set.{u1} α} (s : Set.{u1} α), (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_inter_add_diff₀ MeasureTheory.measure_inter_add_diff₀ₓ'. -/
/-- A null measurable set `t` is Carathéodory measurable: for any `s`, we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
theorem measure_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∩ t) + μ (s \ t) = μ s := by
  refine' le_antisymm _ _
  · rcases exists_measurable_superset μ s with ⟨s', hsub, hs'm, hs'⟩
    replace hs'm : null_measurable_set s' μ := hs'm.null_measurable_set
    calc
      μ (s ∩ t) + μ (s \ t) ≤ μ (s' ∩ t) + μ (s' \ t) :=
        add_le_add (measure_mono <| inter_subset_inter_left _ hsub)
          (measure_mono <| diff_subset_diff_left hsub)
      _ = μ (s' ∩ t ∪ s' \ t) :=
        (measure_union₀_aux (hs'm.inter ht) (hs'm.diff ht) <|
            (@disjoint_inf_sdiff _ s' t _).AEDisjoint).symm
      _ = μ s' := (congr_arg μ (inter_union_diff _ _))
      _ = μ s := hs'
      
  ·
    calc
      μ s = μ (s ∩ t ∪ s \ t) := by rw [inter_union_diff]
      _ ≤ μ (s ∩ t) + μ (s \ t) := measure_union_le _ _
      
#align measure_theory.measure_inter_add_diff₀ MeasureTheory.measure_inter_add_diff₀

/- warning: measure_theory.measure_union_add_inter₀ -> MeasureTheory.measure_union_add_inter₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {t : Set.{u1} α} (s : Set.{u1} α), (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ t)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {t : Set.{u1} α} (s : Set.{u1} α), (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_add_inter₀ MeasureTheory.measure_union_add_inter₀ₓ'. -/
theorem measure_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff₀ s ht, add_comm, ← add_assoc, add_right_comm]
#align measure_theory.measure_union_add_inter₀ MeasureTheory.measure_union_add_inter₀

/- warning: measure_theory.measure_union_add_inter₀' -> MeasureTheory.measure_union_add_inter₀' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (forall (t : Set.{u1} α), Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ t)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (forall (t : Set.{u1} α), Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union_add_inter₀' MeasureTheory.measure_union_add_inter₀'ₓ'. -/
theorem measure_union_add_inter₀' (hs : NullMeasurableSet s μ) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter₀ t hs, add_comm]
#align measure_theory.measure_union_add_inter₀' MeasureTheory.measure_union_add_inter₀'

/- warning: measure_theory.measure_union₀ -> MeasureTheory.measure_union₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.AEDisjoint.{u1} α m0 μ s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ t)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 t μ) -> (MeasureTheory.AEDisjoint.{u1} α m0 μ s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union₀ MeasureTheory.measure_union₀ₓ'. -/
theorem measure_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [← measure_union_add_inter₀ s ht, hd.eq, add_zero]
#align measure_theory.measure_union₀ MeasureTheory.measure_union₀

/- warning: measure_theory.measure_union₀' -> MeasureTheory.measure_union₀' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.AEDisjoint.{u1} α m0 μ s t) -> (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ t)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} {t : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (MeasureTheory.AEDisjoint.{u1} α m0 μ s t) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) t)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_union₀' MeasureTheory.measure_union₀'ₓ'. -/
theorem measure_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t) :
    μ (s ∪ t) = μ s + μ t := by rw [union_comm, measure_union₀ hs hd.symm, add_comm]
#align measure_theory.measure_union₀' MeasureTheory.measure_union₀'

/- warning: measure_theory.measure_add_measure_compl₀ -> MeasureTheory.measure_add_measure_compl₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Set.univ.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α}, (MeasureTheory.NullMeasurableSet.{u1} α m0 s μ) -> (Eq.{1} ENNReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (Set.univ.{u1} α)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_add_measure_compl₀ MeasureTheory.measure_add_measure_compl₀ₓ'. -/
theorem measure_add_measure_compl₀ {s : Set α} (hs : NullMeasurableSet s μ) :
    μ s + μ (sᶜ) = μ univ := by rw [← measure_union₀' hs ae_disjoint_compl_right, union_compl_self]
#align measure_theory.measure_add_measure_compl₀ MeasureTheory.measure_add_measure_compl₀

section MeasurableSingletonClass

variable [MeasurableSingletonClass (NullMeasurableSpace α μ)]

#print MeasureTheory.nullMeasurableSet_singleton /-
theorem nullMeasurableSet_singleton (x : α) : NullMeasurableSet {x} μ :=
  measurableSet_singleton x
#align measure_theory.null_measurable_set_singleton MeasureTheory.nullMeasurableSet_singleton
-/

#print MeasureTheory.nullMeasurableSet_insert /-
@[simp]
theorem nullMeasurableSet_insert {a : α} {s : Set α} :
    NullMeasurableSet (insert a s) μ ↔ NullMeasurableSet s μ :=
  measurableSet_insert
#align measure_theory.null_measurable_set_insert MeasureTheory.nullMeasurableSet_insert
-/

#print MeasureTheory.nullMeasurableSet_eq /-
theorem nullMeasurableSet_eq {a : α} : NullMeasurableSet { x | x = a } μ :=
  nullMeasurableSet_singleton a
#align measure_theory.null_measurable_set_eq MeasureTheory.nullMeasurableSet_eq
-/

#print Set.Finite.nullMeasurableSet /-
protected theorem Set.Finite.nullMeasurableSet (hs : s.Finite) : NullMeasurableSet s μ :=
  Finite.measurableSet hs
#align set.finite.null_measurable_set Set.Finite.nullMeasurableSet
-/

#print Finset.nullMeasurableSet /-
protected theorem Finset.nullMeasurableSet (s : Finset α) : NullMeasurableSet (↑s) μ :=
  Finset.measurableSet s
#align finset.null_measurable_set Finset.nullMeasurableSet
-/

end MeasurableSingletonClass

#print Set.Finite.nullMeasurableSet_biUnion /-
theorem Set.Finite.nullMeasurableSet_biUnion {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finite.measurableSet_biUnion hs h
#align set.finite.null_measurable_set_bUnion Set.Finite.nullMeasurableSet_biUnion
-/

#print Finset.nullMeasurableSet_biUnion /-
theorem Finset.nullMeasurableSet_biUnion {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋃ b ∈ s, f b) μ :=
  Finset.measurableSet_biUnion s h
#align finset.null_measurable_set_bUnion Finset.nullMeasurableSet_biUnion
-/

#print Set.Finite.nullMeasurableSet_sUnion /-
theorem Set.Finite.nullMeasurableSet_sUnion {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋃₀ s) μ :=
  Finite.measurableSet_sUnion hs h
#align set.finite.null_measurable_set_sUnion Set.Finite.nullMeasurableSet_sUnion
-/

#print Set.Finite.nullMeasurableSet_biInter /-
theorem Set.Finite.nullMeasurableSet_biInter {f : ι → Set α} {s : Set ι} (hs : s.Finite)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  Finite.measurableSet_biInter hs h
#align set.finite.null_measurable_set_bInter Set.Finite.nullMeasurableSet_biInter
-/

#print Finset.nullMeasurableSet_biInter /-
theorem Finset.nullMeasurableSet_biInter {f : ι → Set α} (s : Finset ι)
    (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) : NullMeasurableSet (⋂ b ∈ s, f b) μ :=
  s.finite_toSet.nullMeasurableSet_biInter h
#align finset.null_measurable_set_bInter Finset.nullMeasurableSet_biInter
-/

#print Set.Finite.nullMeasurableSet_sInter /-
theorem Set.Finite.nullMeasurableSet_sInter {s : Set (Set α)} (hs : s.Finite)
    (h : ∀ t ∈ s, NullMeasurableSet t μ) : NullMeasurableSet (⋂₀ s) μ :=
  NullMeasurableSet.sInter hs.Countable h
#align set.finite.null_measurable_set_sInter Set.Finite.nullMeasurableSet_sInter
-/

#print MeasureTheory.nullMeasurableSet_toMeasurable /-
theorem nullMeasurableSet_toMeasurable : NullMeasurableSet (toMeasurable μ s) μ :=
  (measurableSet_toMeasurable _ _).NullMeasurableSet
#align measure_theory.null_measurable_set_to_measurable MeasureTheory.nullMeasurableSet_toMeasurable
-/

end

section NullMeasurable

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β} {μ : Measure α}

#print MeasureTheory.NullMeasurable /-
/-- A function `f : α → β` is null measurable if the preimage of a measurable set is a null
measurable set. -/
def NullMeasurable (f : α → β) (μ : Measure α := by exact MeasureTheory.MeasureSpace.volume) :
    Prop :=
  ∀ ⦃s : Set β⦄, MeasurableSet s → NullMeasurableSet (f ⁻¹' s) μ
#align measure_theory.null_measurable MeasureTheory.NullMeasurable
-/

/- warning: measurable.null_measurable -> Measurable.nullMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α _inst_1}, (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (MeasureTheory.NullMeasurable.{u1, u2} α β _inst_1 _inst_2 f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_1}, (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (MeasureTheory.NullMeasurable.{u2, u1} α β _inst_1 _inst_2 f μ)
Case conversion may be inaccurate. Consider using '#align measurable.null_measurable Measurable.nullMeasurableₓ'. -/
protected theorem Measurable.nullMeasurable (h : Measurable f) : NullMeasurable f μ := fun s hs =>
  (h hs).NullMeasurableSet
#align measurable.null_measurable Measurable.nullMeasurable

/- warning: measure_theory.null_measurable.measurable' -> MeasureTheory.NullMeasurable.measurable' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α _inst_1}, (MeasureTheory.NullMeasurable.{u1, u2} α β _inst_1 _inst_2 f μ) -> (Measurable.{u1, u2} (MeasureTheory.NullMeasurableSpace.{u1} α _inst_1 μ) β (MeasureTheory.NullMeasurableSpace.instMeasurableSpace.{u1} α _inst_1 μ) _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_1}, (MeasureTheory.NullMeasurable.{u2, u1} α β _inst_1 _inst_2 f μ) -> (Measurable.{u2, u1} (MeasureTheory.NullMeasurableSpace.{u2} α _inst_1 μ) β (MeasureTheory.NullMeasurableSpace.instMeasurableSpace.{u2} α _inst_1 μ) _inst_2 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable.measurable' MeasureTheory.NullMeasurable.measurable'ₓ'. -/
protected theorem NullMeasurable.measurable' (h : NullMeasurable f μ) :
    @Measurable (NullMeasurableSpace α μ) β _ _ f :=
  h
#align measure_theory.null_measurable.measurable' MeasureTheory.NullMeasurable.measurable'

/- warning: measure_theory.measurable.comp_null_measurable -> MeasureTheory.Measurable.comp_nullMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : MeasurableSpace.{u3} γ] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α _inst_1} {g : β -> γ}, (Measurable.{u2, u3} β γ _inst_2 _inst_3 g) -> (MeasureTheory.NullMeasurable.{u1, u2} α β _inst_1 _inst_2 f μ) -> (MeasureTheory.NullMeasurable.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u3} β] [_inst_3 : MeasurableSpace.{u2} γ] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α _inst_1} {g : β -> γ}, (Measurable.{u3, u2} β γ _inst_2 _inst_3 g) -> (MeasureTheory.NullMeasurable.{u1, u3} α β _inst_1 _inst_2 f μ) -> (MeasureTheory.NullMeasurable.{u1, u2} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.measurable.comp_null_measurable MeasureTheory.Measurable.comp_nullMeasurableₓ'. -/
theorem Measurable.comp_nullMeasurable {g : β → γ} (hg : Measurable g) (hf : NullMeasurable f μ) :
    NullMeasurable (g ∘ f) μ :=
  hg.comp hf
#align measure_theory.measurable.comp_null_measurable MeasureTheory.Measurable.comp_nullMeasurable

/- warning: measure_theory.null_measurable.congr -> MeasureTheory.NullMeasurable.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α _inst_1} {g : α -> β}, (MeasureTheory.NullMeasurable.{u1, u2} α β _inst_1 _inst_2 f μ) -> (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g) -> (MeasureTheory.NullMeasurable.{u1, u2} α β _inst_1 _inst_2 g μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_1} {g : α -> β}, (MeasureTheory.NullMeasurable.{u2, u1} α β _inst_1 _inst_2 f μ) -> (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f g) -> (MeasureTheory.NullMeasurable.{u2, u1} α β _inst_1 _inst_2 g μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable.congr MeasureTheory.NullMeasurable.congrₓ'. -/
theorem NullMeasurable.congr {g : α → β} (hf : NullMeasurable f μ) (hg : f =ᵐ[μ] g) :
    NullMeasurable g μ := fun s hs =>
  (hf hs).congr <| eventuallyEq_set.2 <| hg.mono fun x hx => by rw [mem_preimage, mem_preimage, hx]
#align measure_theory.null_measurable.congr MeasureTheory.NullMeasurable.congr

end NullMeasurable

section IsComplete

#print MeasureTheory.Measure.IsComplete /-
/-- A measure is complete if every null set is also measurable.
  A null set is a subset of a measurable set with measure `0`.
  Since every measure is defined as a special case of an outer measure, we can more simply state
  that a set `s` is null if `μ s = 0`. -/
class Measure.IsComplete {_ : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : ∀ s, μ s = 0 → MeasurableSet s
#align measure_theory.measure.is_complete MeasureTheory.Measure.IsComplete
-/

variable {m0 : MeasurableSpace α} {μ : Measure α} {s t : Set α}

/- warning: measure_theory.measure.is_complete_iff -> MeasureTheory.Measure.isComplete_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0}, Iff (MeasureTheory.Measure.IsComplete.{u1} α m0 μ) (forall (s : Set.{u1} α), (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasurableSet.{u1} α m0 s))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0}, Iff (MeasureTheory.Measure.IsComplete.{u1} α m0 μ) (forall (s : Set.{u1} α), (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasurableSet.{u1} α m0 s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.is_complete_iff MeasureTheory.Measure.isComplete_iffₓ'. -/
theorem Measure.isComplete_iff : μ.IsComplete ↔ ∀ s, μ s = 0 → MeasurableSet s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align measure_theory.measure.is_complete_iff MeasureTheory.Measure.isComplete_iff

/- warning: measure_theory.measure.is_complete.out -> MeasureTheory.Measure.IsComplete.out is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0}, (MeasureTheory.Measure.IsComplete.{u1} α m0 μ) -> (forall (s : Set.{u1} α), (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasurableSet.{u1} α m0 s))
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0}, (MeasureTheory.Measure.IsComplete.{u1} α m0 μ) -> (forall (s : Set.{u1} α), (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasurableSet.{u1} α m0 s))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.is_complete.out MeasureTheory.Measure.IsComplete.outₓ'. -/
theorem Measure.IsComplete.out (h : μ.IsComplete) : ∀ s, μ s = 0 → MeasurableSet s :=
  h.1
#align measure_theory.measure.is_complete.out MeasureTheory.Measure.IsComplete.out

/- warning: measure_theory.measurable_set_of_null -> MeasureTheory.measurableSet_of_null is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} [_inst_1 : MeasureTheory.Measure.IsComplete.{u1} α m0 μ], (Eq.{1} ENNReal (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ s) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) -> (MeasurableSet.{u1} α m0 s)
but is expected to have type
  forall {α : Type.{u1}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {s : Set.{u1} α} [_inst_1 : MeasureTheory.Measure.IsComplete.{u1} α m0 μ], (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) s) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) -> (MeasurableSet.{u1} α m0 s)
Case conversion may be inaccurate. Consider using '#align measure_theory.measurable_set_of_null MeasureTheory.measurableSet_of_nullₓ'. -/
theorem measurableSet_of_null [μ.IsComplete] (hs : μ s = 0) : MeasurableSet s :=
  MeasureTheory.Measure.IsComplete.out' s hs
#align measure_theory.measurable_set_of_null MeasureTheory.measurableSet_of_null

#print MeasureTheory.NullMeasurableSet.measurable_of_complete /-
theorem NullMeasurableSet.measurable_of_complete (hs : NullMeasurableSet s μ) [μ.IsComplete] :
    MeasurableSet s :=
  diff_diff_cancel_left (subset_toMeasurable μ s) ▸
    (measurableSet_toMeasurable _ _).diffₓ
      (measurableSet_of_null (ae_le_set.1 hs.toMeasurable_ae_eq.le))
#align measure_theory.null_measurable_set.measurable_of_complete MeasureTheory.NullMeasurableSet.measurable_of_complete
-/

/- warning: measure_theory.null_measurable.measurable_of_complete -> MeasureTheory.NullMeasurable.measurable_of_complete is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_1 : MeasureTheory.Measure.IsComplete.{u1} α m0 μ] {m1 : MeasurableSpace.{u2} β} {f : α -> β}, (MeasureTheory.NullMeasurable.{u1, u2} α β m0 m1 f μ) -> (Measurable.{u1, u2} α β m0 m1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_1 : MeasureTheory.Measure.IsComplete.{u2} α m0 μ] {m1 : MeasurableSpace.{u1} β} {f : α -> β}, (MeasureTheory.NullMeasurable.{u2, u1} α β m0 m1 f μ) -> (Measurable.{u2, u1} α β m0 m1 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.null_measurable.measurable_of_complete MeasureTheory.NullMeasurable.measurable_of_completeₓ'. -/
theorem NullMeasurable.measurable_of_complete [μ.IsComplete] {m1 : MeasurableSpace β} {f : α → β}
    (hf : NullMeasurable f μ) : Measurable f := fun s hs => (hf hs).measurable_of_complete
#align measure_theory.null_measurable.measurable_of_complete MeasureTheory.NullMeasurable.measurable_of_complete

/- warning: measurable.congr_ae -> Measurable.congr_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {μ : MeasureTheory.Measure.{u1} α _inst_1} [hμ : MeasureTheory.Measure.IsComplete.{u1} α _inst_1 μ] {f : α -> β} {g : α -> β}, (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g) -> (Measurable.{u1, u2} α β _inst_1 _inst_2 g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {μ : MeasureTheory.Measure.{u2} α _inst_1} [hμ : MeasureTheory.Measure.IsComplete.{u2} α _inst_1 μ] {f : α -> β} {g : α -> β}, (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f g) -> (Measurable.{u2, u1} α β _inst_1 _inst_2 g)
Case conversion may be inaccurate. Consider using '#align measurable.congr_ae Measurable.congr_aeₓ'. -/
theorem Measurable.congr_ae {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    [hμ : μ.IsComplete] {f g : α → β} (hf : Measurable f) (hfg : f =ᵐ[μ] g) : Measurable g :=
  (hf.NullMeasurable.congr hfg).measurable_of_complete
#align measurable.congr_ae Measurable.congr_ae

namespace Measure

#print MeasureTheory.Measure.completion /-
/-- Given a measure we can complete it to a (complete) measure on all null measurable sets. -/
def completion {_ : MeasurableSpace α} (μ : Measure α) :
    @MeasureTheory.Measure (NullMeasurableSpace α μ) _
    where
  toOuterMeasure := μ.toOuterMeasure
  m_iUnion s hs hd := measure_iUnion₀ (hd.mono fun i j h => h.AEDisjoint) hs
  trimmed := by
    refine' le_antisymm (fun s => _) (outer_measure.le_trim _)
    rw [outer_measure.trim_eq_infi]; simp only [to_outer_measure_apply]
    refine' (iInf₂_mono _).trans_eq (measure_eq_infi _).symm
    exact fun t ht => iInf_mono' fun h => ⟨h.NullMeasurableSet, le_rfl⟩
#align measure_theory.measure.completion MeasureTheory.Measure.completion
-/

#print MeasureTheory.Measure.completion.isComplete /-
instance completion.isComplete {m : MeasurableSpace α} (μ : Measure α) : μ.Completion.IsComplete :=
  ⟨fun z hz => NullMeasurableSet.of_null hz⟩
#align measure_theory.measure.completion.is_complete MeasureTheory.Measure.completion.isComplete
-/

#print MeasureTheory.Measure.coe_completion /-
@[simp]
theorem coe_completion {_ : MeasurableSpace α} (μ : Measure α) : ⇑μ.Completion = μ :=
  rfl
#align measure_theory.measure.coe_completion MeasureTheory.Measure.coe_completion
-/

#print MeasureTheory.Measure.completion_apply /-
theorem completion_apply {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.Completion s = μ s :=
  rfl
#align measure_theory.measure.completion_apply MeasureTheory.Measure.completion_apply
-/

end Measure

end IsComplete

end MeasureTheory

