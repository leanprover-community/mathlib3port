/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module topology.bornology.basic
! leanprover-community/mathlib commit a11f9106a169dd302a285019e5165f8ab32ff433
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Cofinite

/-!
# Basic theory of bornology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter.  This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `bornology.of_bounded`,
`is_bounded.union`, `is_bounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `bornology α`: a class consisting of `cobounded : filter α` and a proof that this filter
  contains the `cofinite` filter.
- `bornology.is_cobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : set α`, one should prefer `bornology.is_cobounded s` over `s ∈ cobounded α`.
- `bornology.is_bounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `bornology.is_bounded s` over `sᶜ ∈ cobounded α`.
- `bounded_space α`: a class extending `bornology α` with the condition
  `bornology.is_bounded (set.univ : set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/


open Set Filter

variable {ι α β : Type _}

#print Bornology /-
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`cobounded] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:393:30: infer kinds are unsupported in Lean 4: #[`le_cofinite] [] -/
/-- A **bornology** on a type `α` is a filter of cobounded sets which contains the cofinite filter.
Such spaces are equivalently specified by their bounded sets, see `bornology.of_bounded`
and `bornology.ext_iff_is_bounded`-/
@[ext]
class Bornology (α : Type _) where
  cobounded : Filter α
  le_cofinite : cobounded ≤ cofinite
#align bornology Bornology
-/

/- warning: bornology.of_bounded -> Bornology.ofBounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (B : Set.{u1} (Set.{u1} α)), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) B) -> (forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₁) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B))) -> (forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) B))) -> (forall (x : α), Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) B) -> (Bornology.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (B : Set.{u1} (Set.{u1} α)), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) B) -> (forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₂ s₁) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B))) -> (forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) B))) -> (forall (x : α), Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) B) -> (Bornology.{u1} α)
Case conversion may be inaccurate. Consider using '#align bornology.of_bounded Bornology.ofBoundedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s₁ s₂ «expr ∈ » B) -/
/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps]
def Bornology.ofBounded {α : Type _} (B : Set (Set α)) (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ : Set α, s₂ ⊆ s₁ → s₂ ∈ B)
    (union_mem : ∀ (s₁) (_ : s₁ ∈ B) (s₂) (_ : s₂ ∈ B), s₁ ∪ s₂ ∈ B)
    (singleton_mem : ∀ x, {x} ∈ B) : Bornology α
    where
  cobounded :=
    { sets := { s : Set α | sᶜ ∈ B }
      univ_sets := by rwa [← compl_univ] at empty_mem
      sets_of_superset := fun x y hx hy => subset_mem (xᶜ) hx (yᶜ) (compl_subset_compl.mpr hy)
      inter_sets := fun x y hx hy => by simpa [compl_inter] using union_mem (xᶜ) hx (yᶜ) hy }
  le_cofinite := by
    rw [le_cofinite_iff_compl_singleton_mem]
    intro x
    change {x}ᶜᶜ ∈ B
    rw [compl_compl]
    exact singleton_mem x
#align bornology.of_bounded Bornology.ofBounded

/- warning: bornology.of_bounded' -> Bornology.ofBounded' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (B : Set.{u1} (Set.{u1} α)), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) B) -> (forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₁) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B))) -> (forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) B))) -> (Eq.{succ u1} (Set.{u1} α) (Set.sUnion.{u1} α B) (Set.univ.{u1} α)) -> (Bornology.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (B : Set.{u1} (Set.{u1} α)), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) B) -> (forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₂ s₁) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B))) -> (forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) B))) -> (Eq.{succ u1} (Set.{u1} α) (Set.sUnion.{u1} α B) (Set.univ.{u1} α)) -> (Bornology.{u1} α)
Case conversion may be inaccurate. Consider using '#align bornology.of_bounded' Bornology.ofBounded'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s₁ s₂ «expr ∈ » B) -/
/-- A constructor for bornologies by specifying the bounded sets,
and showing that they satisfy the appropriate conditions. -/
@[simps]
def Bornology.ofBounded' {α : Type _} (B : Set (Set α)) (empty_mem : ∅ ∈ B)
    (subset_mem : ∀ s₁ ∈ B, ∀ s₂ : Set α, s₂ ⊆ s₁ → s₂ ∈ B)
    (union_mem : ∀ (s₁) (_ : s₁ ∈ B) (s₂) (_ : s₂ ∈ B), s₁ ∪ s₂ ∈ B) (sUnion_univ : ⋃₀ B = univ) :
    Bornology α :=
  Bornology.ofBounded B empty_mem subset_mem union_mem fun x =>
    by
    rw [sUnion_eq_univ_iff] at sUnion_univ
    rcases sUnion_univ x with ⟨s, hs, hxs⟩
    exact subset_mem s hs {x} (singleton_subset_iff.mpr hxs)
#align bornology.of_bounded' Bornology.ofBounded'

namespace Bornology

section

variable [Bornology α] {s t : Set α} {x : α}

#print Bornology.IsCobounded /-
/-- `is_cobounded` is the predicate that `s` is in the filter of cobounded sets in the ambient
bornology on `α` -/
def IsCobounded (s : Set α) : Prop :=
  s ∈ cobounded α
#align bornology.is_cobounded Bornology.IsCobounded
-/

#print Bornology.IsBounded /-
/-- `is_bounded` is the predicate that `s` is bounded relative to the ambient bornology on `α`. -/
def IsBounded (s : Set α) : Prop :=
  IsCobounded (sᶜ)
#align bornology.is_bounded Bornology.IsBounded
-/

#print Bornology.isCobounded_def /-
theorem isCobounded_def {s : Set α} : IsCobounded s ↔ s ∈ cobounded α :=
  Iff.rfl
#align bornology.is_cobounded_def Bornology.isCobounded_def
-/

/- warning: bornology.is_bounded_def -> Bornology.isBounded_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α _inst_1 s) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Bornology.cobounded.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α _inst_1 s) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (Bornology.cobounded.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_def Bornology.isBounded_defₓ'. -/
theorem isBounded_def {s : Set α} : IsBounded s ↔ sᶜ ∈ cobounded α :=
  Iff.rfl
#align bornology.is_bounded_def Bornology.isBounded_def

/- warning: bornology.is_bounded_compl_iff -> Bornology.isBounded_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Bornology.IsCobounded.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Bornology.IsCobounded.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_compl_iff Bornology.isBounded_compl_iffₓ'. -/
@[simp]
theorem isBounded_compl_iff : IsBounded (sᶜ) ↔ IsCobounded s := by
  rw [is_bounded_def, is_cobounded_def, compl_compl]
#align bornology.is_bounded_compl_iff Bornology.isBounded_compl_iff

/- warning: bornology.is_cobounded_compl_iff -> Bornology.isCobounded_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsCobounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Bornology.IsBounded.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsCobounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Bornology.IsBounded.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded_compl_iff Bornology.isCobounded_compl_iffₓ'. -/
@[simp]
theorem isCobounded_compl_iff : IsCobounded (sᶜ) ↔ IsBounded s :=
  Iff.rfl
#align bornology.is_cobounded_compl_iff Bornology.isCobounded_compl_iff

/- warning: bornology.is_bounded.of_compl -> Bornology.IsBounded.of_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsBounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> (Bornology.IsCobounded.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsBounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) -> (Bornology.IsCobounded.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.of_compl Bornology.IsBounded.of_complₓ'. -/
/- warning: bornology.is_cobounded.compl -> Bornology.IsCobounded.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsCobounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsCobounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded.compl Bornology.IsCobounded.complₓ'. -/
alias is_bounded_compl_iff ↔ is_bounded.of_compl is_cobounded.compl
#align bornology.is_bounded.of_compl Bornology.IsBounded.of_compl
#align bornology.is_cobounded.compl Bornology.IsCobounded.compl

/- warning: bornology.is_cobounded.of_compl -> Bornology.IsCobounded.of_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsCobounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> (Bornology.IsBounded.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsCobounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) -> (Bornology.IsBounded.{u1} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded.of_compl Bornology.IsCobounded.of_complₓ'. -/
/- warning: bornology.is_bounded.compl -> Bornology.IsBounded.compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsCobounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsCobounded.{u1} α _inst_1 (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.compl Bornology.IsBounded.complₓ'. -/
alias is_cobounded_compl_iff ↔ is_cobounded.of_compl is_bounded.compl
#align bornology.is_cobounded.of_compl Bornology.IsCobounded.of_compl
#align bornology.is_bounded.compl Bornology.IsBounded.compl

#print Bornology.isBounded_empty /-
@[simp]
theorem isBounded_empty : IsBounded (∅ : Set α) := by rw [is_bounded_def, compl_empty];
  exact univ_mem
#align bornology.is_bounded_empty Bornology.isBounded_empty
-/

#print Bornology.isBounded_singleton /-
@[simp]
theorem isBounded_singleton : IsBounded ({x} : Set α) := by rw [is_bounded_def];
  exact le_cofinite _ (finite_singleton x).compl_mem_cofinite
#align bornology.is_bounded_singleton Bornology.isBounded_singleton
-/

#print Bornology.isCobounded_univ /-
@[simp]
theorem isCobounded_univ : IsCobounded (univ : Set α) :=
  univ_mem
#align bornology.is_cobounded_univ Bornology.isCobounded_univ
-/

/- warning: bornology.is_cobounded_inter -> Bornology.isCobounded_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Bornology.IsCobounded.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (And (Bornology.IsCobounded.{u1} α _inst_1 s) (Bornology.IsCobounded.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Bornology.IsCobounded.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (And (Bornology.IsCobounded.{u1} α _inst_1 s) (Bornology.IsCobounded.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded_inter Bornology.isCobounded_interₓ'. -/
@[simp]
theorem isCobounded_inter : IsCobounded (s ∩ t) ↔ IsCobounded s ∧ IsCobounded t :=
  inter_mem_iff
#align bornology.is_cobounded_inter Bornology.isCobounded_inter

/- warning: bornology.is_cobounded.inter -> Bornology.IsCobounded.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Bornology.IsCobounded.{u1} α _inst_1 s) -> (Bornology.IsCobounded.{u1} α _inst_1 t) -> (Bornology.IsCobounded.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Bornology.IsCobounded.{u1} α _inst_1 s) -> (Bornology.IsCobounded.{u1} α _inst_1 t) -> (Bornology.IsCobounded.{u1} α _inst_1 (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded.inter Bornology.IsCobounded.interₓ'. -/
theorem IsCobounded.inter (hs : IsCobounded s) (ht : IsCobounded t) : IsCobounded (s ∩ t) :=
  isCobounded_inter.2 ⟨hs, ht⟩
#align bornology.is_cobounded.inter Bornology.IsCobounded.inter

/- warning: bornology.is_bounded_union -> Bornology.isBounded_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (And (Bornology.IsBounded.{u1} α _inst_1 s) (Bornology.IsBounded.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (And (Bornology.IsBounded.{u1} α _inst_1 s) (Bornology.IsBounded.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_union Bornology.isBounded_unionₓ'. -/
@[simp]
theorem isBounded_union : IsBounded (s ∪ t) ↔ IsBounded s ∧ IsBounded t := by
  simp only [← is_cobounded_compl_iff, compl_union, is_cobounded_inter]
#align bornology.is_bounded_union Bornology.isBounded_union

/- warning: bornology.is_bounded.union -> Bornology.IsBounded.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u1} α _inst_1 t) -> (Bornology.IsBounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u1} α _inst_1 t) -> (Bornology.IsBounded.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.union Bornology.IsBounded.unionₓ'. -/
theorem IsBounded.union (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ∪ t) :=
  isBounded_union.2 ⟨hs, ht⟩
#align bornology.is_bounded.union Bornology.IsBounded.union

#print Bornology.IsCobounded.superset /-
theorem IsCobounded.superset (hs : IsCobounded s) (ht : s ⊆ t) : IsCobounded t :=
  mem_of_superset hs ht
#align bornology.is_cobounded.superset Bornology.IsCobounded.superset
-/

#print Bornology.IsBounded.subset /-
theorem IsBounded.subset (ht : IsBounded t) (hs : s ⊆ t) : IsBounded s :=
  ht.Superset (compl_subset_compl.mpr hs)
#align bornology.is_bounded.subset Bornology.IsBounded.subset
-/

#print Bornology.sUnion_bounded_univ /-
@[simp]
theorem sUnion_bounded_univ : ⋃₀ { s : Set α | IsBounded s } = univ :=
  sUnion_eq_univ_iff.2 fun a => ⟨{a}, isBounded_singleton, mem_singleton a⟩
#align bornology.sUnion_bounded_univ Bornology.sUnion_bounded_univ
-/

/- warning: bornology.comap_cobounded_le_iff -> Bornology.comap_cobounded_le_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] {f : α -> β}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) (Filter.comap.{u1, u2} α β f (Bornology.cobounded.{u2} β _inst_2)) (Bornology.cobounded.{u1} α _inst_1)) (forall {{s : Set.{u1} α}}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Bornology.{u2} β] {f : α -> β}, Iff (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) (Filter.comap.{u1, u2} α β f (Bornology.cobounded.{u2} β _inst_2)) (Bornology.cobounded.{u1} α _inst_1)) (forall {{s : Set.{u1} α}}, (Bornology.IsBounded.{u1} α _inst_1 s) -> (Bornology.IsBounded.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
Case conversion may be inaccurate. Consider using '#align bornology.comap_cobounded_le_iff Bornology.comap_cobounded_le_iffₓ'. -/
theorem comap_cobounded_le_iff [Bornology β] {f : α → β} :
    (cobounded β).comap f ≤ cobounded α ↔ ∀ ⦃s⦄, IsBounded s → IsBounded (f '' s) :=
  by
  refine'
    ⟨fun h s hs => _, fun h t ht =>
      ⟨(f '' tᶜ)ᶜ, h <| is_cobounded.compl ht, compl_subset_comm.1 <| subset_preimage_image _ _⟩⟩
  obtain ⟨t, ht, hts⟩ := h hs.compl
  rw [subset_compl_comm, ← preimage_compl] at hts
  exact (is_cobounded.compl ht).Subset ((image_subset f hts).trans <| image_preimage_subset _ _)
#align bornology.comap_cobounded_le_iff Bornology.comap_cobounded_le_iff

end

#print Bornology.ext_iff' /-
theorem ext_iff' {t t' : Bornology α} :
    t = t' ↔ ∀ s, (@cobounded α t).sets s ↔ (@cobounded α t').sets s :=
  (ext_iff _ _).trans Filter.ext_iff
#align bornology.ext_iff' Bornology.ext_iff'
-/

#print Bornology.ext_iff_isBounded /-
theorem ext_iff_isBounded {t t' : Bornology α} :
    t = t' ↔ ∀ s, @IsBounded α t s ↔ @IsBounded α t' s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by ext; simpa only [is_bounded_def, compl_compl] using h (sᶜ)⟩
#align bornology.ext_iff_is_bounded Bornology.ext_iff_isBounded
-/

variable {s : Set α}

/- warning: bornology.is_cobounded_of_bounded_iff -> Bornology.isCobounded_ofBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} (B : Set.{u1} (Set.{u1} α)) {empty_mem : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) B} {subset_mem : forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₁) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B))} {union_mem : forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) B))} {sUnion_univ : forall (x : α), Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) B}, Iff (Bornology.IsCobounded.{u1} α (Bornology.ofBounded.{u1} α B empty_mem subset_mem union_mem sUnion_univ) s) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) B)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} (B : Set.{u1} (Set.{u1} α)) {empty_mem : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) B} {subset_mem : forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₂ s₁) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B))} {union_mem : forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) B))} {sUnion_univ : forall (x : α), Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) B}, Iff (Bornology.IsCobounded.{u1} α (Bornology.ofBounded.{u1} α B empty_mem subset_mem union_mem sUnion_univ) s) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) B)
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded_of_bounded_iff Bornology.isCobounded_ofBounded_iffₓ'. -/
theorem isCobounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsCobounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ sᶜ ∈ B :=
  Iff.rfl
#align bornology.is_cobounded_of_bounded_iff Bornology.isCobounded_ofBounded_iff

/- warning: bornology.is_bounded_of_bounded_iff -> Bornology.isBounded_ofBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} (B : Set.{u1} (Set.{u1} α)) {empty_mem : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) B} {subset_mem : forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₁) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B))} {union_mem : forall (s₁ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s₂ B) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) B))} {sUnion_univ : forall (x : α), Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) B}, Iff (Bornology.IsBounded.{u1} α (Bornology.ofBounded.{u1} α B empty_mem subset_mem union_mem sUnion_univ) s) (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s B)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} (B : Set.{u1} (Set.{u1} α)) {empty_mem : Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) B} {subset_mem : forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₂ s₁) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B))} {union_mem : forall (s₁ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₁ B) -> (forall (s₂ : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s₂ B) -> (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) B))} {sUnion_univ : forall (x : α), Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) B}, Iff (Bornology.IsBounded.{u1} α (Bornology.ofBounded.{u1} α B empty_mem subset_mem union_mem sUnion_univ) s) (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s B)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_of_bounded_iff Bornology.isBounded_ofBounded_iffₓ'. -/
theorem isBounded_ofBounded_iff (B : Set (Set α)) {empty_mem subset_mem union_mem sUnion_univ} :
    @IsBounded _ (ofBounded B empty_mem subset_mem union_mem sUnion_univ) s ↔ s ∈ B := by
  rw [is_bounded_def, ← Filter.mem_sets, of_bounded_cobounded_sets, Set.mem_setOf_eq, compl_compl]
#align bornology.is_bounded_of_bounded_iff Bornology.isBounded_ofBounded_iff

variable [Bornology α]

/- warning: bornology.is_cobounded_bInter -> Bornology.isCobounded_biInter is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Bornology.{u2} α] {s : Set.{u1} ι} {f : ι -> (Set.{u2} α)}, (Set.Finite.{u1} ι s) -> (Iff (Bornology.IsCobounded.{u2} α _inst_1 (Set.iInter.{u2, succ u1} α ι (fun (i : ι) => Set.iInter.{u2, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i)))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Bornology.IsCobounded.{u2} α _inst_1 (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.Finite.{u2} ι s) -> (Iff (Bornology.IsCobounded.{u1} α _inst_1 (Set.iInter.{u1, succ u2} α ι (fun (i : ι) => Set.iInter.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i)))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Bornology.IsCobounded.{u1} α _inst_1 (f i))))
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded_bInter Bornology.isCobounded_biInterₓ'. -/
theorem isCobounded_biInter {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_mem hs
#align bornology.is_cobounded_bInter Bornology.isCobounded_biInter

/- warning: bornology.is_cobounded_bInter_finset -> Bornology.isCobounded_biInter_finset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Bornology.{u2} α] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Bornology.IsCobounded.{u2} α _inst_1 (Set.iInter.{u2, succ u1} α ι (fun (i : ι) => Set.iInter.{u2, 0} α (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => f i)))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Bornology.IsCobounded.{u2} α _inst_1 (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] (s : Finset.{u2} ι) {f : ι -> (Set.{u1} α)}, Iff (Bornology.IsCobounded.{u1} α _inst_1 (Set.iInter.{u1, succ u2} α ι (fun (i : ι) => Set.iInter.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => f i)))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Bornology.IsCobounded.{u1} α _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded_bInter_finset Bornology.isCobounded_biInter_finsetₓ'. -/
@[simp]
theorem isCobounded_biInter_finset (s : Finset ι) {f : ι → Set α} :
    IsCobounded (⋂ i ∈ s, f i) ↔ ∀ i ∈ s, IsCobounded (f i) :=
  biInter_finset_mem s
#align bornology.is_cobounded_bInter_finset Bornology.isCobounded_biInter_finset

/- warning: bornology.is_cobounded_Inter -> Bornology.isCobounded_iInter is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Finite.{succ u1} ι] {f : ι -> (Set.{u2} α)}, Iff (Bornology.IsCobounded.{u2} α _inst_1 (Set.iInter.{u2, succ u1} α ι (fun (i : ι) => f i))) (forall (i : ι), Bornology.IsCobounded.{u2} α _inst_1 (f i))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Finite.{succ u2} ι] {f : ι -> (Set.{u1} α)}, Iff (Bornology.IsCobounded.{u1} α _inst_1 (Set.iInter.{u1, succ u2} α ι (fun (i : ι) => f i))) (forall (i : ι), Bornology.IsCobounded.{u1} α _inst_1 (f i))
Case conversion may be inaccurate. Consider using '#align bornology.is_cobounded_Inter Bornology.isCobounded_iInterₓ'. -/
@[simp]
theorem isCobounded_iInter [Finite ι] {f : ι → Set α} :
    IsCobounded (⋂ i, f i) ↔ ∀ i, IsCobounded (f i) :=
  iInter_mem
#align bornology.is_cobounded_Inter Bornology.isCobounded_iInter

#print Bornology.isCobounded_sInter /-
theorem isCobounded_sInter {S : Set (Set α)} (hs : S.Finite) :
    IsCobounded (⋂₀ S) ↔ ∀ s ∈ S, IsCobounded s :=
  sInter_mem hs
#align bornology.is_cobounded_sInter Bornology.isCobounded_sInter
-/

/- warning: bornology.is_bounded_bUnion -> Bornology.isBounded_biUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Bornology.{u2} α] {s : Set.{u1} ι} {f : ι -> (Set.{u2} α)}, (Set.Finite.{u1} ι s) -> (Iff (Bornology.IsBounded.{u2} α _inst_1 (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => Set.iUnion.{u2, 0} α (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) => f i)))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Bornology.IsBounded.{u2} α _inst_1 (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] {s : Set.{u2} ι} {f : ι -> (Set.{u1} α)}, (Set.Finite.{u2} ι s) -> (Iff (Bornology.IsBounded.{u1} α _inst_1 (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) => f i)))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Bornology.IsBounded.{u1} α _inst_1 (f i))))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_bUnion Bornology.isBounded_biUnionₓ'. -/
theorem isBounded_biUnion {s : Set ι} {f : ι → Set α} (hs : s.Finite) :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) := by
  simp only [← is_cobounded_compl_iff, compl_Union, is_cobounded_bInter hs]
#align bornology.is_bounded_bUnion Bornology.isBounded_biUnion

/- warning: bornology.is_bounded_bUnion_finset -> Bornology.isBounded_biUnion_finset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Bornology.{u2} α] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Bornology.IsBounded.{u2} α _inst_1 (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => Set.iUnion.{u2, 0} α (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => f i)))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Bornology.IsBounded.{u2} α _inst_1 (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] (s : Finset.{u2} ι) {f : ι -> (Set.{u1} α)}, Iff (Bornology.IsBounded.{u1} α _inst_1 (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => Set.iUnion.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => f i)))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Bornology.IsBounded.{u1} α _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_bUnion_finset Bornology.isBounded_biUnion_finsetₓ'. -/
theorem isBounded_biUnion_finset (s : Finset ι) {f : ι → Set α} :
    IsBounded (⋃ i ∈ s, f i) ↔ ∀ i ∈ s, IsBounded (f i) :=
  isBounded_biUnion s.finite_toSet
#align bornology.is_bounded_bUnion_finset Bornology.isBounded_biUnion_finset

#print Bornology.isBounded_sUnion /-
theorem isBounded_sUnion {S : Set (Set α)} (hs : S.Finite) :
    IsBounded (⋃₀ S) ↔ ∀ s ∈ S, IsBounded s := by rw [sUnion_eq_bUnion, is_bounded_bUnion hs]
#align bornology.is_bounded_sUnion Bornology.isBounded_sUnion
-/

/- warning: bornology.is_bounded_Union -> Bornology.isBounded_iUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Bornology.{u2} α] [_inst_2 : Finite.{succ u1} ι] {s : ι -> (Set.{u2} α)}, Iff (Bornology.IsBounded.{u2} α _inst_1 (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i))) (forall (i : ι), Bornology.IsBounded.{u2} α _inst_1 (s i))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : Bornology.{u1} α] [_inst_2 : Finite.{succ u2} ι] {s : ι -> (Set.{u1} α)}, Iff (Bornology.IsBounded.{u1} α _inst_1 (Set.iUnion.{u1, succ u2} α ι (fun (i : ι) => s i))) (forall (i : ι), Bornology.IsBounded.{u1} α _inst_1 (s i))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_Union Bornology.isBounded_iUnionₓ'. -/
@[simp]
theorem isBounded_iUnion [Finite ι] {s : ι → Set α} : IsBounded (⋃ i, s i) ↔ ∀ i, IsBounded (s i) :=
  by rw [← sUnion_range, is_bounded_sUnion (finite_range s), forall_range_iff]
#align bornology.is_bounded_Union Bornology.isBounded_iUnion

end Bornology

open Bornology

#print Set.Finite.isBounded /-
theorem Set.Finite.isBounded [Bornology α] {s : Set α} (hs : s.Finite) : IsBounded s :=
  Bornology.le_cofinite α hs.compl_mem_cofinite
#align set.finite.is_bounded Set.Finite.isBounded
-/

instance : Bornology PUnit :=
  ⟨⊥, bot_le⟩

#print Bornology.cofinite /-
/-- The cofinite filter as a bornology -/
@[reducible]
def Bornology.cofinite : Bornology α
    where
  cobounded := cofinite
  le_cofinite := le_rfl
#align bornology.cofinite Bornology.cofinite
-/

#print BoundedSpace /-
/-- A space with a `bornology` is a **bounded space** if `set.univ : set α` is bounded. -/
class BoundedSpace (α : Type _) [Bornology α] : Prop where
  bounded_univ : Bornology.IsBounded (univ : Set α)
#align bounded_space BoundedSpace
-/

namespace Bornology

variable [Bornology α]

#print Bornology.isBounded_univ /-
theorem isBounded_univ : IsBounded (univ : Set α) ↔ BoundedSpace α :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩
#align bornology.is_bounded_univ Bornology.isBounded_univ
-/

/- warning: bornology.cobounded_eq_bot_iff -> Bornology.cobounded_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α], Iff (Eq.{succ u1} (Filter.{u1} α) (Bornology.cobounded.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (BoundedSpace.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Bornology.{u1} α], Iff (Eq.{succ u1} (Filter.{u1} α) (Bornology.cobounded.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (BoundedSpace.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align bornology.cobounded_eq_bot_iff Bornology.cobounded_eq_bot_iffₓ'. -/
theorem cobounded_eq_bot_iff : cobounded α = ⊥ ↔ BoundedSpace α := by
  rw [← is_bounded_univ, is_bounded_def, compl_univ, empty_mem_iff_bot]
#align bornology.cobounded_eq_bot_iff Bornology.cobounded_eq_bot_iff

variable [BoundedSpace α]

#print Bornology.IsBounded.all /-
theorem IsBounded.all (s : Set α) : IsBounded s :=
  BoundedSpace.bounded_univ.Subset s.subset_univ
#align bornology.is_bounded.all Bornology.IsBounded.all
-/

#print Bornology.IsCobounded.all /-
theorem IsCobounded.all (s : Set α) : IsCobounded s :=
  compl_compl s ▸ IsBounded.all (sᶜ)
#align bornology.is_cobounded.all Bornology.IsCobounded.all
-/

variable (α)

/- warning: bornology.cobounded_eq_bot -> Bornology.cobounded_eq_bot is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Bornology.{u1} α] [_inst_2 : BoundedSpace.{u1} α _inst_1], Eq.{succ u1} (Filter.{u1} α) (Bornology.cobounded.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Bornology.{u1} α] [_inst_2 : BoundedSpace.{u1} α _inst_1], Eq.{succ u1} (Filter.{u1} α) (Bornology.cobounded.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align bornology.cobounded_eq_bot Bornology.cobounded_eq_botₓ'. -/
@[simp]
theorem cobounded_eq_bot : cobounded α = ⊥ :=
  cobounded_eq_bot_iff.2 ‹_›
#align bornology.cobounded_eq_bot Bornology.cobounded_eq_bot

end Bornology

