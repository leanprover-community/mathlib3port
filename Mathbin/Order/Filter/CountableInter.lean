/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module order.filter.countable_Inter
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Basic
import Mathbin.Data.Set.Countable

/-!
# Filters with countable intersection property

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `countable_Inter_filter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `topology.metric_space.baire` and
the `measure.ae` filter defined in `measure_theory.measure_space`.

We reformulate the definition in terms of indexed intersection and in terms of `filter.eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `filter.principal`, `filter.map`,
`filter.comap`, `has_inf.inf`). We also provide a custom constructor `filter.of_countable_Inter`
that deduces two axioms of a `filter` from the countable intersection property.

## Tags
filter, countable
-/


open Set Filter

open Filter

variable {ι : Sort _} {α β : Type _}

#print CountableInterFilter /-
/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CountableInterFilter (l : Filter α) : Prop where
  countable_sInter_mem' : ∀ {S : Set (Set α)} (hSc : S.Countable) (hS : ∀ s ∈ S, s ∈ l), ⋂₀ S ∈ l
#align countable_Inter_filter CountableInterFilter
-/

variable {l : Filter α} [CountableInterFilter l]

#print countable_interₛ_mem /-
theorem countable_interₛ_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
  ⟨fun hS s hs => mem_of_superset hS (interₛ_subset_of_mem hs),
    CountableInterFilter.countable_interₛ_mem' hSc⟩
#align countable_sInter_mem countable_interₛ_mem
-/

/- warning: countable_Inter_mem -> countable_interᵢ_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {l : Filter.{u2} α} [_inst_1 : CountableInterFilter.{u2} α l] [_inst_2 : Countable.{u1} ι] {s : ι -> (Set.{u2} α)}, Iff (Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) l) (forall (i : ι), Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) (s i) l)
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {l : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α l] [_inst_2 : Countable.{u2} ι] {s : ι -> (Set.{u1} α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) l) (forall (i : ι), Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) (s i) l)
Case conversion may be inaccurate. Consider using '#align countable_Inter_mem countable_interᵢ_memₓ'. -/
theorem countable_interᵢ_mem [Countable ι] {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  interₛ_range s ▸ (countable_interₛ_mem (countable_range _)).trans forall_range_iff
#align countable_Inter_mem countable_interᵢ_mem

#print countable_bInter_mem /-
theorem countable_bInter_mem {ι : Type _} {S : Set ι} (hS : S.Countable) {s : ∀ i ∈ S, Set α} :
    (⋂ i ∈ S, s i ‹_›) ∈ l ↔ ∀ i ∈ S, s i ‹_› ∈ l :=
  by
  rw [bInter_eq_Inter]
  haveI := hS.to_encodable
  exact countable_Inter_mem.trans Subtype.forall
#align countable_bInter_mem countable_bInter_mem
-/

/- warning: eventually_countable_forall -> eventually_countable_forall is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {l : Filter.{u2} α} [_inst_1 : CountableInterFilter.{u2} α l] [_inst_2 : Countable.{u1} ι] {p : α -> ι -> Prop}, Iff (Filter.Eventually.{u2} α (fun (x : α) => forall (i : ι), p x i) l) (forall (i : ι), Filter.Eventually.{u2} α (fun (x : α) => p x i) l)
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {l : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α l] [_inst_2 : Countable.{u2} ι] {p : α -> ι -> Prop}, Iff (Filter.Eventually.{u1} α (fun (x : α) => forall (i : ι), p x i) l) (forall (i : ι), Filter.Eventually.{u1} α (fun (x : α) => p x i) l)
Case conversion may be inaccurate. Consider using '#align eventually_countable_forall eventually_countable_forallₓ'. -/
theorem eventually_countable_forall [Countable ι] {p : α → ι → Prop} :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simpa only [Filter.Eventually, set_of_forall] using
    @countable_interᵢ_mem _ _ l _ _ fun i => { x | p x i }
#align eventually_countable_forall eventually_countable_forall

#print eventually_countable_ball /-
theorem eventually_countable_ball {ι : Type _} {S : Set ι} (hS : S.Countable)
    {p : ∀ (x : α), ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i ∈ S, p x i ‹_›) ↔ ∀ i ∈ S, ∀ᶠ x in l, p x i ‹_› := by
  simpa only [Filter.Eventually, set_of_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }
#align eventually_countable_ball eventually_countable_ball
-/

/- warning: eventually_le.countable_Union -> EventuallyLe.countable_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {l : Filter.{u2} α} [_inst_1 : CountableInterFilter.{u2} α l] [_inst_2 : Countable.{u1} ι] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), Filter.EventuallyLe.{u2, 0} α Prop Prop.le l (s i) (t i)) -> (Filter.EventuallyLe.{u2, 0} α Prop Prop.le l (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {l : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α l] [_inst_2 : Countable.{u2} ι] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (s i) (t i)) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align eventually_le.countable_Union EventuallyLe.countable_unionᵢₓ'. -/
theorem EventuallyLe.countable_unionᵢ [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
  (eventually_countable_forall.2 h).mono fun x hst hs => mem_unionᵢ.2 <| (mem_unionᵢ.1 hs).imp hst
#align eventually_le.countable_Union EventuallyLe.countable_unionᵢ

/- warning: eventually_eq.countable_Union -> EventuallyEq.countable_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {l : Filter.{u2} α} [_inst_1 : CountableInterFilter.{u2} α l] [_inst_2 : Countable.{u1} ι] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), Filter.EventuallyEq.{u2, 0} α Prop l (s i) (t i)) -> (Filter.EventuallyEq.{u2, 0} α Prop l (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {l : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α l] [_inst_2 : Countable.{u2} ι] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), Filter.EventuallyEq.{u1, 0} α Prop l (s i) (t i)) -> (Filter.EventuallyEq.{u1, 0} α Prop l (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.unionᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align eventually_eq.countable_Union EventuallyEq.countable_unionᵢₓ'. -/
theorem EventuallyEq.countable_unionᵢ [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
  (EventuallyLe.countable_unionᵢ fun i => (h i).le).antisymm
    (EventuallyLe.countable_unionᵢ fun i => (h i).symm.le)
#align eventually_eq.countable_Union EventuallyEq.countable_unionᵢ

#print EventuallyLe.countable_bUnion /-
theorem EventuallyLe.countable_bUnion {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) :
    (⋃ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  by
  simp only [bUnion_eq_Union]
  haveI := hS.to_encodable
  exact EventuallyLe.countable_unionᵢ fun i => h i i.2
#align eventually_le.countable_bUnion EventuallyLe.countable_bUnion
-/

#print EventuallyEq.countable_bUnion /-
theorem EventuallyEq.countable_bUnion {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) :
    (⋃ i ∈ S, s i ‹_›) =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLe.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLe.countable_bUnion hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bUnion EventuallyEq.countable_bUnion
-/

/- warning: eventually_le.countable_Inter -> EventuallyLe.countable_interᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {l : Filter.{u2} α} [_inst_1 : CountableInterFilter.{u2} α l] [_inst_2 : Countable.{u1} ι] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), Filter.EventuallyLe.{u2, 0} α Prop Prop.le l (s i) (t i)) -> (Filter.EventuallyLe.{u2, 0} α Prop Prop.le l (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {l : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α l] [_inst_2 : Countable.{u2} ι] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (s i) (t i)) -> (Filter.EventuallyLe.{u1, 0} α Prop Prop.le l (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align eventually_le.countable_Inter EventuallyLe.countable_interᵢₓ'. -/
theorem EventuallyLe.countable_interᵢ [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun x hst hs =>
    mem_interᵢ.2 fun i => hst _ (mem_interᵢ.1 hs i)
#align eventually_le.countable_Inter EventuallyLe.countable_interᵢ

/- warning: eventually_eq.countable_Inter -> EventuallyEq.countable_interᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {l : Filter.{u2} α} [_inst_1 : CountableInterFilter.{u2} α l] [_inst_2 : Countable.{u1} ι] {s : ι -> (Set.{u2} α)} {t : ι -> (Set.{u2} α)}, (forall (i : ι), Filter.EventuallyEq.{u2, 0} α Prop l (s i) (t i)) -> (Filter.EventuallyEq.{u2, 0} α Prop l (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => t i)))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u1}} {l : Filter.{u1} α} [_inst_1 : CountableInterFilter.{u1} α l] [_inst_2 : Countable.{u2} ι] {s : ι -> (Set.{u1} α)} {t : ι -> (Set.{u1} α)}, (forall (i : ι), Filter.EventuallyEq.{u1, 0} α Prop l (s i) (t i)) -> (Filter.EventuallyEq.{u1, 0} α Prop l (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => s i)) (Set.interᵢ.{u1, u2} α ι (fun (i : ι) => t i)))
Case conversion may be inaccurate. Consider using '#align eventually_eq.countable_Inter EventuallyEq.countable_interᵢₓ'. -/
theorem EventuallyEq.countable_interᵢ [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
  (EventuallyLe.countable_interᵢ fun i => (h i).le).antisymm
    (EventuallyLe.countable_interᵢ fun i => (h i).symm.le)
#align eventually_eq.countable_Inter EventuallyEq.countable_interᵢ

#print EventuallyLe.countable_bInter /-
theorem EventuallyLe.countable_bInter {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) :
    (⋂ i ∈ S, s i ‹_›) ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  by
  simp only [bInter_eq_Inter]
  haveI := hS.to_encodable
  exact EventuallyLe.countable_interᵢ fun i => h i i.2
#align eventually_le.countable_bInter EventuallyLe.countable_bInter
-/

#print EventuallyEq.countable_bInter /-
theorem EventuallyEq.countable_bInter {ι : Type _} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) :
    (⋂ i ∈ S, s i ‹_›) =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLe.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLe.countable_bInter hS fun i hi => (h i hi).symm.le)
#align eventually_eq.countable_bInter EventuallyEq.countable_bInter
-/

#print Filter.ofCountableInter /-
/-- Construct a filter with countable intersection property. This constructor deduces
`filter.univ_sets` and `filter.inter_sets` from the countable intersection property. -/
def Filter.ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α
    where
  sets := l
  univ_sets := @interₛ_empty α ▸ hp _ countable_empty (empty_subset _)
  sets_of_superset := h_mono
  inter_sets s t hs ht :=
    interₛ_pair s t ▸
      hp _ ((countable_singleton _).insert _) (insert_subset.2 ⟨hs, singleton_subset_iff.2 ht⟩)
#align filter.of_countable_Inter Filter.ofCountableInter
-/

#print Filter.countable_Inter_ofCountableInter /-
instance Filter.countable_Inter_ofCountableInter (l : Set (Set α))
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCountableInter l hp h_mono) :=
  ⟨hp⟩
#align filter.countable_Inter_of_countable_Inter Filter.countable_Inter_ofCountableInter
-/

#print Filter.mem_ofCountableInter /-
@[simp]
theorem Filter.mem_ofCountableInter {l : Set (Set α)}
    (hp : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCountableInter l hp h_mono ↔ s ∈ l :=
  Iff.rfl
#align filter.mem_of_countable_Inter Filter.mem_ofCountableInter
-/

#print countableInterFilter_principal /-
instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun S hSc hS => subset_interₛ hS⟩
#align countable_Inter_filter_principal countableInterFilter_principal
-/

/- warning: countable_Inter_filter_bot -> countableInterFilter_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, CountableInterFilter.{u1} α (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}}, CountableInterFilter.{u1} α (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))
Case conversion may be inaccurate. Consider using '#align countable_Inter_filter_bot countableInterFilter_botₓ'. -/
instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) :=
  by
  rw [← principal_empty]
  apply countableInterFilter_principal
#align countable_Inter_filter_bot countableInterFilter_bot

/- warning: countable_Inter_filter_top -> countableInterFilter_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, CountableInterFilter.{u1} α (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, CountableInterFilter.{u1} α (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))
Case conversion may be inaccurate. Consider using '#align countable_Inter_filter_top countableInterFilter_topₓ'. -/
instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) :=
  by
  rw [← principal_univ]
  apply countableInterFilter_principal
#align countable_Inter_filter_top countableInterFilter_top

instance (l : Filter β) [CountableInterFilter l] (f : α → β) : CountableInterFilter (comap f l) :=
  by
  refine' ⟨fun S hSc hS => _⟩
  choose! t htl ht using hS
  have : (⋂ s ∈ S, t s) ∈ l := (countable_bInter_mem hSc).2 htl
  refine' ⟨_, this, _⟩
  simpa [preimage_Inter] using Inter₂_mono ht

instance (l : Filter α) [CountableInterFilter l] (f : α → β) : CountableInterFilter (map f l) :=
  by
  constructor; intro S hSc hS
  simp only [mem_map, sInter_eq_bInter, preimage_Inter₂] at hS⊢
  exact (countable_bInter_mem hSc).2 hS

/- warning: countable_Inter_filter_inf -> countableInterFilter_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l₁ : Filter.{u1} α) (l₂ : Filter.{u1} α) [_inst_2 : CountableInterFilter.{u1} α l₁] [_inst_3 : CountableInterFilter.{u1} α l₂], CountableInterFilter.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} (l₁ : Filter.{u1} α) (l₂ : Filter.{u1} α) [_inst_2 : CountableInterFilter.{u1} α l₁] [_inst_3 : CountableInterFilter.{u1} α l₂], CountableInterFilter.{u1} α (HasInf.inf.{u1} (Filter.{u1} α) (Filter.instHasInfFilter.{u1} α) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align countable_Inter_filter_inf countableInterFilter_infₓ'. -/
/-- Infimum of two `countable_Inter_filter`s is a `countable_Inter_filter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) :=
  by
  refine' ⟨fun S hSc hS => _⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht
  refine' mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => _)
  rw [hst i hi]
  apply inter_subset_inter <;> exact Inter_subset_of_subset i (Inter_subset _ _)
#align countable_Inter_filter_inf countableInterFilter_inf

/- warning: countable_Inter_filter_sup -> countableInterFilter_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l₁ : Filter.{u1} α) (l₂ : Filter.{u1} α) [_inst_2 : CountableInterFilter.{u1} α l₁] [_inst_3 : CountableInterFilter.{u1} α l₂], CountableInterFilter.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) l₁ l₂)
but is expected to have type
  forall {α : Type.{u1}} (l₁ : Filter.{u1} α) (l₂ : Filter.{u1} α) [_inst_2 : CountableInterFilter.{u1} α l₁] [_inst_3 : CountableInterFilter.{u1} α l₂], CountableInterFilter.{u1} α (HasSup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (CompleteLattice.toLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) l₁ l₂)
Case conversion may be inaccurate. Consider using '#align countable_Inter_filter_sup countableInterFilter_supₓ'. -/
/-- Supremum of two `countable_Inter_filter`s is a `countable_Inter_filter`. -/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) :=
  by
  refine' ⟨fun S hSc hS => ⟨_, _⟩⟩ <;> refine' (countable_interₛ_mem hSc).2 fun s hs => _
  exacts[(hS s hs).1, (hS s hs).2]
#align countable_Inter_filter_sup countableInterFilter_sup

