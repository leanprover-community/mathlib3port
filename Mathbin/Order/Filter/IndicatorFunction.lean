/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.indicator_function
! leanprover-community/mathlib commit 4d392a6c9c4539cbeca399b3ee0afea398fbd2eb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Order.Filter.AtTopBot

/-!
# Indicator function and filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Properties of indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/


variable {α β M E : Type _}

open Set Filter Classical

open Filter Classical

section Zero

variable [Zero M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

/- warning: indicator_eventually_eq -> indicator_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> M} {g : α -> M} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, u2} α M (Inf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l (Filter.principal.{u1} α s)) f g) -> (Filter.EventuallyEq.{u1, 0} α Prop l s t) -> (Filter.EventuallyEq.{u1, u2} α M l (Set.indicator.{u1, u2} α M _inst_1 s f) (Set.indicator.{u1, u2} α M _inst_1 t g))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> M} {g : α -> M} {l : Filter.{u2} α}, (Filter.EventuallyEq.{u2, u1} α M (Inf.inf.{u2} (Filter.{u2} α) (Filter.instInfFilter.{u2} α) l (Filter.principal.{u2} α s)) f g) -> (Filter.EventuallyEq.{u2, 0} α Prop l s t) -> (Filter.EventuallyEq.{u2, u1} α M l (Set.indicator.{u2, u1} α M _inst_1 s f) (Set.indicator.{u2, u1} α M _inst_1 t g))
Case conversion may be inaccurate. Consider using '#align indicator_eventually_eq indicator_eventuallyEqₓ'. -/
theorem indicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t) :
    indicator s f =ᶠ[l] indicator t g :=
  (eventually_inf_principal.1 hf).mp <|
    hs.mem_iff.mono fun x hst hfg =>
      by_cases (fun hxs : x ∈ s => by simp only [*, hst.1 hxs, indicator_of_mem]) fun hxs => by
        simp only [indicator_of_not_mem hxs, indicator_of_not_mem (mt hst.2 hxs)]
#align indicator_eventually_eq indicator_eventuallyEq

end Zero

section AddMonoid

variable [AddMonoid M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

/- warning: indicator_union_eventually_eq -> indicator_union_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddMonoid.{u2} M] {s : Set.{u1} α} {t : Set.{u1} α} {f : α -> M} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (a : α) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))) l) -> (Filter.EventuallyEq.{u1, u2} α M l (Set.indicator.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) f) (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> M) (α -> M) (α -> M) (instHAdd.{max u1 u2} (α -> M) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1)))) (Set.indicator.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1)) s f) (Set.indicator.{u1, u2} α M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_1)) t f)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : AddMonoid.{u1} M] {s : Set.{u2} α} {t : Set.{u2} α} {f : α -> M} {l : Filter.{u2} α}, (Filter.Eventually.{u2} α (fun (a : α) => Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t))) l) -> (Filter.EventuallyEq.{u2, u1} α M l (Set.indicator.{u2, u1} α M (AddMonoid.toZero.{u1} M _inst_1) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t) f) (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHAdd.{max u2 u1} (α -> M) (Pi.instAdd.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_1)))) (Set.indicator.{u2, u1} α M (AddMonoid.toZero.{u1} M _inst_1) s f) (Set.indicator.{u2, u1} α M (AddMonoid.toZero.{u1} M _inst_1) t f)))
Case conversion may be inaccurate. Consider using '#align indicator_union_eventually_eq indicator_union_eventuallyEqₓ'. -/
theorem indicator_union_eventuallyEq (h : ∀ᶠ a in l, a ∉ s ∩ t) :
    indicator (s ∪ t) f =ᶠ[l] indicator s f + indicator t f :=
  h.mono fun a ha => indicator_union_of_not_mem_inter ha _
#align indicator_union_eventually_eq indicator_union_eventuallyEq

end AddMonoid

section Order

variable [Zero β] [Preorder β] {s t : Set α} {f g : α → β} {a : α} {l : Filter α}

/- warning: indicator_eventually_le_indicator -> indicator_eventuallyLE_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u2} β] [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {f : α -> β} {g : α -> β} {l : Filter.{u1} α}, (Filter.EventuallyLE.{u1, u2} α β (Preorder.toHasLe.{u2} β _inst_2) (Inf.inf.{u1} (Filter.{u1} α) (Filter.hasInf.{u1} α) l (Filter.principal.{u1} α s)) f g) -> (Filter.EventuallyLE.{u1, u2} α β (Preorder.toHasLe.{u2} β _inst_2) l (Set.indicator.{u1, u2} α β _inst_1 s f) (Set.indicator.{u1, u2} α β _inst_1 s g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u1} β] [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {f : α -> β} {g : α -> β} {l : Filter.{u2} α}, (Filter.EventuallyLE.{u2, u1} α β (Preorder.toLE.{u1} β _inst_2) (Inf.inf.{u2} (Filter.{u2} α) (Filter.instInfFilter.{u2} α) l (Filter.principal.{u2} α s)) f g) -> (Filter.EventuallyLE.{u2, u1} α β (Preorder.toLE.{u1} β _inst_2) l (Set.indicator.{u2, u1} α β _inst_1 s f) (Set.indicator.{u2, u1} α β _inst_1 s g))
Case conversion may be inaccurate. Consider using '#align indicator_eventually_le_indicator indicator_eventuallyLE_indicatorₓ'. -/
theorem indicator_eventuallyLE_indicator (h : f ≤ᶠ[l ⊓ 𝓟 s] g) :
    indicator s f ≤ᶠ[l] indicator s g :=
  (eventually_inf_principal.1 h).mono fun a h => indicator_rel_indicator le_rfl h
#align indicator_eventually_le_indicator indicator_eventuallyLE_indicator

end Order

/- warning: monotone.tendsto_indicator -> Monotone.tendsto_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Preorder.{u3} ι] [_inst_2 : Zero.{u2} β] (s : ι -> (Set.{u1} α)), (Monotone.{u3, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) s) -> (forall (f : α -> β) (a : α), Filter.Tendsto.{u3, u2} ι β (fun (i : ι) => Set.indicator.{u1, u2} α β _inst_2 (s i) f a) (Filter.atTop.{u3} ι _inst_1) (Pure.pure.{u2, u2} Filter.{u2} Filter.hasPure.{u2} β (Set.indicator.{u1, u2} α β _inst_2 (Set.iUnion.{u1, succ u3} α ι (fun (i : ι) => s i)) f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Preorder.{u3} ι] [_inst_2 : Zero.{u2} β] (s : ι -> (Set.{u1} α)), (Monotone.{u3, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s) -> (forall (f : α -> β) (a : α), Filter.Tendsto.{u3, u2} ι β (fun (i : ι) => Set.indicator.{u1, u2} α β _inst_2 (s i) f a) (Filter.atTop.{u3} ι _inst_1) (Pure.pure.{u2, u2} Filter.{u2} Filter.instPureFilter.{u2} β (Set.indicator.{u1, u2} α β _inst_2 (Set.iUnion.{u1, succ u3} α ι (fun (i : ι) => s i)) f a)))
Case conversion may be inaccurate. Consider using '#align monotone.tendsto_indicator Monotone.tendsto_indicatorₓ'. -/
theorem Monotone.tendsto_indicator {ι} [Preorder ι] [Zero β] (s : ι → Set α) (hs : Monotone s)
    (f : α → β) (a : α) :
    Tendsto (fun i => indicator (s i) f a) atTop (pure <| indicator (⋃ i, s i) f a) :=
  by
  by_cases h : ∃ i, a ∈ s i
  · rcases h with ⟨i, hi⟩
    refine' tendsto_pure.2 ((eventually_ge_at_top i).mono fun n hn => _)
    rw [indicator_of_mem (hs hn hi) _, indicator_of_mem ((subset_Union _ _) hi) _]
  · rw [not_exists] at h
    simp only [indicator_of_not_mem (h _)]
    convert tendsto_const_pure
    apply indicator_of_not_mem; simpa only [not_exists, mem_Union]
#align monotone.tendsto_indicator Monotone.tendsto_indicator

/- warning: antitone.tendsto_indicator -> Antitone.tendsto_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Preorder.{u3} ι] [_inst_2 : Zero.{u2} β] (s : ι -> (Set.{u1} α)), (Antitone.{u3, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) s) -> (forall (f : α -> β) (a : α), Filter.Tendsto.{u3, u2} ι β (fun (i : ι) => Set.indicator.{u1, u2} α β _inst_2 (s i) f a) (Filter.atTop.{u3} ι _inst_1) (Pure.pure.{u2, u2} Filter.{u2} Filter.hasPure.{u2} β (Set.indicator.{u1, u2} α β _inst_2 (Set.iInter.{u1, succ u3} α ι (fun (i : ι) => s i)) f a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Preorder.{u3} ι] [_inst_2 : Zero.{u2} β] (s : ι -> (Set.{u1} α)), (Antitone.{u3, u1} ι (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) s) -> (forall (f : α -> β) (a : α), Filter.Tendsto.{u3, u2} ι β (fun (i : ι) => Set.indicator.{u1, u2} α β _inst_2 (s i) f a) (Filter.atTop.{u3} ι _inst_1) (Pure.pure.{u2, u2} Filter.{u2} Filter.instPureFilter.{u2} β (Set.indicator.{u1, u2} α β _inst_2 (Set.iInter.{u1, succ u3} α ι (fun (i : ι) => s i)) f a)))
Case conversion may be inaccurate. Consider using '#align antitone.tendsto_indicator Antitone.tendsto_indicatorₓ'. -/
theorem Antitone.tendsto_indicator {ι} [Preorder ι] [Zero β] (s : ι → Set α) (hs : Antitone s)
    (f : α → β) (a : α) :
    Tendsto (fun i => indicator (s i) f a) atTop (pure <| indicator (⋂ i, s i) f a) :=
  by
  by_cases h : ∃ i, a ∉ s i
  · rcases h with ⟨i, hi⟩
    refine' tendsto_pure.2 ((eventually_ge_at_top i).mono fun n hn => _)
    rw [indicator_of_not_mem _ _, indicator_of_not_mem _ _]
    · simp only [mem_Inter, not_forall]; exact ⟨i, hi⟩
    · intro h; have := hs hn h; contradiction
  · push_neg  at h
    simp only [indicator_of_mem, h, mem_Inter.2 h, tendsto_const_pure]
#align antitone.tendsto_indicator Antitone.tendsto_indicator

#print tendsto_indicator_biUnion_finset /-
theorem tendsto_indicator_biUnion_finset {ι} [Zero β] (s : ι → Set α) (f : α → β) (a : α) :
    Tendsto (fun n : Finset ι => indicator (⋃ i ∈ n, s i) f a) atTop
      (pure <| indicator (iUnion s) f a) :=
  by
  rw [Union_eq_Union_finset s]
  refine' Monotone.tendsto_indicator (fun n : Finset ι => ⋃ i ∈ n, s i) _ f a
  exact fun t₁ t₂ => bUnion_subset_bUnion_left
#align tendsto_indicator_bUnion_finset tendsto_indicator_biUnion_finset
-/

#print Filter.EventuallyEq.support /-
theorem Filter.EventuallyEq.support [Zero β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    Function.support f =ᶠ[l] Function.support g :=
  by
  filter_upwards [h]with x hx
  rw [eq_iff_iff]
  change f x ≠ 0 ↔ g x ≠ 0
  rw [hx]
#align filter.eventually_eq.support Filter.EventuallyEq.support
-/

#print Filter.EventuallyEq.indicator /-
theorem Filter.EventuallyEq.indicator [Zero β] {l : Filter α} {f g : α → β} {s : Set α}
    (hfg : f =ᶠ[l] g) : s.indicator f =ᶠ[l] s.indicator g :=
  by
  filter_upwards [hfg]with x hx
  by_cases x ∈ s
  · rwa [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_not_mem h, indicator_of_not_mem h]
#align filter.eventually_eq.indicator Filter.EventuallyEq.indicator
-/

#print Filter.EventuallyEq.indicator_zero /-
theorem Filter.EventuallyEq.indicator_zero [Zero β] {l : Filter α} {f : α → β} {s : Set α}
    (hf : f =ᶠ[l] 0) : s.indicator f =ᶠ[l] 0 :=
  by
  refine' hf.indicator.trans _
  rw [indicator_zero']
#align filter.eventually_eq.indicator_zero Filter.EventuallyEq.indicator_zero
-/

