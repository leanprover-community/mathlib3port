/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Rémy Degenne

! This file was ported from Lean 3 source module order.liminf_limsup
! leanprover-community/mathlib commit 3e32bc908f617039c74c06ea9a897e30c30803c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Cofinite
import Mathbin.Order.Hom.CompleteLattice

/-!
# liminfs and limsups of functions and filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Defines the Liminf/Limsup of a function taking values in a conditionally complete lattice, with
respect to an arbitrary filter.

We define `Limsup f` (`Liminf f`) where `f` is a filter taking values in a conditionally complete
lattice. `Limsup f` is the smallest element `a` such that, eventually, `u ≤ a` (and vice versa for
`Liminf f`). To work with the Limsup along a function `u` use `Limsup (map u f)`.

Usually, one defines the Limsup as `Inf (Sup s)` where the Inf is taken over all sets in the filter.
For instance, in ℕ along a function `u`, this is `Inf_n (Sup_{k ≥ n} u k)` (and the latter quantity
decreases with `n`, so this is in fact a limit.). There is however a difficulty: it is well possible
that `u` is not bounded on the whole space, only eventually (think of `Limsup (λx, 1/x)` on ℝ. Then
there is no guarantee that the quantity above really decreases (the value of the `Sup` beforehand is
not really well defined, as one can not use ∞), so that the Inf could be anything. So one can not
use this `Inf Sup ...` definition in conditionally complete lattices, and one has to use a less
tractable definition.

In conditionally complete lattices, the definition is only useful for filters which are eventually
bounded above (otherwise, the Limsup would morally be +∞, which does not belong to the space) and
which are frequently bounded below (otherwise, the Limsup would morally be -∞, which is not in the
space either). We start with definitions of these concepts for arbitrary filters, before turning to
the definitions of Limsup and Liminf.

In complete lattices, however, it coincides with the `Inf Sup` definition.
-/


open Filter Set

open Filter

variable {α β γ ι : Type _}

namespace Filter

section Relation

#print Filter.IsBounded /-
/-- `f.is_bounded (≺)`: the filter `f` is eventually bounded w.r.t. the relation `≺`, i.e.
eventually, it is bounded by some uniform bound.
`r` will be usually instantiated with `≤` or `≥`. -/
def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b
#align filter.is_bounded Filter.IsBounded
-/

#print Filter.IsBoundedUnder /-
/-- `f.is_bounded_under (≺) u`: the image of the filter `f` under `u` is eventually bounded w.r.t.
the relation `≺`, i.e. eventually, it is bounded by some uniform bound. -/
def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsBounded r
#align filter.is_bounded_under Filter.IsBoundedUnder
-/

variable {r : α → α → Prop} {f g : Filter α}

/- warning: filter.is_bounded_iff -> Filter.isBounded_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α}, Iff (Filter.IsBounded.{u1} α r f) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (Filter.sets.{u1} α f)) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (Filter.sets.{u1} α f)) => Exists.{succ u1} α (fun (b : α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (setOf.{u1} α (fun (x : α) => r x b))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α}, Iff (Filter.IsBounded.{u1} α r f) (Exists.{succ u1} (Set.{u1} α) (fun (s : Set.{u1} α) => And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (Filter.sets.{u1} α f)) (Exists.{succ u1} α (fun (b : α) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (setOf.{u1} α (fun (x : α) => r x b))))))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_iff Filter.isBounded_iffₓ'. -/
/-- `f` is eventually bounded if and only if, there exists an admissible set on which it is
bounded. -/
theorem isBounded_iff : f.IsBounded r ↔ ∃ s ∈ f.sets, ∃ b, s ⊆ { x | r x b } :=
  Iff.intro (fun ⟨b, hb⟩ => ⟨{ a | r a b }, hb, b, Subset.refl _⟩) fun ⟨s, hs, b, hb⟩ =>
    ⟨b, mem_of_superset hs hb⟩
#align filter.is_bounded_iff Filter.isBounded_iff

#print Filter.isBoundedUnder_of /-
/-- A bounded function `u` is in particular eventually bounded. -/
theorem isBoundedUnder_of {f : Filter β} {u : β → α} : (∃ b, ∀ x, r (u x) b) → f.IsBoundedUnder r u
  | ⟨b, hb⟩ => ⟨b, show ∀ᶠ x in f, r (u x) b from eventually_of_forall hb⟩
#align filter.is_bounded_under_of Filter.isBoundedUnder_of
-/

/- warning: filter.is_bounded_bot -> Filter.isBounded_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsBounded.{u1} α r (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Nonempty.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsBounded.{u1} α r (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Nonempty.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_bot Filter.isBounded_botₓ'. -/
theorem isBounded_bot : IsBounded r ⊥ ↔ Nonempty α := by simp [is_bounded, exists_true_iff_nonempty]
#align filter.is_bounded_bot Filter.isBounded_bot

/- warning: filter.is_bounded_top -> Filter.isBounded_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsBounded.{u1} α r (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Exists.{succ u1} α (fun (t : α) => forall (x : α), r x t))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsBounded.{u1} α r (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Exists.{succ u1} α (fun (t : α) => forall (x : α), r x t))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_top Filter.isBounded_topₓ'. -/
theorem isBounded_top : IsBounded r ⊤ ↔ ∃ t, ∀ x, r x t := by simp [is_bounded, eq_univ_iff_forall]
#align filter.is_bounded_top Filter.isBounded_top

#print Filter.isBounded_principal /-
theorem isBounded_principal (s : Set α) : IsBounded r (𝓟 s) ↔ ∃ t, ∀ x ∈ s, r x t := by
  simp [is_bounded, subset_def]
#align filter.is_bounded_principal Filter.isBounded_principal
-/

/- warning: filter.is_bounded_sup -> Filter.isBounded_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α} [_inst_1 : IsTrans.{u1} α r], (forall (b₁ : α) (b₂ : α), Exists.{succ u1} α (fun (b : α) => And (r b₁ b) (r b₂ b))) -> (Filter.IsBounded.{u1} α r f) -> (Filter.IsBounded.{u1} α r g) -> (Filter.IsBounded.{u1} α r (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α))))) f g))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α} [_inst_1 : IsTrans.{u1} α r], (forall (b₁ : α) (b₂ : α), Exists.{succ u1} α (fun (b : α) => And (r b₁ b) (r b₂ b))) -> (Filter.IsBounded.{u1} α r f) -> (Filter.IsBounded.{u1} α r g) -> (Filter.IsBounded.{u1} α r (Sup.sup.{u1} (Filter.{u1} α) (SemilatticeSup.toSup.{u1} (Filter.{u1} α) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α))))) f g))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_sup Filter.isBounded_supₓ'. -/
theorem isBounded_sup [IsTrans α r] (hr : ∀ b₁ b₂, ∃ b, r b₁ b ∧ r b₂ b) :
    IsBounded r f → IsBounded r g → IsBounded r (f ⊔ g)
  | ⟨b₁, h₁⟩, ⟨b₂, h₂⟩ =>
    let ⟨b, rb₁b, rb₂b⟩ := hr b₁ b₂
    ⟨b, eventually_sup.mpr ⟨h₁.mono fun x h => trans h rb₁b, h₂.mono fun x h => trans h rb₂b⟩⟩
#align filter.is_bounded_sup Filter.isBounded_sup

/- warning: filter.is_bounded.mono -> Filter.IsBounded.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) -> (Filter.IsBounded.{u1} α r g) -> (Filter.IsBounded.{u1} α r f)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) -> (Filter.IsBounded.{u1} α r g) -> (Filter.IsBounded.{u1} α r f)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded.mono Filter.IsBounded.monoₓ'. -/
theorem IsBounded.mono (h : f ≤ g) : IsBounded r g → IsBounded r f
  | ⟨b, hb⟩ => ⟨b, h hb⟩
#align filter.is_bounded.mono Filter.IsBounded.mono

/- warning: filter.is_bounded_under.mono -> Filter.IsBoundedUnder.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {f : Filter.{u2} β} {g : Filter.{u2} β} {u : β -> α}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toHasLe.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) f g) -> (Filter.IsBoundedUnder.{u1, u2} α β r g u) -> (Filter.IsBoundedUnder.{u1, u2} α β r f u)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {f : Filter.{u2} β} {g : Filter.{u2} β} {u : β -> α}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) f g) -> (Filter.IsBoundedUnder.{u1, u2} α β r g u) -> (Filter.IsBoundedUnder.{u1, u2} α β r f u)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.mono Filter.IsBoundedUnder.monoₓ'. -/
theorem IsBoundedUnder.mono {f g : Filter β} {u : β → α} (h : f ≤ g) :
    g.IsBoundedUnder r u → f.IsBoundedUnder r u := fun hg => hg.mono (map_mono h)
#align filter.is_bounded_under.mono Filter.IsBoundedUnder.mono

/- warning: filter.is_bounded_under.mono_le -> Filter.IsBoundedUnder.mono_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {l : Filter.{u1} α} {u : α -> β} {v : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_1)) l u) -> (Filter.EventuallyLE.{u1, u2} α β (Preorder.toHasLe.{u2} β _inst_1) l v u) -> (Filter.IsBoundedUnder.{u2, u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_1)) l v)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {l : Filter.{u1} α} {u : α -> β} {v : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.747 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.749 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.747 x._@.Mathlib.Order.LiminfLimsup._hyg.749) l u) -> (Filter.EventuallyLE.{u1, u2} α β (Preorder.toLE.{u2} β _inst_1) l v u) -> (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.771 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.773 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.771 x._@.Mathlib.Order.LiminfLimsup._hyg.773) l v)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.mono_le Filter.IsBoundedUnder.mono_leₓ'. -/
theorem IsBoundedUnder.mono_le [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≤ ·) l u) (hv : v ≤ᶠ[l] u) : IsBoundedUnder (· ≤ ·) l v :=
  hu.imp fun b hb => (eventually_map.1 hb).mp <| hv.mono fun x => le_trans
#align filter.is_bounded_under.mono_le Filter.IsBoundedUnder.mono_le

/- warning: filter.is_bounded_under.mono_ge -> Filter.IsBoundedUnder.mono_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {l : Filter.{u1} α} {u : α -> β} {v : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β _inst_1)) l u) -> (Filter.EventuallyLE.{u1, u2} α β (Preorder.toHasLe.{u2} β _inst_1) l u v) -> (Filter.IsBoundedUnder.{u2, u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β _inst_1)) l v)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {l : Filter.{u1} α} {u : α -> β} {v : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.841 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.843 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.841 x._@.Mathlib.Order.LiminfLimsup._hyg.843) l u) -> (Filter.EventuallyLE.{u1, u2} α β (Preorder.toLE.{u2} β _inst_1) l u v) -> (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.865 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.867 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.865 x._@.Mathlib.Order.LiminfLimsup._hyg.867) l v)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.mono_ge Filter.IsBoundedUnder.mono_geₓ'. -/
theorem IsBoundedUnder.mono_ge [Preorder β] {l : Filter α} {u v : α → β}
    (hu : IsBoundedUnder (· ≥ ·) l u) (hv : u ≤ᶠ[l] v) : IsBoundedUnder (· ≥ ·) l v :=
  @IsBoundedUnder.mono_le α βᵒᵈ _ _ _ _ hu hv
#align filter.is_bounded_under.mono_ge Filter.IsBoundedUnder.mono_ge

/- warning: filter.is_bounded_under_const -> Filter.isBoundedUnder_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} [_inst_1 : IsRefl.{u1} α r] {l : Filter.{u2} β} {a : α}, Filter.IsBoundedUnder.{u1, u2} α β r l (fun (_x : β) => a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsRefl.{u2} α r] {l : Filter.{u1} β} {a : α}, Filter.IsBoundedUnder.{u2, u1} α β r l (fun (_x : β) => a)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_const Filter.isBoundedUnder_constₓ'. -/
theorem isBoundedUnder_const [IsRefl α r] {l : Filter β} {a : α} : IsBoundedUnder r l fun _ => a :=
  ⟨a, eventually_map.2 <| eventually_of_forall fun _ => refl _⟩
#align filter.is_bounded_under_const Filter.isBoundedUnder_const

/- warning: filter.is_bounded.is_bounded_under -> Filter.IsBounded.isBoundedUnder is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {f : Filter.{u1} α} {q : β -> β -> Prop} {u : α -> β}, (forall (a₀ : α) (a₁ : α), (r a₀ a₁) -> (q (u a₀) (u a₁))) -> (Filter.IsBounded.{u1} α r f) -> (Filter.IsBoundedUnder.{u2, u1} β α q f u)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u2} α} {q : β -> β -> Prop} {u : α -> β}, (forall (a₀ : α) (a₁ : α), (r a₀ a₁) -> (q (u a₀) (u a₁))) -> (Filter.IsBounded.{u2} α r f) -> (Filter.IsBoundedUnder.{u1, u2} β α q f u)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded.is_bounded_under Filter.IsBounded.isBoundedUnderₓ'. -/
theorem IsBounded.isBoundedUnder {q : β → β → Prop} {u : α → β}
    (hf : ∀ a₀ a₁, r a₀ a₁ → q (u a₀) (u a₁)) : f.IsBounded r → f.IsBoundedUnder q u
  | ⟨b, h⟩ => ⟨u b, show ∀ᶠ x in f, q (u x) (u b) from h.mono fun x => hf x b⟩
#align filter.is_bounded.is_bounded_under Filter.IsBounded.isBoundedUnder

/- warning: filter.not_is_bounded_under_of_tendsto_at_top -> Filter.not_isBoundedUnder_of_tendsto_atTop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : NoMaxOrder.{u2} β (Preorder.toHasLt.{u2} β _inst_1)] {f : α -> β} {l : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α l], (Filter.Tendsto.{u1, u2} α β f l (Filter.atTop.{u2} β _inst_1)) -> (Not (Filter.IsBoundedUnder.{u2, u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_1)) l f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : NoMaxOrder.{u2} β (Preorder.toLT.{u2} β _inst_1)] {f : α -> β} {l : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α l], (Filter.Tendsto.{u1, u2} α β f l (Filter.atTop.{u2} β _inst_1)) -> (Not (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1086 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.1088 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.1086 x._@.Mathlib.Order.LiminfLimsup._hyg.1088) l f))
Case conversion may be inaccurate. Consider using '#align filter.not_is_bounded_under_of_tendsto_at_top Filter.not_isBoundedUnder_of_tendsto_atTopₓ'. -/
theorem not_isBoundedUnder_of_tendsto_atTop [Preorder β] [NoMaxOrder β] {f : α → β} {l : Filter α}
    [l.ne_bot] (hf : Tendsto f l atTop) : ¬IsBoundedUnder (· ≤ ·) l f :=
  by
  rintro ⟨b, hb⟩
  rw [eventually_map] at hb
  obtain ⟨b', h⟩ := exists_gt b
  have hb' := (tendsto_at_top.mp hf) b'
  have : { x : α | f x ≤ b } ∩ { x : α | b' ≤ f x } = ∅ :=
    eq_empty_of_subset_empty fun x hx => (not_le_of_lt h) (le_trans hx.2 hx.1)
  exact (nonempty_of_mem (hb.and hb')).ne_empty this
#align filter.not_is_bounded_under_of_tendsto_at_top Filter.not_isBoundedUnder_of_tendsto_atTop

/- warning: filter.not_is_bounded_under_of_tendsto_at_bot -> Filter.not_isBoundedUnder_of_tendsto_atBot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : NoMinOrder.{u2} β (Preorder.toHasLt.{u2} β _inst_1)] {f : α -> β} {l : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α l], (Filter.Tendsto.{u1, u2} α β f l (Filter.atBot.{u2} β _inst_1)) -> (Not (Filter.IsBoundedUnder.{u2, u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β _inst_1)) l f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : NoMinOrder.{u2} β (Preorder.toLT.{u2} β _inst_1)] {f : α -> β} {l : Filter.{u1} α} [_inst_3 : Filter.NeBot.{u1} α l], (Filter.Tendsto.{u1, u2} α β f l (Filter.atBot.{u2} β _inst_1)) -> (Not (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1278 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.1280 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.1278 x._@.Mathlib.Order.LiminfLimsup._hyg.1280) l f))
Case conversion may be inaccurate. Consider using '#align filter.not_is_bounded_under_of_tendsto_at_bot Filter.not_isBoundedUnder_of_tendsto_atBotₓ'. -/
theorem not_isBoundedUnder_of_tendsto_atBot [Preorder β] [NoMinOrder β] {f : α → β} {l : Filter α}
    [l.ne_bot] (hf : Tendsto f l atBot) : ¬IsBoundedUnder (· ≥ ·) l f :=
  @not_isBoundedUnder_of_tendsto_atTop α βᵒᵈ _ _ _ _ _ hf
#align filter.not_is_bounded_under_of_tendsto_at_bot Filter.not_isBoundedUnder_of_tendsto_atBot

/- warning: filter.is_bounded_under.bdd_above_range_of_cofinite -> Filter.IsBoundedUnder.bddAbove_range_of_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u2} β] {f : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_1)))) (Filter.cofinite.{u1} α) f) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_1)) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u2} β] {f : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1326 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.1328 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.1326 x._@.Mathlib.Order.LiminfLimsup._hyg.1328) (Filter.cofinite.{u1} α) f) -> (BddAbove.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_1)) (Set.range.{u2, succ u1} β α f))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.bdd_above_range_of_cofinite Filter.IsBoundedUnder.bddAbove_range_of_cofiniteₓ'. -/
theorem IsBoundedUnder.bddAbove_range_of_cofinite [SemilatticeSup β] {f : α → β}
    (hf : IsBoundedUnder (· ≤ ·) cofinite f) : BddAbove (range f) :=
  by
  rcases hf with ⟨b, hb⟩
  haveI : Nonempty β := ⟨b⟩
  rw [← image_univ, ← union_compl_self { x | f x ≤ b }, image_union, bddAbove_union]
  exact ⟨⟨b, ball_image_iff.2 fun x => id⟩, (hb.image f).BddAbove⟩
#align filter.is_bounded_under.bdd_above_range_of_cofinite Filter.IsBoundedUnder.bddAbove_range_of_cofinite

/- warning: filter.is_bounded_under.bdd_below_range_of_cofinite -> Filter.IsBoundedUnder.bddBelow_range_of_cofinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u2} β] {f : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_1)))) (Filter.cofinite.{u1} α) f) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_1)) (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u2} β] {f : α -> β}, (Filter.IsBoundedUnder.{u2, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1460 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.1462 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.1460 x._@.Mathlib.Order.LiminfLimsup._hyg.1462) (Filter.cofinite.{u1} α) f) -> (BddBelow.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_1)) (Set.range.{u2, succ u1} β α f))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.bdd_below_range_of_cofinite Filter.IsBoundedUnder.bddBelow_range_of_cofiniteₓ'. -/
theorem IsBoundedUnder.bddBelow_range_of_cofinite [SemilatticeInf β] {f : α → β}
    (hf : IsBoundedUnder (· ≥ ·) cofinite f) : BddBelow (range f) :=
  @IsBoundedUnder.bddAbove_range_of_cofinite α βᵒᵈ _ _ hf
#align filter.is_bounded_under.bdd_below_range_of_cofinite Filter.IsBoundedUnder.bddBelow_range_of_cofinite

/- warning: filter.is_bounded_under.bdd_above_range -> Filter.IsBoundedUnder.bddAbove_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} β] {f : Nat -> β}, (Filter.IsBoundedUnder.{u1, 0} β Nat (LE.le.{u1} β (Preorder.toHasLe.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1)) (Set.range.{u1, 1} β Nat f))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u1} β] {f : Nat -> β}, (Filter.IsBoundedUnder.{u1, 0} β Nat (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1516 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.1518 : β) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.1516 x._@.Mathlib.Order.LiminfLimsup._hyg.1518) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f) -> (BddAbove.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_1)) (Set.range.{u1, 1} β Nat f))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.bdd_above_range Filter.IsBoundedUnder.bddAbove_rangeₓ'. -/
theorem IsBoundedUnder.bddAbove_range [SemilatticeSup β] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≤ ·) atTop f) : BddAbove (range f) :=
  by
  rw [← Nat.cofinite_eq_atTop] at hf
  exact hf.bdd_above_range_of_cofinite
#align filter.is_bounded_under.bdd_above_range Filter.IsBoundedUnder.bddAbove_range

/- warning: filter.is_bounded_under.bdd_below_range -> Filter.IsBoundedUnder.bddBelow_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} β] {f : Nat -> β}, (Filter.IsBoundedUnder.{u1, 0} β Nat (GE.ge.{u1} β (Preorder.toHasLe.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_1)))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_1)) (Set.range.{u1, 1} β Nat f))
but is expected to have type
  forall {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u1} β] {f : Nat -> β}, (Filter.IsBoundedUnder.{u1, 0} β Nat (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1600 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.1602 : β) => GE.ge.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.1600 x._@.Mathlib.Order.LiminfLimsup._hyg.1602) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f) -> (BddBelow.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_1)) (Set.range.{u1, 1} β Nat f))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.bdd_below_range Filter.IsBoundedUnder.bddBelow_rangeₓ'. -/
theorem IsBoundedUnder.bddBelow_range [SemilatticeInf β] {f : ℕ → β}
    (hf : IsBoundedUnder (· ≥ ·) atTop f) : BddBelow (range f) :=
  @IsBoundedUnder.bddAbove_range βᵒᵈ _ _ hf
#align filter.is_bounded_under.bdd_below_range Filter.IsBoundedUnder.bddBelow_range

#print Filter.IsCobounded /-
/-- `is_cobounded (≺) f` states that the filter `f` does not tend to infinity w.r.t. `≺`. This is
also called frequently bounded. Will be usually instantiated with `≤` or `≥`.

There is a subtlety in this definition: we want `f.is_cobounded` to hold for any `f` in the case of
complete lattices. This will be relevant to deduce theorems on complete lattices from their
versions on conditionally complete lattices with additional assumptions. We have to be careful in
the edge case of the trivial filter containing the empty set: the other natural definition
  `¬ ∀ a, ∀ᶠ n in f, a ≤ n`
would not work as well in this case.
-/
def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a
#align filter.is_cobounded Filter.IsCobounded
-/

#print Filter.IsCoboundedUnder /-
/-- `is_cobounded_under (≺) f u` states that the image of the filter `f` under the map `u` does not
tend to infinity w.r.t. `≺`. This is also called frequently bounded. Will be usually instantiated
with `≤` or `≥`. -/
def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsCobounded r
#align filter.is_cobounded_under Filter.IsCoboundedUnder
-/

/- warning: filter.is_cobounded.mk -> Filter.IsCobounded.mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} [_inst_1 : IsTrans.{u1} α r] (a : α), (forall (s : Set.{u1} α), (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => r a x)))) -> (Filter.IsCobounded.{u1} α r f)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} [_inst_1 : IsTrans.{u1} α r] (a : α), (forall (s : Set.{u1} α), (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (r a x)))) -> (Filter.IsCobounded.{u1} α r f)
Case conversion may be inaccurate. Consider using '#align filter.is_cobounded.mk Filter.IsCobounded.mkₓ'. -/
/-- To check that a filter is frequently bounded, it suffices to have a witness
which bounds `f` at some point for every admissible set.

This is only an implication, as the other direction is wrong for the trivial filter.-/
theorem IsCobounded.mk [IsTrans α r] (a : α) (h : ∀ s ∈ f, ∃ x ∈ s, r a x) : f.IsCobounded r :=
  ⟨a, fun y s =>
    let ⟨x, h₁, h₂⟩ := h _ s
    trans h₂ h₁⟩
#align filter.is_cobounded.mk Filter.IsCobounded.mk

#print Filter.IsBounded.isCobounded_flip /-
/-- A filter which is eventually bounded is in particular frequently bounded (in the opposite
direction). At least if the filter is not trivial. -/
theorem IsBounded.isCobounded_flip [IsTrans α r] [NeBot f] : f.IsBounded r → f.IsCobounded (flip r)
  | ⟨a, ha⟩ =>
    ⟨a, fun b hb =>
      let ⟨x, rxa, rbx⟩ := (ha.And hb).exists
      show r b a from trans rbx rxa⟩
#align filter.is_bounded.is_cobounded_flip Filter.IsBounded.isCobounded_flip
-/

/- warning: filter.is_bounded.is_cobounded_ge -> Filter.IsBounded.isCobounded_ge is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : Filter.NeBot.{u1} α f], (Filter.IsBounded.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f) -> (Filter.IsCobounded.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : Filter.NeBot.{u1} α f], (Filter.IsBounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1955 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.1957 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.1955 x._@.Mathlib.Order.LiminfLimsup._hyg.1957) f) -> (Filter.IsCobounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.1971 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.1973 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.1971 x._@.Mathlib.Order.LiminfLimsup._hyg.1973) f)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded.is_cobounded_ge Filter.IsBounded.isCobounded_geₓ'. -/
theorem IsBounded.isCobounded_ge [Preorder α] [NeBot f] (h : f.IsBounded (· ≤ ·)) :
    f.IsCobounded (· ≥ ·) :=
  h.isCobounded_flip
#align filter.is_bounded.is_cobounded_ge Filter.IsBounded.isCobounded_ge

/- warning: filter.is_bounded.is_cobounded_le -> Filter.IsBounded.isCobounded_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : Filter.NeBot.{u1} α f], (Filter.IsBounded.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f) -> (Filter.IsCobounded.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f)
but is expected to have type
  forall {α : Type.{u1}} {f : Filter.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : Filter.NeBot.{u1} α f], (Filter.IsBounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2013 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2015 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2013 x._@.Mathlib.Order.LiminfLimsup._hyg.2015) f) -> (Filter.IsCobounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2029 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2031 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2029 x._@.Mathlib.Order.LiminfLimsup._hyg.2031) f)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded.is_cobounded_le Filter.IsBounded.isCobounded_leₓ'. -/
theorem IsBounded.isCobounded_le [Preorder α] [NeBot f] (h : f.IsBounded (· ≥ ·)) :
    f.IsCobounded (· ≤ ·) :=
  h.isCobounded_flip
#align filter.is_bounded.is_cobounded_le Filter.IsBounded.isCobounded_le

/- warning: filter.is_cobounded_bot -> Filter.isCobounded_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsCobounded.{u1} α r (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Exists.{succ u1} α (fun (b : α) => forall (x : α), r b x))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsCobounded.{u1} α r (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Exists.{succ u1} α (fun (b : α) => forall (x : α), r b x))
Case conversion may be inaccurate. Consider using '#align filter.is_cobounded_bot Filter.isCobounded_botₓ'. -/
theorem isCobounded_bot : IsCobounded r ⊥ ↔ ∃ b, ∀ x, r b x := by simp [is_cobounded]
#align filter.is_cobounded_bot Filter.isCobounded_bot

/- warning: filter.is_cobounded_top -> Filter.isCobounded_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsCobounded.{u1} α r (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Nonempty.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (Filter.IsCobounded.{u1} α r (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Nonempty.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align filter.is_cobounded_top Filter.isCobounded_topₓ'. -/
theorem isCobounded_top : IsCobounded r ⊤ ↔ Nonempty α := by
  simp (config := { contextual := true }) [is_cobounded, eq_univ_iff_forall,
    exists_true_iff_nonempty]
#align filter.is_cobounded_top Filter.isCobounded_top

#print Filter.isCobounded_principal /-
theorem isCobounded_principal (s : Set α) :
    (𝓟 s).IsCobounded r ↔ ∃ b, ∀ a, (∀ x ∈ s, r x a) → r b a := by simp [is_cobounded, subset_def]
#align filter.is_cobounded_principal Filter.isCobounded_principal
-/

/- warning: filter.is_cobounded.mono -> Filter.IsCobounded.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toHasLe.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.partialOrder.{u1} α))) f g) -> (Filter.IsCobounded.{u1} α r f) -> (Filter.IsCobounded.{u1} α r g)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {f : Filter.{u1} α} {g : Filter.{u1} α}, (LE.le.{u1} (Filter.{u1} α) (Preorder.toLE.{u1} (Filter.{u1} α) (PartialOrder.toPreorder.{u1} (Filter.{u1} α) (Filter.instPartialOrderFilter.{u1} α))) f g) -> (Filter.IsCobounded.{u1} α r f) -> (Filter.IsCobounded.{u1} α r g)
Case conversion may be inaccurate. Consider using '#align filter.is_cobounded.mono Filter.IsCobounded.monoₓ'. -/
theorem IsCobounded.mono (h : f ≤ g) : f.IsCobounded r → g.IsCobounded r
  | ⟨b, hb⟩ => ⟨b, fun a ha => hb a (h ha)⟩
#align filter.is_cobounded.mono Filter.IsCobounded.mono

end Relation

/- warning: filter.is_cobounded_le_of_bot -> Filter.isCobounded_le_of_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsCobounded.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsCobounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2280 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2282 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2280 x._@.Mathlib.Order.LiminfLimsup._hyg.2282) f
Case conversion may be inaccurate. Consider using '#align filter.is_cobounded_le_of_bot Filter.isCobounded_le_of_botₓ'. -/
theorem isCobounded_le_of_bot [Preorder α] [OrderBot α] {f : Filter α} : f.IsCobounded (· ≤ ·) :=
  ⟨⊥, fun a h => bot_le⟩
#align filter.is_cobounded_le_of_bot Filter.isCobounded_le_of_bot

/- warning: filter.is_cobounded_ge_of_top -> Filter.isCobounded_ge_of_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsCobounded.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsCobounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2322 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2324 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2322 x._@.Mathlib.Order.LiminfLimsup._hyg.2324) f
Case conversion may be inaccurate. Consider using '#align filter.is_cobounded_ge_of_top Filter.isCobounded_ge_of_topₓ'. -/
theorem isCobounded_ge_of_top [Preorder α] [OrderTop α] {f : Filter α} : f.IsCobounded (· ≥ ·) :=
  ⟨⊤, fun a h => le_top⟩
#align filter.is_cobounded_ge_of_top Filter.isCobounded_ge_of_top

/- warning: filter.is_bounded_le_of_top -> Filter.isBounded_le_of_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toHasLe.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsBounded.{u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsBounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2364 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2366 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2364 x._@.Mathlib.Order.LiminfLimsup._hyg.2366) f
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_le_of_top Filter.isBounded_le_of_topₓ'. -/
theorem isBounded_le_of_top [Preorder α] [OrderTop α] {f : Filter α} : f.IsBounded (· ≤ ·) :=
  ⟨⊤, eventually_of_forall fun _ => le_top⟩
#align filter.is_bounded_le_of_top Filter.isBounded_le_of_top

/- warning: filter.is_bounded_ge_of_bot -> Filter.isBounded_ge_of_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsBounded.{u1} α (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)] {f : Filter.{u1} α}, Filter.IsBounded.{u1} α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2405 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2407 : α) => GE.ge.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2405 x._@.Mathlib.Order.LiminfLimsup._hyg.2407) f
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_ge_of_bot Filter.isBounded_ge_of_botₓ'. -/
theorem isBounded_ge_of_bot [Preorder α] [OrderBot α] {f : Filter α} : f.IsBounded (· ≥ ·) :=
  ⟨⊥, eventually_of_forall fun _ => bot_le⟩
#align filter.is_bounded_ge_of_bot Filter.isBounded_ge_of_bot

/- warning: order_iso.is_bounded_under_le_comp -> OrderIso.isBoundedUnder_le_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α _inst_1) (Preorder.toHasLe.{u2} β _inst_2)) {l : Filter.{u3} γ} {u : γ -> α}, Iff (Filter.IsBoundedUnder.{u2, u3} β γ (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) l (fun (x : γ) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α _inst_1) (Preorder.toHasLe.{u2} β _inst_2)) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2))) e (u x))) (Filter.IsBoundedUnder.{u1, u3} α γ (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) l u)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) {l : Filter.{u1} γ} {u : γ -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} β γ (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2459 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.2461 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.LiminfLimsup._hyg.2459 x._@.Mathlib.Order.LiminfLimsup._hyg.2461) l (fun (x : γ) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) e (u x))) (Filter.IsBoundedUnder.{u3, u1} α γ (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2485 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2487 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2485 x._@.Mathlib.Order.LiminfLimsup._hyg.2487) l u)
Case conversion may be inaccurate. Consider using '#align order_iso.is_bounded_under_le_comp OrderIso.isBoundedUnder_le_compₓ'. -/
@[simp]
theorem OrderIso.isBoundedUnder_le_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≤ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≤ ·) l u :=
  e.Surjective.exists.trans <| exists_congr fun a => by simp only [eventually_map, e.le_iff_le]
#align order_iso.is_bounded_under_le_comp OrderIso.isBoundedUnder_le_comp

/- warning: order_iso.is_bounded_under_ge_comp -> OrderIso.isBoundedUnder_ge_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α _inst_1) (Preorder.toHasLe.{u2} β _inst_2)) {l : Filter.{u3} γ} {u : γ -> α}, Iff (Filter.IsBoundedUnder.{u2, u3} β γ (GE.ge.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) l (fun (x : γ) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β (Preorder.toHasLe.{u1} α _inst_1) (Preorder.toHasLe.{u2} β _inst_2)) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2))) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2))) e (u x))) (Filter.IsBoundedUnder.{u1, u3} α γ (GE.ge.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) l u)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u2} β] (e : OrderIso.{u3, u2} α β (Preorder.toLE.{u3} α _inst_1) (Preorder.toLE.{u2} β _inst_2)) {l : Filter.{u1} γ} {u : γ -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} β γ (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2546 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.2548 : β) => GE.ge.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.LiminfLimsup._hyg.2546 x._@.Mathlib.Order.LiminfLimsup._hyg.2548) l (fun (x : γ) => FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α (fun (_x : α) => β) (RelHomClass.toFunLike.{max u3 u2, u3, u2} (RelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302)) α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302) (RelIso.instRelHomClassRelIso.{u3, u2} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1285 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1287 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.Hom.Basic._hyg.1285 x._@.Mathlib.Order.Hom.Basic._hyg.1287) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1300 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1302 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_2) x._@.Mathlib.Order.Hom.Basic._hyg.1300 x._@.Mathlib.Order.Hom.Basic._hyg.1302))) e (u x))) (Filter.IsBoundedUnder.{u3, u1} α γ (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2572 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2574 : α) => GE.ge.{u3} α (Preorder.toLE.{u3} α _inst_1) x._@.Mathlib.Order.LiminfLimsup._hyg.2572 x._@.Mathlib.Order.LiminfLimsup._hyg.2574) l u)
Case conversion may be inaccurate. Consider using '#align order_iso.is_bounded_under_ge_comp OrderIso.isBoundedUnder_ge_compₓ'. -/
@[simp]
theorem OrderIso.isBoundedUnder_ge_comp [Preorder α] [Preorder β] (e : α ≃o β) {l : Filter γ}
    {u : γ → α} : (IsBoundedUnder (· ≥ ·) l fun x => e (u x)) ↔ IsBoundedUnder (· ≥ ·) l u :=
  e.dual.isBoundedUnder_le_comp
#align order_iso.is_bounded_under_ge_comp OrderIso.isBoundedUnder_ge_comp

/- warning: filter.is_bounded_under_le_inv -> Filter.isBoundedUnder_le_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedCommGroup.{u1} α] {l : Filter.{u2} β} {u : β -> α}, Iff (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) l (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (u x))) (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) l u)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : OrderedCommGroup.{u2} α] {l : Filter.{u1} β} {u : β -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2611 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2613 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedCommGroup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2611 x._@.Mathlib.Order.LiminfLimsup._hyg.2613) l (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α (CommGroup.toDivisionCommMonoid.{u2} α (OrderedCommGroup.toCommGroup.{u2} α _inst_1)))))) (u x))) (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2638 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2640 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedCommGroup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2638 x._@.Mathlib.Order.LiminfLimsup._hyg.2640) l u)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_le_inv Filter.isBoundedUnder_le_invₓ'. -/
@[simp, to_additive]
theorem isBoundedUnder_le_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≤ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≥ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_ge_comp
#align filter.is_bounded_under_le_inv Filter.isBoundedUnder_le_inv
#align filter.is_bounded_under_le_neg Filter.isBoundedUnder_le_neg

/- warning: filter.is_bounded_under_ge_inv -> Filter.isBoundedUnder_ge_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : OrderedCommGroup.{u1} α] {l : Filter.{u2} β} {u : β -> α}, Iff (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) l (fun (x : β) => Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (u x))) (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) l u)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : OrderedCommGroup.{u2} α] {l : Filter.{u1} β} {u : β -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2681 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2683 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedCommGroup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2681 x._@.Mathlib.Order.LiminfLimsup._hyg.2683) l (fun (x : β) => Inv.inv.{u2} α (InvOneClass.toInv.{u2} α (DivInvOneMonoid.toInvOneClass.{u2} α (DivisionMonoid.toDivInvOneMonoid.{u2} α (DivisionCommMonoid.toDivisionMonoid.{u2} α (CommGroup.toDivisionCommMonoid.{u2} α (OrderedCommGroup.toCommGroup.{u2} α _inst_1)))))) (u x))) (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2708 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2710 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedCommGroup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2708 x._@.Mathlib.Order.LiminfLimsup._hyg.2710) l u)
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_ge_inv Filter.isBoundedUnder_ge_invₓ'. -/
@[simp, to_additive]
theorem isBoundedUnder_ge_inv [OrderedCommGroup α] {l : Filter β} {u : β → α} :
    (IsBoundedUnder (· ≥ ·) l fun x => (u x)⁻¹) ↔ IsBoundedUnder (· ≤ ·) l u :=
  (OrderIso.inv α).isBoundedUnder_le_comp
#align filter.is_bounded_under_ge_inv Filter.isBoundedUnder_ge_inv
#align filter.is_bounded_under_ge_neg Filter.isBoundedUnder_ge_neg

/- warning: filter.is_bounded_under.sup -> Filter.IsBoundedUnder.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {f : Filter.{u2} β} {u : β -> α} {v : β -> α}, (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) f u) -> (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) f v) -> (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) f (fun (a : β) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (u a) (v a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {f : Filter.{u1} β} {u : β -> α} {v : β -> α}, (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2753 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2755 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2753 x._@.Mathlib.Order.LiminfLimsup._hyg.2755) f u) -> (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2771 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2773 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2771 x._@.Mathlib.Order.LiminfLimsup._hyg.2773) f v) -> (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2788 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2790 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2788 x._@.Mathlib.Order.LiminfLimsup._hyg.2790) f (fun (a : β) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) (u a) (v a)))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.sup Filter.IsBoundedUnder.supₓ'. -/
theorem IsBoundedUnder.sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≤ ·) u →
      f.IsBoundedUnder (· ≤ ·) v → f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a
  | ⟨bu, (hu : ∀ᶠ x in f, u x ≤ bu)⟩, ⟨bv, (hv : ∀ᶠ x in f, v x ≤ bv)⟩ =>
    ⟨bu ⊔ bv, show ∀ᶠ x in f, u x ⊔ v x ≤ bu ⊔ bv by filter_upwards [hu, hv]with _ using sup_le_sup⟩
#align filter.is_bounded_under.sup Filter.IsBoundedUnder.sup

/- warning: filter.is_bounded_under_le_sup -> Filter.isBoundedUnder_le_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeSup.{u1} α] {f : Filter.{u2} β} {u : β -> α} {v : β -> α}, Iff (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) f (fun (a : β) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (u a) (v a))) (And (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) f u) (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) f v))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeSup.{u2} α] {f : Filter.{u1} β} {u : β -> α} {v : β -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.2985 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.2987 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.2985 x._@.Mathlib.Order.LiminfLimsup._hyg.2987) f (fun (a : β) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α _inst_1) (u a) (v a))) (And (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3014 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3016 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3014 x._@.Mathlib.Order.LiminfLimsup._hyg.3016) f u) (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3031 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3033 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeSup.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3031 x._@.Mathlib.Order.LiminfLimsup._hyg.3033) f v))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_le_sup Filter.isBoundedUnder_le_supₓ'. -/
@[simp]
theorem isBoundedUnder_le_sup [SemilatticeSup α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => u a ⊔ v a) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≤ ·) v :=
  ⟨fun h =>
    ⟨h.mono_le <| eventually_of_forall fun _ => le_sup_left,
      h.mono_le <| eventually_of_forall fun _ => le_sup_right⟩,
    fun h => h.1.sup h.2⟩
#align filter.is_bounded_under_le_sup Filter.isBoundedUnder_le_sup

/- warning: filter.is_bounded_under.inf -> Filter.IsBoundedUnder.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {f : Filter.{u2} β} {u : β -> α} {v : β -> α}, (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) f u) -> (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) f v) -> (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) f (fun (a : β) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (u a) (v a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {f : Filter.{u1} β} {u : β -> α} {v : β -> α}, (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3099 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3101 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3099 x._@.Mathlib.Order.LiminfLimsup._hyg.3101) f u) -> (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3117 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3119 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3117 x._@.Mathlib.Order.LiminfLimsup._hyg.3119) f v) -> (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3134 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3136 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3134 x._@.Mathlib.Order.LiminfLimsup._hyg.3136) f (fun (a : β) => Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) (u a) (v a)))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.inf Filter.IsBoundedUnder.infₓ'. -/
theorem IsBoundedUnder.inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    f.IsBoundedUnder (· ≥ ·) u →
      f.IsBoundedUnder (· ≥ ·) v → f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a :=
  @IsBoundedUnder.sup αᵒᵈ β _ _ _ _
#align filter.is_bounded_under.inf Filter.IsBoundedUnder.inf

/- warning: filter.is_bounded_under_ge_inf -> Filter.isBoundedUnder_ge_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SemilatticeInf.{u1} α] {f : Filter.{u2} β} {u : β -> α} {v : β -> α}, Iff (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) f (fun (a : β) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (u a) (v a))) (And (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) f u) (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) f v))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SemilatticeInf.{u2} α] {f : Filter.{u1} β} {u : β -> α} {v : β -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3188 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3190 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3188 x._@.Mathlib.Order.LiminfLimsup._hyg.3190) f (fun (a : β) => Inf.inf.{u2} α (SemilatticeInf.toInf.{u2} α _inst_1) (u a) (v a))) (And (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3217 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3219 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3217 x._@.Mathlib.Order.LiminfLimsup._hyg.3219) f u) (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3234 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3236 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α _inst_1))) x._@.Mathlib.Order.LiminfLimsup._hyg.3234 x._@.Mathlib.Order.LiminfLimsup._hyg.3236) f v))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_ge_inf Filter.isBoundedUnder_ge_infₓ'. -/
@[simp]
theorem isBoundedUnder_ge_inf [SemilatticeInf α] {f : Filter β} {u v : β → α} :
    (f.IsBoundedUnder (· ≥ ·) fun a => u a ⊓ v a) ↔
      f.IsBoundedUnder (· ≥ ·) u ∧ f.IsBoundedUnder (· ≥ ·) v :=
  @isBoundedUnder_le_sup αᵒᵈ _ _ _ _ _
#align filter.is_bounded_under_ge_inf Filter.isBoundedUnder_ge_inf

/- warning: filter.is_bounded_under_le_abs -> Filter.isBoundedUnder_le_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrderedAddCommGroup.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Iff (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) f (fun (a : β) => Abs.abs.{u1} α (Neg.toHasAbs.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (OrderedAddCommGroup.toAddCommGroup.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (LinearOrder.toLattice.{u1} α (LinearOrderedAddCommGroup.toLinearOrder.{u1} α _inst_1))))) (u a))) (And (Filter.IsBoundedUnder.{u1, u2} α β (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) f u) (Filter.IsBoundedUnder.{u1, u2} α β (GE.ge.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedAddCommGroup.toPartialOrder.{u1} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u1} α _inst_1))))) f u))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrderedAddCommGroup.{u2} α] {f : Filter.{u1} β} {u : β -> α}, Iff (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3275 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3277 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))) x._@.Mathlib.Order.LiminfLimsup._hyg.3275 x._@.Mathlib.Order.LiminfLimsup._hyg.3277) f (fun (a : β) => Abs.abs.{u2} α (Neg.toHasAbs.{u2} α (NegZeroClass.toNeg.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (SubtractionCommMonoid.toSubtractionMonoid.{u2} α (AddCommGroup.toDivisionAddCommMonoid.{u2} α (OrderedAddCommGroup.toAddCommGroup.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1))))))) (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α (LinearOrderedAddCommGroup.toLinearOrder.{u2} α _inst_1)))))) (u a))) (And (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3302 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3304 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))) x._@.Mathlib.Order.LiminfLimsup._hyg.3302 x._@.Mathlib.Order.LiminfLimsup._hyg.3304) f u) (Filter.IsBoundedUnder.{u2, u1} α β (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.3319 : α) (x._@.Mathlib.Order.LiminfLimsup._hyg.3321 : α) => GE.ge.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (OrderedAddCommGroup.toPartialOrder.{u2} α (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} α _inst_1)))) x._@.Mathlib.Order.LiminfLimsup._hyg.3319 x._@.Mathlib.Order.LiminfLimsup._hyg.3321) f u))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under_le_abs Filter.isBoundedUnder_le_absₓ'. -/
theorem isBoundedUnder_le_abs [LinearOrderedAddCommGroup α] {f : Filter β} {u : β → α} :
    (f.IsBoundedUnder (· ≤ ·) fun a => |u a|) ↔
      f.IsBoundedUnder (· ≤ ·) u ∧ f.IsBoundedUnder (· ≥ ·) u :=
  isBoundedUnder_le_sup.trans <| and_congr Iff.rfl isBoundedUnder_le_neg
#align filter.is_bounded_under_le_abs Filter.isBoundedUnder_le_abs

/-- Filters are automatically bounded or cobounded in complete lattices. To use the same statements
in complete and conditionally complete lattices but let automation fill automatically the
boundedness proofs in complete lattices, we use the tactic `is_bounded_default` in the statements,
in the form `(hf : f.is_bounded (≥) . is_bounded_default)`. -/
unsafe def is_bounded_default : tactic Unit :=
  tactic.applyc `` is_cobounded_le_of_bot <|>
    tactic.applyc `` is_cobounded_ge_of_top <|>
      tactic.applyc `` is_bounded_le_of_top <|> tactic.applyc `` is_bounded_ge_of_bot
#align filter.is_bounded_default filter.is_bounded_default

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

#print Filter.limsSup /-
/-- The `Limsup` of a filter `f` is the infimum of the `a` such that, eventually for `f`,
holds `x ≤ a`. -/
def limsSup (f : Filter α) : α :=
  sInf { a | ∀ᶠ n in f, n ≤ a }
#align filter.Limsup Filter.limsSup
-/

#print Filter.limsInf /-
/-- The `Liminf` of a filter `f` is the supremum of the `a` such that, eventually for `f`,
holds `x ≥ a`. -/
def limsInf (f : Filter α) : α :=
  sSup { a | ∀ᶠ n in f, a ≤ n }
#align filter.Liminf Filter.limsInf
-/

#print Filter.limsup /-
/-- The `limsup` of a function `u` along a filter `f` is the infimum of the `a` such that,
eventually for `f`, holds `u x ≤ a`. -/
def limsup (u : β → α) (f : Filter β) : α :=
  limsSup (map u f)
#align filter.limsup Filter.limsup
-/

#print Filter.liminf /-
/-- The `liminf` of a function `u` along a filter `f` is the supremum of the `a` such that,
eventually for `f`, holds `u x ≥ a`. -/
def liminf (u : β → α) (f : Filter β) : α :=
  limsInf (map u f)
#align filter.liminf Filter.liminf
-/

#print Filter.blimsup /-
/-- The `blimsup` of a function `u` along a filter `f`, bounded by a predicate `p`, is the infimum
of the `a` such that, eventually for `f`, `u x ≤ a` whenever `p x` holds. -/
def blimsup (u : β → α) (f : Filter β) (p : β → Prop) :=
  sInf { a | ∀ᶠ x in f, p x → u x ≤ a }
#align filter.blimsup Filter.blimsup
-/

#print Filter.bliminf /-
/-- The `bliminf` of a function `u` along a filter `f`, bounded by a predicate `p`, is the supremum
of the `a` such that, eventually for `f`, `a ≤ u x` whenever `p x` holds. -/
def bliminf (u : β → α) (f : Filter β) (p : β → Prop) :=
  sSup { a | ∀ᶠ x in f, p x → a ≤ u x }
#align filter.bliminf Filter.bliminf
-/

section

variable {f : Filter β} {u : β → α} {p : β → Prop}

/- warning: filter.limsup_eq -> Filter.limsup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.limsup.{u1, u2} α β _inst_1 u f) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => Filter.Eventually.{u2} β (fun (n : β) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (u n) a) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : Filter.{u1} β} {u : β -> α}, Eq.{succ u2} α (Filter.limsup.{u2, u1} α β _inst_1 u f) (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) (setOf.{u2} α (fun (a : α) => Filter.Eventually.{u1} β (fun (n : β) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (u n) a) f)))
Case conversion may be inaccurate. Consider using '#align filter.limsup_eq Filter.limsup_eqₓ'. -/
theorem limsup_eq : limsup u f = sInf { a | ∀ᶠ n in f, u n ≤ a } :=
  rfl
#align filter.limsup_eq Filter.limsup_eq

/- warning: filter.liminf_eq -> Filter.liminf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.liminf.{u1, u2} α β _inst_1 u f) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => Filter.Eventually.{u2} β (fun (n : β) => LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (u n)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : Filter.{u1} β} {u : β -> α}, Eq.{succ u2} α (Filter.liminf.{u2, u1} α β _inst_1 u f) (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) (setOf.{u2} α (fun (a : α) => Filter.Eventually.{u1} β (fun (n : β) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) a (u n)) f)))
Case conversion may be inaccurate. Consider using '#align filter.liminf_eq Filter.liminf_eqₓ'. -/
theorem liminf_eq : liminf u f = sSup { a | ∀ᶠ n in f, a ≤ u n } :=
  rfl
#align filter.liminf_eq Filter.liminf_eq

/- warning: filter.blimsup_eq -> Filter.blimsup_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} {p : β -> Prop}, Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β _inst_1 u f p) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => Filter.Eventually.{u2} β (fun (x : β) => (p x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) (u x) a)) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : Filter.{u1} β} {u : β -> α} {p : β -> Prop}, Eq.{succ u2} α (Filter.blimsup.{u2, u1} α β _inst_1 u f p) (InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α _inst_1) (setOf.{u2} α (fun (a : α) => Filter.Eventually.{u1} β (fun (x : β) => (p x) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) (u x) a)) f)))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_eq Filter.blimsup_eqₓ'. -/
theorem blimsup_eq : blimsup u f p = sInf { a | ∀ᶠ x in f, p x → u x ≤ a } :=
  rfl
#align filter.blimsup_eq Filter.blimsup_eq

/- warning: filter.bliminf_eq -> Filter.bliminf_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} {p : β -> Prop}, Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β _inst_1 u f p) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) (setOf.{u1} α (fun (a : α) => Filter.Eventually.{u2} β (fun (x : β) => (p x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1))))) a (u x))) f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u2} α] {f : Filter.{u1} β} {u : β -> α} {p : β -> Prop}, Eq.{succ u2} α (Filter.bliminf.{u2, u1} α β _inst_1 u f p) (SupSet.sSup.{u2} α (ConditionallyCompleteLattice.toSupSet.{u2} α _inst_1) (setOf.{u2} α (fun (a : α) => Filter.Eventually.{u1} β (fun (x : β) => (p x) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α _inst_1))))) a (u x))) f)))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_eq Filter.bliminf_eqₓ'. -/
theorem bliminf_eq : bliminf u f p = sSup { a | ∀ᶠ x in f, p x → a ≤ u x } :=
  rfl
#align filter.bliminf_eq Filter.bliminf_eq

end

#print Filter.blimsup_true /-
@[simp]
theorem blimsup_true (f : Filter β) (u : β → α) : (blimsup u f fun x => True) = limsup u f := by
  simp [blimsup_eq, limsup_eq]
#align filter.blimsup_true Filter.blimsup_true
-/

#print Filter.bliminf_true /-
@[simp]
theorem bliminf_true (f : Filter β) (u : β → α) : (bliminf u f fun x => True) = liminf u f := by
  simp [bliminf_eq, liminf_eq]
#align filter.bliminf_true Filter.bliminf_true
-/

#print Filter.blimsup_eq_limsup_subtype /-
theorem blimsup_eq_limsup_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    blimsup u f p = limsup (u ∘ (coe : { x | p x } → β)) (comap coe f) :=
  by
  simp only [blimsup_eq, limsup_eq, Function.comp_apply, eventually_comap, SetCoe.forall,
    Subtype.coe_mk, mem_set_of_eq]
  congr
  ext a
  exact
    eventually_congr
      (eventually_of_forall fun x =>
        ⟨fun hx y hy hxy => hxy.symm ▸ hx (hxy ▸ hy), fun hx hx' => hx x hx' rfl⟩)
#align filter.blimsup_eq_limsup_subtype Filter.blimsup_eq_limsup_subtype
-/

#print Filter.bliminf_eq_liminf_subtype /-
theorem bliminf_eq_liminf_subtype {f : Filter β} {u : β → α} {p : β → Prop} :
    bliminf u f p = liminf (u ∘ (coe : { x | p x } → β)) (comap coe f) :=
  @blimsup_eq_limsup_subtype αᵒᵈ β _ f u p
#align filter.bliminf_eq_liminf_subtype Filter.bliminf_eq_liminf_subtype
-/

/- warning: filter.Limsup_le_of_le -> Filter.limsSup_le_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Limsup_le_of_le Filter.limsSup_le_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsSup_le_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, n ≤ a) : limsSup f ≤ a :=
  csInf_le hf h
#align filter.Limsup_le_of_le Filter.limsSup_le_of_le

/- warning: filter.le_Liminf_of_le -> Filter.le_limsInf_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.le_Liminf_of_le Filter.le_limsInf_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_limsInf_of_le {f : Filter α} {a}
    (hf : f.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, a ≤ n) : a ≤ limsInf f :=
  le_csSup hf h
#align filter.le_Liminf_of_le Filter.le_limsInf_of_le

/- warning: filter.limsup_le_of_le clashes with filter.Limsup_le_of_le -> Filter.limsSup_le_of_le
warning: filter.limsup_le_of_le -> Filter.limsSup_le_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.limsup_le_of_le Filter.limsSup_le_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsSup_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, u n ≤ a) : limsup u f ≤ a :=
  csInf_le hf h
#align filter.limsup_le_of_le Filter.limsSup_le_of_le

/- warning: filter.le_liminf_of_le -> Filter.le_liminf_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.le_liminf_of_le Filter.le_liminf_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f :=
  le_csSup hf h
#align filter.le_liminf_of_le Filter.le_liminf_of_le

/- warning: filter.le_Limsup_of_le -> Filter.le_limsSup_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.le_Limsup_of_le Filter.le_limsSup_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_limsSup_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, n ≤ b) → a ≤ b) : a ≤ limsSup f :=
  le_csInf hf h
#align filter.le_Limsup_of_le Filter.le_limsSup_of_le

/- warning: filter.Liminf_le_of_le -> Filter.limsInf_le_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Liminf_le_of_le Filter.limsInf_le_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsInf_le_of_le {f : Filter α} {a}
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, b ≤ n) → b ≤ a) : limsInf f ≤ a :=
  csSup_le hf h
#align filter.Liminf_le_of_le Filter.limsInf_le_of_le

/- warning: filter.le_limsup_of_le -> Filter.le_limsup_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.le_limsup_of_le Filter.le_limsup_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_limsup_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, u n ≤ b) → a ≤ b) : a ≤ limsup u f :=
  le_csInf hf h
#align filter.le_limsup_of_le Filter.le_limsup_of_le

/- warning: filter.liminf_le_of_le -> Filter.liminf_le_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.liminf_le_of_le Filter.liminf_le_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : ∀ b, (∀ᶠ n in f, b ≤ u n) → b ≤ a) : liminf u f ≤ a :=
  csSup_le hf h
#align filter.liminf_le_of_le Filter.liminf_le_of_le

/- warning: filter.Liminf_le_Limsup -> Filter.limsInf_le_limsSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Liminf_le_Limsup Filter.limsInf_le_limsSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsInf_le_limsSup {f : Filter α} [NeBot f]
    (h₁ : f.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h₂ : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default) :
    limsInf f ≤ limsSup f :=
  limsInf_le_of_le h₂ fun a₀ ha₀ =>
    le_limsSup_of_le h₁ fun a₁ ha₁ =>
      show a₀ ≤ a₁ from
        let ⟨b, hb₀, hb₁⟩ := (ha₀.And ha₁).exists
        le_trans hb₀ hb₁
#align filter.Liminf_le_Limsup Filter.limsInf_le_limsSup

/- warning: filter.liminf_le_limsup -> Filter.liminf_le_limsup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.liminf_le_limsup Filter.liminf_le_limsupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_limsup {f : Filter β} [NeBot f] {u : β → α}
    (h : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ limsup u f :=
  limsInf_le_limsSup h h'
#align filter.liminf_le_limsup Filter.liminf_le_limsup

/- warning: filter.Limsup_le_Limsup -> Filter.limsSup_le_limsSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Limsup_le_Limsup Filter.limsSup_le_limsSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsSup_le_limsSup {f g : Filter α}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ a, (∀ᶠ n in g, n ≤ a) → ∀ᶠ n in f, n ≤ a) : limsSup f ≤ limsSup g :=
  csInf_le_csInf hf hg h
#align filter.Limsup_le_Limsup Filter.limsSup_le_limsSup

/- warning: filter.Liminf_le_Liminf -> Filter.limsInf_le_limsInf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Liminf_le_Liminf Filter.limsInf_le_limsInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsInf_le_limsInf {f g : Filter α}
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : ∀ a, (∀ᶠ n in f, a ≤ n) → ∀ᶠ n in g, a ≤ n) : limsInf f ≤ limsInf g :=
  csSup_le_csSup hg hf h
#align filter.Liminf_le_Liminf Filter.limsInf_le_limsInf

/- warning: filter.limsup_le_limsup -> Filter.limsup_le_limsup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.limsup_le_limsup Filter.limsup_le_limsupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsup_le_limsup {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : u ≤ᶠ[f] v)
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hv : f.IsBoundedUnder (· ≤ ·) v := by
      run_tac
        is_bounded_default) :
    limsup u f ≤ limsup v f :=
  limsSup_le_limsSup hu hv fun b => h.trans
#align filter.limsup_le_limsup Filter.limsup_le_limsup

/- warning: filter.liminf_le_liminf -> Filter.liminf_le_liminf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.liminf_le_liminf Filter.liminf_le_liminfₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_liminf {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a ≤ v a)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hv : f.IsCoboundedUnder (· ≥ ·) v := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ liminf v f :=
  @limsup_le_limsup βᵒᵈ α _ _ _ _ h hv hu
#align filter.liminf_le_liminf Filter.liminf_le_liminf

/- warning: filter.Limsup_le_Limsup_of_le -> Filter.limsSup_le_limsSup_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Limsup_le_Limsup_of_le Filter.limsSup_le_limsSup_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsSup_le_limsSup_of_le {f g : Filter α} (h : f ≤ g)
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsBounded (· ≤ ·) := by
      run_tac
        is_bounded_default) :
    limsSup f ≤ limsSup g :=
  limsSup_le_limsSup hf hg fun a ha => h ha
#align filter.Limsup_le_Limsup_of_le Filter.limsSup_le_limsSup_of_le

/- warning: filter.Liminf_le_Liminf_of_le -> Filter.limsInf_le_limsInf_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.Liminf_le_Liminf_of_le Filter.limsInf_le_limsInf_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsInf_le_limsInf_of_le {f g : Filter α} (h : g ≤ f)
    (hf : f.IsBounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (hg : g.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default) :
    limsInf f ≤ limsInf g :=
  limsInf_le_limsInf hf hg fun a ha => h ha
#align filter.Liminf_le_Liminf_of_le Filter.limsInf_le_limsInf_of_le

/- warning: filter.limsup_le_limsup_of_le -> Filter.limsup_le_limsup_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.limsup_le_limsup_of_le Filter.limsup_le_limsup_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem limsup_le_limsup_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : f ≤ g)
    {u : α → β}
    (hf : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hg : g.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    limsup u f ≤ limsup u g :=
  limsSup_le_limsSup_of_le (map_mono h) hf hg
#align filter.limsup_le_limsup_of_le Filter.limsup_le_limsup_of_le

/- warning: filter.liminf_le_liminf_of_le -> Filter.liminf_le_liminf_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.liminf_le_liminf_of_le Filter.liminf_le_liminf_of_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_liminf_of_le {α β} [ConditionallyCompleteLattice β] {f g : Filter α} (h : g ≤ f)
    {u : α → β}
    (hf : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hg : g.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ liminf u g :=
  limsInf_le_limsInf_of_le (map_mono h) hf hg
#align filter.liminf_le_liminf_of_le Filter.liminf_le_liminf_of_le

/- warning: filter.Limsup_principal -> Filter.limsSup_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (Filter.limsSup.{u1} α _inst_1 (Filter.principal.{u1} α s)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddAbove.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (Filter.limsSup.{u1} α _inst_1 (Filter.principal.{u1} α s)) (SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align filter.Limsup_principal Filter.limsSup_principalₓ'. -/
theorem limsSup_principal {s : Set α} (h : BddAbove s) (hs : s.Nonempty) : limsSup (𝓟 s) = sSup s :=
  by simp [Limsup] <;> exact csInf_upper_bounds_eq_csSup h hs
#align filter.Limsup_principal Filter.limsSup_principal

/- warning: filter.Liminf_principal -> Filter.limsInf_principal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (Filter.limsInf.{u1} α _inst_1 (Filter.principal.{u1} α s)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : ConditionallyCompleteLattice.{u1} α] {s : Set.{u1} α}, (BddBelow.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α _inst_1)))) s) -> (Set.Nonempty.{u1} α s) -> (Eq.{succ u1} α (Filter.limsInf.{u1} α _inst_1 (Filter.principal.{u1} α s)) (InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align filter.Liminf_principal Filter.limsInf_principalₓ'. -/
theorem limsInf_principal {s : Set α} (h : BddBelow s) (hs : s.Nonempty) : limsInf (𝓟 s) = sInf s :=
  @limsSup_principal αᵒᵈ _ s h hs
#align filter.Liminf_principal Filter.limsInf_principal

#print Filter.limsup_congr /-
theorem limsup_congr {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : limsup u f = limsup v f :=
  by
  rw [limsup_eq]
  congr with b
  exact eventually_congr (h.mono fun x hx => by simp [hx])
#align filter.limsup_congr Filter.limsup_congr
-/

#print Filter.blimsup_congr /-
theorem blimsup_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    blimsup u f p = blimsup v f p := by
  rw [blimsup_eq]
  congr with b
  refine' eventually_congr (h.mono fun x hx => ⟨fun h₁ h₂ => _, fun h₁ h₂ => _⟩)
  · rw [← hx h₂]
    exact h₁ h₂
  · rw [hx h₂]
    exact h₁ h₂
#align filter.blimsup_congr Filter.blimsup_congr
-/

#print Filter.bliminf_congr /-
theorem bliminf_congr {f : Filter β} {u v : β → α} {p : β → Prop} (h : ∀ᶠ a in f, p a → u a = v a) :
    bliminf u f p = bliminf v f p :=
  @blimsup_congr αᵒᵈ _ _ _ _ _ _ h
#align filter.bliminf_congr Filter.bliminf_congr
-/

#print Filter.liminf_congr /-
theorem liminf_congr {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} {u v : α → β}
    (h : ∀ᶠ a in f, u a = v a) : liminf u f = liminf v f :=
  @limsup_congr βᵒᵈ _ _ _ _ _ h
#align filter.liminf_congr Filter.liminf_congr
-/

#print Filter.limsup_const /-
theorem limsup_const {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : limsup (fun x => b) f = b := by
  simpa only [limsup_eq, eventually_const] using csInf_Ici
#align filter.limsup_const Filter.limsup_const
-/

#print Filter.liminf_const /-
theorem liminf_const {α : Type _} [ConditionallyCompleteLattice β] {f : Filter α} [NeBot f]
    (b : β) : liminf (fun x => b) f = b :=
  @limsup_const βᵒᵈ α _ f _ b
#align filter.liminf_const Filter.liminf_const
-/

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice α]

/- warning: filter.Limsup_bot -> Filter.limsSup_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.Limsup_bot Filter.limsSup_botₓ'. -/
@[simp]
theorem limsSup_bot : limsSup (⊥ : Filter α) = ⊥ :=
  bot_unique <| sInf_le <| by simp
#align filter.Limsup_bot Filter.limsSup_bot

/- warning: filter.Liminf_bot -> Filter.limsInf_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toHasBot.{u1} (Filter.{u1} α) (Filter.completeLattice.{u1} α)))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Bot.bot.{u1} (Filter.{u1} α) (CompleteLattice.toBot.{u1} (Filter.{u1} α) (Filter.instCompleteLatticeFilter.{u1} α)))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.Liminf_bot Filter.limsInf_botₓ'. -/
@[simp]
theorem limsInf_bot : limsInf (⊥ : Filter α) = ⊤ :=
  top_unique <| le_sSup <| by simp
#align filter.Liminf_bot Filter.limsInf_bot

/- warning: filter.Limsup_top -> Filter.limsSup_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.Limsup_top Filter.limsSup_topₓ'. -/
@[simp]
theorem limsSup_top : limsSup (⊤ : Filter α) = ⊤ :=
  top_unique <| le_sInf <| by simp [eq_univ_iff_forall] <;> exact fun b hb => top_unique <| hb _
#align filter.Limsup_top Filter.limsSup_top

/- warning: filter.Liminf_top -> Filter.limsInf_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Top.top.{u1} (Filter.{u1} α) (Filter.hasTop.{u1} α))) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (Top.top.{u1} (Filter.{u1} α) (Filter.instTopFilter.{u1} α))) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.Liminf_top Filter.limsInf_topₓ'. -/
@[simp]
theorem limsInf_top : limsInf (⊤ : Filter α) = ⊥ :=
  bot_unique <| sSup_le <| by simp [eq_univ_iff_forall] <;> exact fun b hb => bot_unique <| hb _
#align filter.Liminf_top Filter.limsInf_top

/- warning: filter.blimsup_false -> Filter.blimsup_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => False)) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => False)) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_false Filter.blimsup_falseₓ'. -/
@[simp]
theorem blimsup_false {f : Filter β} {u : β → α} : (blimsup u f fun x => False) = ⊥ := by
  simp [blimsup_eq]
#align filter.blimsup_false Filter.blimsup_false

/- warning: filter.bliminf_false -> Filter.bliminf_false is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => False)) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => False)) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_false Filter.bliminf_falseₓ'. -/
@[simp]
theorem bliminf_false {f : Filter β} {u : β → α} : (bliminf u f fun x => False) = ⊤ := by
  simp [bliminf_eq]
#align filter.bliminf_false Filter.bliminf_false

/- warning: filter.limsup_const_bot -> Filter.limsup_const_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β}, Eq.{succ u1} α (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (x : β) => Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1)) f) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β}, Eq.{succ u1} α (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (x : β) => Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1)) f) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.limsup_const_bot Filter.limsup_const_botₓ'. -/
/-- Same as limsup_const applied to `⊥` but without the `ne_bot f` assumption -/
theorem limsup_const_bot {f : Filter β} : limsup (fun x : β => (⊥ : α)) f = (⊥ : α) :=
  by
  rw [limsup_eq, eq_bot_iff]
  exact sInf_le (eventually_of_forall fun x => le_rfl)
#align filter.limsup_const_bot Filter.limsup_const_bot

/- warning: filter.liminf_const_top -> Filter.liminf_const_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β}, Eq.{succ u1} α (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (x : β) => Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1)) f) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β}, Eq.{succ u1} α (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (x : β) => Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1)) f) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align filter.liminf_const_top Filter.liminf_const_topₓ'. -/
/-- Same as limsup_const applied to `⊤` but without the `ne_bot f` assumption -/
theorem liminf_const_top {f : Filter β} : liminf (fun x : β => (⊤ : α)) f = (⊤ : α) :=
  @limsup_const_bot αᵒᵈ β _ _
#align filter.liminf_const_top Filter.liminf_const_top

/- warning: filter.has_basis.Limsup_eq_infi_Sup -> Filter.HasBasis.limsSup_eq_iInf_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {f : Filter.{u1} α}, (Filter.HasBasis.{u1, u2} α ι f p s) -> (Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (s i)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {ι : Sort.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {f : Filter.{u1} α}, (Filter.HasBasis.{u1, u2} α ι f p s) -> (Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iInf.{u1, u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.Limsup_eq_infi_Sup Filter.HasBasis.limsSup_eq_iInf_sSupₓ'. -/
theorem HasBasis.limsSup_eq_iInf_sSup {ι} {p : ι → Prop} {s} {f : Filter α} (h : f.HasBasis p s) :
    limsSup f = ⨅ (i) (hi : p i), sSup (s i) :=
  le_antisymm (le_iInf₂ fun i hi => sInf_le <| h.eventually_iff.2 ⟨i, hi, fun x => le_sSup⟩)
    (le_sInf fun a ha =>
      let ⟨i, hi, ha⟩ := h.eventually_iff.1 ha
      iInf₂_le_of_le _ hi <| sSup_le ha)
#align filter.has_basis.Limsup_eq_infi_Sup Filter.HasBasis.limsSup_eq_iInf_sSup

/- warning: filter.has_basis.Liminf_eq_supr_Inf -> Filter.HasBasis.limsInf_eq_iSup_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u1} α)} {f : Filter.{u1} α}, (Filter.HasBasis.{u1, succ u2} α ι f p s) -> (Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (s i)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {p : ι -> Prop} {s : ι -> (Set.{u2} α)} {f : Filter.{u2} α}, (Filter.HasBasis.{u2, succ u1} α ι f p s) -> (Eq.{succ u2} α (Filter.limsInf.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) f) (iSup.{u2, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) ι (fun (i : ι) => iSup.{u2, 0} α (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (p i) (fun (hi : p i) => InfSet.sInf.{u2} α (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (s i)))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.Liminf_eq_supr_Inf Filter.HasBasis.limsInf_eq_iSup_sInfₓ'. -/
theorem HasBasis.limsInf_eq_iSup_sInf {p : ι → Prop} {s : ι → Set α} {f : Filter α}
    (h : f.HasBasis p s) : limsInf f = ⨆ (i) (hi : p i), sInf (s i) :=
  @HasBasis.limsSup_eq_iInf_sSup αᵒᵈ _ _ _ _ _ h
#align filter.has_basis.Liminf_eq_supr_Inf Filter.HasBasis.limsInf_eq_iSup_sInf

/- warning: filter.Limsup_eq_infi_Sup -> Filter.limsSup_eq_iInf_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u1} α}, Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iInf.{u1, succ u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u1} α) (fun (s : Set.{u1} α) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u1} α}, Eq.{succ u1} α (Filter.limsSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iInf.{u1, succ u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u1} α) (fun (s : Set.{u1} α) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) => SupSet.sSup.{u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)))
Case conversion may be inaccurate. Consider using '#align filter.Limsup_eq_infi_Sup Filter.limsSup_eq_iInf_sSupₓ'. -/
theorem limsSup_eq_iInf_sSup {f : Filter α} : limsSup f = ⨅ s ∈ f, sSup s :=
  f.basis_sets.limsSup_eq_iInf_sSup
#align filter.Limsup_eq_infi_Sup Filter.limsSup_eq_iInf_sSup

/- warning: filter.Liminf_eq_supr_Inf -> Filter.limsInf_eq_iSup_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u1} α}, Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u1} α) (fun (s : Set.{u1} α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s f) => InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u1} α}, Eq.{succ u1} α (Filter.limsInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) f) (iSup.{u1, succ u1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u1} α) (fun (s : Set.{u1} α) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) (fun (H : Membership.mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (instMembershipSetFilter.{u1} α) s f) => InfSet.sInf.{u1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) s)))
Case conversion may be inaccurate. Consider using '#align filter.Liminf_eq_supr_Inf Filter.limsInf_eq_iSup_sInfₓ'. -/
theorem limsInf_eq_iSup_sInf {f : Filter α} : limsInf f = ⨆ s ∈ f, sInf s :=
  @limsSup_eq_iInf_sSup αᵒᵈ _ _
#align filter.Liminf_eq_supr_Inf Filter.limsInf_eq_iSup_sInf

/- warning: filter.limsup_le_supr -> Filter.limsup_le_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (n : β) => u n))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (n : β) => u n))
Case conversion may be inaccurate. Consider using '#align filter.limsup_le_supr Filter.limsup_le_iSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem limsup_le_iSup {f : Filter β} {u : β → α} : limsup u f ≤ ⨆ n, u n :=
  limsSup_le_of_le
    (by
      run_tac
        is_bounded_default)
    (eventually_of_forall (le_iSup u))
#align filter.limsup_le_supr Filter.limsup_le_iSup

/- warning: filter.infi_le_liminf -> Filter.iInf_le_liminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (n : β) => u n)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (n : β) => u n)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f)
Case conversion may be inaccurate. Consider using '#align filter.infi_le_liminf Filter.iInf_le_liminfₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem iInf_le_liminf {f : Filter β} {u : β → α} : (⨅ n, u n) ≤ liminf u f :=
  le_liminf_of_le
    (by
      run_tac
        is_bounded_default)
    (eventually_of_forall (iInf_le u))
#align filter.infi_le_liminf Filter.iInf_le_liminf

/- warning: filter.limsup_eq_infi_supr -> Filter.limsup_eq_iInf_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) => iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => u a)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) => iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) => u a)))))
Case conversion may be inaccurate. Consider using '#align filter.limsup_eq_infi_supr Filter.limsup_eq_iInf_iSupₓ'. -/
/-- In a complete lattice, the limsup of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem limsup_eq_iInf_iSup {f : Filter β} {u : β → α} : limsup u f = ⨅ s ∈ f, ⨆ a ∈ s, u a :=
  (f.basis_sets.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]
#align filter.limsup_eq_infi_supr Filter.limsup_eq_iInf_iSup

/- warning: filter.limsup_eq_infi_supr_of_nat -> Filter.limsup_eq_iInf_iSup_of_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => u i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => u i))))
Case conversion may be inaccurate. Consider using '#align filter.limsup_eq_infi_supr_of_nat Filter.limsup_eq_iInf_iSup_of_natₓ'. -/
theorem limsup_eq_iInf_iSup_of_nat {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i ≥ n, u i :=
  (atTop_basis.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, iInf_const] <;> rfl
#align filter.limsup_eq_infi_supr_of_nat Filter.limsup_eq_iInf_iSup_of_nat

/- warning: filter.limsup_eq_infi_supr_of_nat' -> Filter.limsup_eq_iInf_iSup_of_nat' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i n))))
Case conversion may be inaccurate. Consider using '#align filter.limsup_eq_infi_supr_of_nat' Filter.limsup_eq_iInf_iSup_of_nat'ₓ'. -/
theorem limsup_eq_iInf_iSup_of_nat' {u : ℕ → α} : limsup u atTop = ⨅ n : ℕ, ⨆ i : ℕ, u (i + n) := by
  simp only [limsup_eq_infi_supr_of_nat, iSup_ge_eq_iSup_nat_add]
#align filter.limsup_eq_infi_supr_of_nat' Filter.limsup_eq_iInf_iSup_of_nat'

/- warning: filter.has_basis.limsup_eq_infi_supr -> Filter.HasBasis.limsup_eq_iInf_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u2} β)} {f : Filter.{u2} β} {u : β -> α}, (Filter.HasBasis.{u2, succ u3} β ι f p s) -> (Eq.{succ u1} α (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iInf.{u1, succ u3} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (s i)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (s i)) => u a))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u3} β)} {f : Filter.{u3} β} {u : β -> α}, (Filter.HasBasis.{u3, succ u2} β ι f p s) -> (Eq.{succ u1} α (Filter.limsup.{u1, u3} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => iSup.{u1, succ u3} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a (s i)) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a (s i)) => u a))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.limsup_eq_infi_supr Filter.HasBasis.limsup_eq_iInf_iSupₓ'. -/
theorem HasBasis.limsup_eq_iInf_iSup {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : limsup u f = ⨅ (i) (hi : p i), ⨆ a ∈ s i, u a :=
  (h.map u).limsSup_eq_iInf_sSup.trans <| by simp only [sSup_image, id]
#align filter.has_basis.limsup_eq_infi_supr Filter.HasBasis.limsup_eq_iInf_iSup

/- warning: filter.blimsup_congr' -> Filter.blimsup_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (Ne.{succ u1} α (u x) (Bot.bot.{u1} α (CompleteLattice.toHasBot.{u1} α _inst_1))) -> (Iff (p x) (q x))) f) -> (Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (Ne.{succ u1} α (u x) (Bot.bot.{u1} α (CompleteLattice.toBot.{u1} α _inst_1))) -> (Iff (p x) (q x))) f) -> (Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_congr' Filter.blimsup_congr'ₓ'. -/
theorem blimsup_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊥ → (p x ↔ q x)) : blimsup u f p = blimsup u f q :=
  by
  simp only [blimsup_eq]
  congr
  ext a
  refine' eventually_congr (h.mono fun b hb => _)
  cases' eq_or_ne (u b) ⊥ with hu hu; · simp [hu]
  rw [hb hu]
#align filter.blimsup_congr' Filter.blimsup_congr'

/- warning: filter.bliminf_congr' -> Filter.bliminf_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (Ne.{succ u1} α (u x) (Top.top.{u1} α (CompleteLattice.toHasTop.{u1} α _inst_1))) -> (Iff (p x) (q x))) f) -> (Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (Ne.{succ u1} α (u x) (Top.top.{u1} α (CompleteLattice.toTop.{u1} α _inst_1))) -> (Iff (p x) (q x))) f) -> (Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_congr' Filter.bliminf_congr'ₓ'. -/
theorem bliminf_congr' {f : Filter β} {p q : β → Prop} {u : β → α}
    (h : ∀ᶠ x in f, u x ≠ ⊤ → (p x ↔ q x)) : bliminf u f p = bliminf u f q :=
  @blimsup_congr' αᵒᵈ β _ _ _ _ _ h
#align filter.bliminf_congr' Filter.bliminf_congr'

/- warning: filter.blimsup_eq_infi_bsupr -> Filter.blimsup_eq_iInf_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) => iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (b : β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p b) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s)) (fun (hb : And (p b) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s)) => u b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) => iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (b : β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p b) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s)) (fun (hb : And (p b) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s)) => u b)))))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_eq_infi_bsupr Filter.blimsup_eq_iInf_biSupₓ'. -/
theorem blimsup_eq_iInf_biSup {f : Filter β} {p : β → Prop} {u : β → α} :
    blimsup u f p = ⨅ s ∈ f, ⨆ (b) (hb : p b ∧ b ∈ s), u b :=
  by
  refine' le_antisymm (sInf_le_sInf _) (infi_le_iff.mpr fun a ha => le_Inf_iff.mpr fun a' ha' => _)
  · rintro - ⟨s, rfl⟩
    simp only [mem_set_of_eq, le_iInf_iff]
    conv =>
      congr
      ext
      rw [Imp.swap]
    refine'
      eventually_imp_distrib_left.mpr fun h => eventually_iff_exists_mem.2 ⟨s, h, fun x h₁ h₂ => _⟩
    exact @le_iSup₂ α β (fun b => p b ∧ b ∈ s) _ (fun b hb => u b) x ⟨h₂, h₁⟩
  · obtain ⟨s, hs, hs'⟩ := eventually_iff_exists_mem.mp ha'
    simp_rw [Imp.swap] at hs'
    exact (le_infi_iff.mp (ha s) hs).trans (by simpa only [iSup₂_le_iff, and_imp] )
#align filter.blimsup_eq_infi_bsupr Filter.blimsup_eq_iInf_biSup

/- warning: filter.blimsup_eq_infi_bsupr_of_nat -> Filter.blimsup_eq_iInf_biSup_of_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Nat -> Prop} {u : Nat -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) p) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (j : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p j) (LE.le.{0} Nat Nat.hasLe i j)) (fun (hj : And (p j) (LE.le.{0} Nat Nat.hasLe i j)) => u j))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Nat -> Prop} {u : Nat -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) p) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (j : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p j) (LE.le.{0} Nat instLENat i j)) (fun (hj : And (p j) (LE.le.{0} Nat instLENat i j)) => u j))))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_eq_infi_bsupr_of_nat Filter.blimsup_eq_iInf_biSup_of_natₓ'. -/
theorem blimsup_eq_iInf_biSup_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    blimsup u atTop p = ⨅ i, ⨆ (j) (hj : p j ∧ i ≤ j), u j := by
  simp only [blimsup_eq_limsup_subtype, mem_preimage, mem_Ici, Function.comp_apply, ciInf_pos,
    iSup_subtype, (at_top_basis.comap (coe : { x | p x } → ℕ)).limsup_eq_iInf_iSup, mem_set_of_eq,
    Subtype.coe_mk, iSup_and]
#align filter.blimsup_eq_infi_bsupr_of_nat Filter.blimsup_eq_iInf_biSup_of_nat

/- warning: filter.liminf_eq_supr_infi -> Filter.liminf_eq_iSup_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) => iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => u a)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α}, Eq.{succ u1} α (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) => iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) (fun (H : Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) a s) => u a)))))
Case conversion may be inaccurate. Consider using '#align filter.liminf_eq_supr_infi Filter.liminf_eq_iSup_iInfₓ'. -/
/-- In a complete lattice, the liminf of a function is the infimum over sets `s` in the filter
of the supremum of the function over `s` -/
theorem liminf_eq_iSup_iInf {f : Filter β} {u : β → α} : liminf u f = ⨆ s ∈ f, ⨅ a ∈ s, u a :=
  @limsup_eq_iInf_iSup αᵒᵈ β _ _ _
#align filter.liminf_eq_supr_infi Filter.liminf_eq_iSup_iInf

/- warning: filter.liminf_eq_supr_infi_of_nat -> Filter.liminf_eq_iSup_iInf_of_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (GE.ge.{0} Nat Nat.hasLe i n) (fun (H : GE.ge.{0} Nat Nat.hasLe i n) => u i))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (GE.ge.{0} Nat instLENat i n) (fun (H : GE.ge.{0} Nat instLENat i n) => u i))))
Case conversion may be inaccurate. Consider using '#align filter.liminf_eq_supr_infi_of_nat Filter.liminf_eq_iSup_iInf_of_natₓ'. -/
theorem liminf_eq_iSup_iInf_of_nat {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i ≥ n, u i :=
  @limsup_eq_iInf_iSup_of_nat αᵒᵈ _ u
#align filter.liminf_eq_supr_infi_of_nat Filter.liminf_eq_iSup_iInf_of_nat

/- warning: filter.liminf_eq_supr_infi_of_nat' -> Filter.liminf_eq_iSup_iInf_of_nat' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {u : Nat -> α}, Eq.{succ u1} α (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (n : Nat) => iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i n))))
Case conversion may be inaccurate. Consider using '#align filter.liminf_eq_supr_infi_of_nat' Filter.liminf_eq_iSup_iInf_of_nat'ₓ'. -/
theorem liminf_eq_iSup_iInf_of_nat' {u : ℕ → α} : liminf u atTop = ⨆ n : ℕ, ⨅ i : ℕ, u (i + n) :=
  @limsup_eq_iInf_iSup_of_nat' αᵒᵈ _ _
#align filter.liminf_eq_supr_infi_of_nat' Filter.liminf_eq_iSup_iInf_of_nat'

/- warning: filter.has_basis.liminf_eq_supr_infi -> Filter.HasBasis.liminf_eq_iSup_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u2} β)} {f : Filter.{u2} β} {u : β -> α}, (Filter.HasBasis.{u2, succ u3} β ι f p s) -> (Eq.{succ u1} α (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iSup.{u1, succ u3} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (s i)) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a (s i)) => u a))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {ι : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {p : ι -> Prop} {s : ι -> (Set.{u3} β)} {f : Filter.{u3} β} {u : β -> α}, (Filter.HasBasis.{u3, succ u2} β ι f p s) -> (Eq.{succ u1} α (Filter.liminf.{u1, u3} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) ι (fun (i : ι) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (p i) (fun (hi : p i) => iInf.{u1, succ u3} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (a : β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a (s i)) (fun (H : Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) a (s i)) => u a))))))
Case conversion may be inaccurate. Consider using '#align filter.has_basis.liminf_eq_supr_infi Filter.HasBasis.liminf_eq_iSup_iInfₓ'. -/
theorem HasBasis.liminf_eq_iSup_iInf {p : ι → Prop} {s : ι → Set β} {f : Filter β} {u : β → α}
    (h : f.HasBasis p s) : liminf u f = ⨆ (i) (hi : p i), ⨅ a ∈ s i, u a :=
  @HasBasis.limsup_eq_iInf_iSup αᵒᵈ _ _ _ _ _ _ _ h
#align filter.has_basis.liminf_eq_supr_infi Filter.HasBasis.liminf_eq_iSup_iInf

/- warning: filter.bliminf_eq_supr_binfi -> Filter.bliminf_eq_iSup_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) (fun (H : Membership.Mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (Filter.hasMem.{u2} β) s f) => iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (b : β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p b) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s)) (fun (hb : And (p b) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b s)) => u b)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (iSup.{u1, succ u2} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Set.{u2} β) (fun (s : Set.{u2} β) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) (fun (H : Membership.mem.{u2, u2} (Set.{u2} β) (Filter.{u2} β) (instMembershipSetFilter.{u2} β) s f) => iInf.{u1, succ u2} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) β (fun (b : β) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p b) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s)) (fun (hb : And (p b) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) b s)) => u b)))))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_eq_supr_binfi Filter.bliminf_eq_iSup_biInfₓ'. -/
theorem bliminf_eq_iSup_biInf {f : Filter β} {p : β → Prop} {u : β → α} :
    bliminf u f p = ⨆ s ∈ f, ⨅ (b) (hb : p b ∧ b ∈ s), u b :=
  @blimsup_eq_iInf_biSup αᵒᵈ β _ f p u
#align filter.bliminf_eq_supr_binfi Filter.bliminf_eq_iSup_biInf

/- warning: filter.bliminf_eq_supr_binfi_of_nat -> Filter.bliminf_eq_iSup_biInf_of_nat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Nat -> Prop} {u : Nat -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) p) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (j : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p j) (LE.le.{0} Nat Nat.hasLe i j)) (fun (hj : And (p j) (LE.le.{0} Nat Nat.hasLe i j)) => u j))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] {p : Nat -> Prop} {u : Nat -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) p) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (i : Nat) => iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (j : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (And (p j) (LE.le.{0} Nat instLENat i j)) (fun (hj : And (p j) (LE.le.{0} Nat instLENat i j)) => u j))))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_eq_supr_binfi_of_nat Filter.bliminf_eq_iSup_biInf_of_natₓ'. -/
theorem bliminf_eq_iSup_biInf_of_nat {p : ℕ → Prop} {u : ℕ → α} :
    bliminf u atTop p = ⨆ i, ⨅ (j) (hj : p j ∧ i ≤ j), u j :=
  @blimsup_eq_iInf_biSup_of_nat αᵒᵈ _ p u
#align filter.bliminf_eq_supr_binfi_of_nat Filter.bliminf_eq_iSup_biInf_of_nat

/- warning: filter.limsup_eq_Inf_Sup -> Filter.limsup_eq_sInf_sSup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} (F : Filter.{u1} ι) [_inst_2 : CompleteLattice.{u2} R] (a : ι -> R), Eq.{succ u2} R (Filter.limsup.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R _inst_2) a F) (InfSet.sInf.{u2} R (ConditionallyCompleteLattice.toHasInf.{u2} R (CompleteLattice.toConditionallyCompleteLattice.{u2} R _inst_2)) (Set.image.{u1, u2} (Set.{u1} ι) R (fun (I : Set.{u1} ι) => SupSet.sSup.{u2} R (ConditionallyCompleteLattice.toHasSup.{u2} R (CompleteLattice.toConditionallyCompleteLattice.{u2} R _inst_2)) (Set.image.{u1, u2} ι R a I)) (Filter.sets.{u1} ι F)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} (F : Filter.{u2} ι) [_inst_2 : CompleteLattice.{u1} R] (a : ι -> R), Eq.{succ u1} R (Filter.limsup.{u1, u2} R ι (CompleteLattice.toConditionallyCompleteLattice.{u1} R _inst_2) a F) (InfSet.sInf.{u1} R (ConditionallyCompleteLattice.toInfSet.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R _inst_2)) (Set.image.{u2, u1} (Set.{u2} ι) R (fun (I : Set.{u2} ι) => SupSet.sSup.{u1} R (ConditionallyCompleteLattice.toSupSet.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R _inst_2)) (Set.image.{u2, u1} ι R a I)) (Filter.sets.{u2} ι F)))
Case conversion may be inaccurate. Consider using '#align filter.limsup_eq_Inf_Sup Filter.limsup_eq_sInf_sSupₓ'. -/
theorem limsup_eq_sInf_sSup {ι R : Type _} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    limsup a F = sInf ((fun I => sSup (a '' I)) '' F.sets) :=
  by
  refine' le_antisymm _ _
  · rw [limsup_eq]
    refine' sInf_le_sInf fun x hx => _
    rcases(mem_image _ F.sets x).mp hx with ⟨I, ⟨I_mem_F, hI⟩⟩
    filter_upwards [I_mem_F]with i hi
    exact hI ▸ le_sSup (mem_image_of_mem _ hi)
  · refine'
      le_Inf_iff.mpr fun b hb =>
        sInf_le_of_le (mem_image_of_mem _ <| filter.mem_sets.mpr hb) <| sSup_le _
    rintro _ ⟨_, h, rfl⟩
    exact h
#align filter.limsup_eq_Inf_Sup Filter.limsup_eq_sInf_sSup

/- warning: filter.liminf_eq_Sup_Inf -> Filter.liminf_eq_sSup_sInf is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} (F : Filter.{u1} ι) [_inst_2 : CompleteLattice.{u2} R] (a : ι -> R), Eq.{succ u2} R (Filter.liminf.{u2, u1} R ι (CompleteLattice.toConditionallyCompleteLattice.{u2} R _inst_2) a F) (SupSet.sSup.{u2} R (ConditionallyCompleteLattice.toHasSup.{u2} R (CompleteLattice.toConditionallyCompleteLattice.{u2} R _inst_2)) (Set.image.{u1, u2} (Set.{u1} ι) R (fun (I : Set.{u1} ι) => InfSet.sInf.{u2} R (ConditionallyCompleteLattice.toHasInf.{u2} R (CompleteLattice.toConditionallyCompleteLattice.{u2} R _inst_2)) (Set.image.{u1, u2} ι R a I)) (Filter.sets.{u1} ι F)))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} (F : Filter.{u2} ι) [_inst_2 : CompleteLattice.{u1} R] (a : ι -> R), Eq.{succ u1} R (Filter.liminf.{u1, u2} R ι (CompleteLattice.toConditionallyCompleteLattice.{u1} R _inst_2) a F) (SupSet.sSup.{u1} R (ConditionallyCompleteLattice.toSupSet.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R _inst_2)) (Set.image.{u2, u1} (Set.{u2} ι) R (fun (I : Set.{u2} ι) => InfSet.sInf.{u1} R (ConditionallyCompleteLattice.toInfSet.{u1} R (CompleteLattice.toConditionallyCompleteLattice.{u1} R _inst_2)) (Set.image.{u2, u1} ι R a I)) (Filter.sets.{u2} ι F)))
Case conversion may be inaccurate. Consider using '#align filter.liminf_eq_Sup_Inf Filter.liminf_eq_sSup_sInfₓ'. -/
theorem liminf_eq_sSup_sInf {ι R : Type _} (F : Filter ι) [CompleteLattice R] (a : ι → R) :
    liminf a F = sSup ((fun I => sInf (a '' I)) '' F.sets) :=
  @Filter.limsup_eq_sInf_sSup ι (OrderDual R) _ _ a
#align filter.liminf_eq_Sup_Inf Filter.liminf_eq_sSup_sInf

#print Filter.liminf_nat_add /-
@[simp]
theorem liminf_nat_add (f : ℕ → α) (k : ℕ) : liminf (fun i => f (i + k)) atTop = liminf f atTop :=
  by
  simp_rw [liminf_eq_supr_infi_of_nat]
  exact iSup_iInf_ge_nat_add f k
#align filter.liminf_nat_add Filter.liminf_nat_add
-/

#print Filter.limsup_nat_add /-
@[simp]
theorem limsup_nat_add (f : ℕ → α) (k : ℕ) : limsup (fun i => f (i + k)) atTop = limsup f atTop :=
  @liminf_nat_add αᵒᵈ _ f k
#align filter.limsup_nat_add Filter.limsup_nat_add
-/

/- warning: filter.liminf_le_of_frequently_le' -> Filter.liminf_le_of_frequently_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CompleteLattice.{u2} β] {f : Filter.{u1} α} {u : α -> β} {x : β}, (Filter.Frequently.{u1} α (fun (a : α) => LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (u a) x) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Filter.liminf.{u2, u1} β α (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2) u f) x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CompleteLattice.{u1} β] {f : Filter.{u2} α} {u : α -> β} {x : β}, (Filter.Frequently.{u2} α (fun (a : α) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2)))) (u a) x) f) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2)))) (Filter.liminf.{u1, u2} β α (CompleteLattice.toConditionallyCompleteLattice.{u1} β _inst_2) u f) x)
Case conversion may be inaccurate. Consider using '#align filter.liminf_le_of_frequently_le' Filter.liminf_le_of_frequently_le'ₓ'. -/
theorem liminf_le_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, u a ≤ x) : liminf u f ≤ x :=
  by
  rw [liminf_eq]
  refine' sSup_le fun b hb => _
  have hbx : ∃ᶠ a in f, b ≤ x := by
    revert h
    rw [← not_imp_not, not_frequently, not_frequently]
    exact fun h => hb.mp (h.mono fun a hbx hba hax => hbx (hba.trans hax))
  exact hbx.exists.some_spec
#align filter.liminf_le_of_frequently_le' Filter.liminf_le_of_frequently_le'

/- warning: filter.le_limsup_of_frequently_le' -> Filter.le_limsup_of_frequently_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : CompleteLattice.{u2} β] {f : Filter.{u1} α} {u : α -> β} {x : β}, (Filter.Frequently.{u1} α (fun (a : α) => LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x (u a)) f) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) x (Filter.limsup.{u2, u1} β α (CompleteLattice.toConditionallyCompleteLattice.{u2} β _inst_2) u f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : CompleteLattice.{u1} β] {f : Filter.{u2} α} {u : α -> β} {x : β}, (Filter.Frequently.{u2} α (fun (a : α) => LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2)))) x (u a)) f) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (CompleteSemilatticeInf.toPartialOrder.{u1} β (CompleteLattice.toCompleteSemilatticeInf.{u1} β _inst_2)))) x (Filter.limsup.{u1, u2} β α (CompleteLattice.toConditionallyCompleteLattice.{u1} β _inst_2) u f))
Case conversion may be inaccurate. Consider using '#align filter.le_limsup_of_frequently_le' Filter.le_limsup_of_frequently_le'ₓ'. -/
theorem le_limsup_of_frequently_le' {α β} [CompleteLattice β] {f : Filter α} {u : α → β} {x : β}
    (h : ∃ᶠ a in f, x ≤ u a) : x ≤ limsup u f :=
  @liminf_le_of_frequently_le' _ βᵒᵈ _ _ _ _ h
#align filter.le_limsup_of_frequently_le' Filter.le_limsup_of_frequently_le'

/- warning: filter.complete_lattice_hom.apply_limsup_iterate -> Filter.CompleteLatticeHom.apply_limsup_iterate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) f (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))) (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (a : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) a) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))) (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))) (Filter.limsup.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align filter.complete_lattice_hom.apply_limsup_iterate Filter.CompleteLatticeHom.apply_limsup_iterateₓ'. -/
/-- If `f : α → α` is a morphism of complete lattices, then the limsup of its iterates of any
`a : α` is a fixed point. -/
@[simp]
theorem CompleteLatticeHom.apply_limsup_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (limsup (fun n => (f^[n]) a) atTop) = limsup (fun n => (f^[n]) a) atTop :=
  by
  rw [limsup_eq_infi_supr_of_nat', map_iInf]
  simp_rw [_root_.map_supr, ← Function.comp_apply f, ← Function.iterate_succ' f, ← Nat.add_succ]
  conv_rhs => rw [iInf_split _ ((· < ·) (0 : ℕ))]
  simp only [not_lt, le_zero_iff, iInf_iInf_eq_left, add_zero, iInf_nat_gt_zero_eq, left_eq_inf]
  refine' (iInf_le (fun i => ⨆ j, (f^[j + (i + 1)]) a) 0).trans _
  simp only [zero_add, Function.comp_apply, iSup_le_iff]
  exact fun i => le_iSup (fun i => (f^[i]) a) (i + 1)
#align filter.complete_lattice_hom.apply_limsup_iterate Filter.CompleteLatticeHom.apply_limsup_iterate

/- warning: filter.complete_lattice_hom.apply_liminf_iterate -> Filter.CompleteLatticeHom.apply_liminf_iterate is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) f (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))) (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (f : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (a : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) a) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))) (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))) (Filter.liminf.{u1, 0} α Nat (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) (fun (n : Nat) => Nat.iterate.{succ u1} α (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) f) n a) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))))
Case conversion may be inaccurate. Consider using '#align filter.complete_lattice_hom.apply_liminf_iterate Filter.CompleteLatticeHom.apply_liminf_iterateₓ'. -/
/-- If `f : α → α` is a morphism of complete lattices, then the liminf of its iterates of any
`a : α` is a fixed point. -/
theorem CompleteLatticeHom.apply_liminf_iterate (f : CompleteLatticeHom α α) (a : α) :
    f (liminf (fun n => (f^[n]) a) atTop) = liminf (fun n => (f^[n]) a) atTop :=
  (CompleteLatticeHom.dual f).apply_limsup_iterate _
#align filter.complete_lattice_hom.apply_liminf_iterate Filter.CompleteLatticeHom.apply_liminf_iterate

variable {f g : Filter β} {p q : β → Prop} {u v : β → α}

/- warning: filter.blimsup_mono -> Filter.blimsup_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (forall (x : β), (p x) -> (q x)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (forall (x : β), (p x) -> (q x)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f q))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_mono Filter.blimsup_monoₓ'. -/
theorem blimsup_mono (h : ∀ x, p x → q x) : blimsup u f p ≤ blimsup u f q :=
  sInf_le_sInf fun a ha => ha.mono <| by tauto
#align filter.blimsup_mono Filter.blimsup_mono

/- warning: filter.bliminf_antitone -> Filter.bliminf_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (forall (x : β), (p x) -> (q x)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, (forall (x : β), (p x) -> (q x)) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f q) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_antitone Filter.bliminf_antitoneₓ'. -/
theorem bliminf_antitone (h : ∀ x, p x → q x) : bliminf u f q ≤ bliminf u f p :=
  sSup_le_sSup fun a ha => ha.mono <| by tauto
#align filter.bliminf_antitone Filter.bliminf_antitone

/- warning: filter.mono_blimsup' -> Filter.mono_blimsup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (p x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (u x) (v x))) f) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) v f p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (p x) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (u x) (v x))) f) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) v f p))
Case conversion may be inaccurate. Consider using '#align filter.mono_blimsup' Filter.mono_blimsup'ₓ'. -/
theorem mono_blimsup' (h : ∀ᶠ x in f, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  sInf_le_sInf fun a ha => (ha.And h).mono fun x hx hx' => (hx.2 hx').trans (hx.1 hx')
#align filter.mono_blimsup' Filter.mono_blimsup'

/- warning: filter.mono_blimsup -> Filter.mono_blimsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (forall (x : β), (p x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (u x) (v x))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) v f p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (forall (x : β), (p x) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (u x) (v x))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) v f p))
Case conversion may be inaccurate. Consider using '#align filter.mono_blimsup Filter.mono_blimsupₓ'. -/
theorem mono_blimsup (h : ∀ x, p x → u x ≤ v x) : blimsup u f p ≤ blimsup v f p :=
  mono_blimsup' <| eventually_of_forall h
#align filter.mono_blimsup Filter.mono_blimsup

/- warning: filter.mono_bliminf' -> Filter.mono_bliminf' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (p x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (u x) (v x))) f) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) v f p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (Filter.Eventually.{u2} β (fun (x : β) => (p x) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (u x) (v x))) f) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) v f p))
Case conversion may be inaccurate. Consider using '#align filter.mono_bliminf' Filter.mono_bliminf'ₓ'. -/
theorem mono_bliminf' (h : ∀ᶠ x in f, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  sSup_le_sSup fun a ha => (ha.And h).mono fun x hx hx' => (hx.1 hx').trans (hx.2 hx')
#align filter.mono_bliminf' Filter.mono_bliminf'

/- warning: filter.mono_bliminf -> Filter.mono_bliminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (forall (x : β), (p x) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (u x) (v x))) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) v f p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {u : β -> α} {v : β -> α}, (forall (x : β), (p x) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (u x) (v x))) -> (LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) v f p))
Case conversion may be inaccurate. Consider using '#align filter.mono_bliminf Filter.mono_bliminfₓ'. -/
theorem mono_bliminf (h : ∀ x, p x → u x ≤ v x) : bliminf u f p ≤ bliminf v f p :=
  mono_bliminf' <| eventually_of_forall h
#align filter.mono_bliminf Filter.mono_bliminf

/- warning: filter.bliminf_antitone_filter -> Filter.bliminf_antitone_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {g : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toHasLe.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) f g) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u g p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {g : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) f g) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u g p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_antitone_filter Filter.bliminf_antitone_filterₓ'. -/
theorem bliminf_antitone_filter (h : f ≤ g) : bliminf u g p ≤ bliminf u f p :=
  sSup_le_sSup fun a ha => ha.filter_mono h
#align filter.bliminf_antitone_filter Filter.bliminf_antitone_filter

/- warning: filter.blimsup_monotone_filter -> Filter.blimsup_monotone_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {g : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toHasLe.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.partialOrder.{u2} β))) f g) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u g p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {g : Filter.{u2} β} {p : β -> Prop} {u : β -> α}, (LE.le.{u2} (Filter.{u2} β) (Preorder.toLE.{u2} (Filter.{u2} β) (PartialOrder.toPreorder.{u2} (Filter.{u2} β) (Filter.instPartialOrderFilter.{u2} β))) f g) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u g p))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_monotone_filter Filter.blimsup_monotone_filterₓ'. -/
theorem blimsup_monotone_filter (h : f ≤ g) : blimsup u f p ≤ blimsup u g p :=
  sInf_le_sInf fun a ha => ha.filter_mono h
#align filter.blimsup_monotone_filter Filter.blimsup_monotone_filter

/- warning: filter.blimsup_and_le_inf -> Filter.blimsup_and_le_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => And (p x) (q x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f (fun (x : β) => And (p x) (q x))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1))) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f q))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_and_le_inf Filter.blimsup_and_le_infₓ'. -/
@[simp]
theorem blimsup_and_le_inf : (blimsup u f fun x => p x ∧ q x) ≤ blimsup u f p ⊓ blimsup u f q :=
  le_inf (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)
#align filter.blimsup_and_le_inf Filter.blimsup_and_le_inf

/- warning: filter.bliminf_sup_le_and -> Filter.bliminf_sup_le_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q)) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => And (p x) (q x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)))) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f q)) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f (fun (x : β) => And (p x) (q x)))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_sup_le_and Filter.bliminf_sup_le_andₓ'. -/
@[simp]
theorem bliminf_sup_le_and : bliminf u f p ⊔ bliminf u f q ≤ bliminf u f fun x => p x ∧ q x :=
  @blimsup_and_le_inf αᵒᵈ β _ f p q u
#align filter.bliminf_sup_le_and Filter.bliminf_sup_le_and

/- warning: filter.blimsup_sup_le_or -> Filter.blimsup_sup_le_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q)) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => Or (p x) (q x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)))) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f q)) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f (fun (x : β) => Or (p x) (q x)))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_sup_le_or Filter.blimsup_sup_le_orₓ'. -/
/-- See also `filter.blimsup_or_eq_sup`. -/
@[simp]
theorem blimsup_sup_le_or : blimsup u f p ⊔ blimsup u f q ≤ blimsup u f fun x => p x ∨ q x :=
  sup_le (blimsup_mono <| by tauto) (blimsup_mono <| by tauto)
#align filter.blimsup_sup_le_or Filter.blimsup_sup_le_or

/- warning: filter.bliminf_or_le_inf -> Filter.bliminf_or_le_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f (fun (x : β) => Or (p x) (q x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f q))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f (fun (x : β) => Or (p x) (q x))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1))) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f q))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_or_le_inf Filter.bliminf_or_le_infₓ'. -/
/-- See also `filter.bliminf_or_eq_inf`. -/
@[simp]
theorem bliminf_or_le_inf : (bliminf u f fun x => p x ∨ q x) ≤ bliminf u f p ⊓ bliminf u f q :=
  @blimsup_sup_le_or αᵒᵈ β _ f p q u
#align filter.bliminf_or_le_inf Filter.bliminf_or_le_inf

/- warning: filter.order_iso.apply_blimsup -> Filter.OrderIso.apply_blimsup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.order_iso.apply_blimsup Filter.OrderIso.apply_blimsupₓ'. -/
theorem OrderIso.apply_blimsup [CompleteLattice γ] (e : α ≃o γ) :
    e (blimsup u f p) = blimsup (e ∘ u) f p :=
  by
  simp only [blimsup_eq, map_Inf, Function.comp_apply]
  congr
  ext c
  obtain ⟨a, rfl⟩ := e.surjective c
  simp
#align filter.order_iso.apply_blimsup Filter.OrderIso.apply_blimsup

/- warning: filter.order_iso.apply_bliminf -> Filter.OrderIso.apply_bliminf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.order_iso.apply_bliminf Filter.OrderIso.apply_bliminfₓ'. -/
theorem OrderIso.apply_bliminf [CompleteLattice γ] (e : α ≃o γ) :
    e (bliminf u f p) = bliminf (e ∘ u) f p :=
  @OrderIso.apply_blimsup αᵒᵈ β γᵒᵈ _ f p u _ e.dual
#align filter.order_iso.apply_bliminf Filter.OrderIso.apply_bliminf

/- warning: filter.Sup_hom.apply_blimsup_le -> Filter.SupHom.apply_blimsup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} [_inst_2 : CompleteLattice.{u3} γ] (g : sSupHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))), LE.le.{u3} γ (Preorder.toHasLe.{u3} γ (PartialOrder.toPreorder.{u3} γ (CompleteSemilatticeInf.toPartialOrder.{u3} γ (CompleteLattice.toCompleteSemilatticeInf.{u3} γ _inst_2)))) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) (fun (_x : sSupHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) => α -> γ) (sSupHom.hasCoeToFun.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) g (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p)) (Filter.blimsup.{u3, u2} γ β (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2) (Function.comp.{succ u2, succ u1, succ u3} β α γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) (fun (_x : sSupHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) => α -> γ) (sSupHom.hasCoeToFun.{u1, u3} α γ (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) g) u) f p)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {u : β -> α} [_inst_2 : CompleteLattice.{u3} γ] (g : sSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))), LE.le.{u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p)) (Preorder.toLE.{u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p)) (PartialOrder.toPreorder.{u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p)) (CompleteSemilatticeInf.toPartialOrder.{u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p)) (CompleteLattice.toCompleteSemilatticeInf.{u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p)) _inst_2)))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (sSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (sSupHomClass.toFunLike.{max u2 u3, u2, u3} (sSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)) (sSupHom.instSSupHomClassSSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)))) g (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p)) (Filter.blimsup.{u3, u1} γ β (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2) (Function.comp.{succ u1, succ u2, succ u3} β α γ (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (sSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (sSupHomClass.toFunLike.{max u2 u3, u2, u3} (sSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)) (sSupHom.instSSupHomClassSSupHom.{u2, u3} α γ (ConditionallyCompleteLattice.toSupSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)))) g) u) f p)
Case conversion may be inaccurate. Consider using '#align filter.Sup_hom.apply_blimsup_le Filter.SupHom.apply_blimsup_leₓ'. -/
theorem SupHom.apply_blimsup_le [CompleteLattice γ] (g : sSupHom α γ) :
    g (blimsup u f p) ≤ blimsup (g ∘ u) f p :=
  by
  simp only [blimsup_eq_infi_bsupr]
  refine' ((OrderHomClass.mono g).map_iInf₂_le _).trans _
  simp only [_root_.map_supr]
#align filter.Sup_hom.apply_blimsup_le Filter.SupHom.apply_blimsup_le

/- warning: filter.Inf_hom.le_apply_bliminf -> Filter.InfHom.le_apply_bliminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {u : β -> α} [_inst_2 : CompleteLattice.{u3} γ] (g : sInfHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))), LE.le.{u3} γ (Preorder.toHasLe.{u3} γ (PartialOrder.toPreorder.{u3} γ (CompleteSemilatticeInf.toPartialOrder.{u3} γ (CompleteLattice.toCompleteSemilatticeInf.{u3} γ _inst_2)))) (Filter.bliminf.{u3, u2} γ β (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2) (Function.comp.{succ u2, succ u1, succ u3} β α γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) (fun (_x : sInfHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) => α -> γ) (sInfHom.hasCoeToFun.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) g) u) f p) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) (fun (_x : sInfHom.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) => α -> γ) (sInfHom.hasCoeToFun.{u1, u3} α γ (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (ConditionallyCompleteLattice.toHasInf.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) g (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1) u f p))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {u : β -> α} [_inst_2 : CompleteLattice.{u3} γ] (g : sInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))), LE.le.{u3} γ (Preorder.toLE.{u3} γ (PartialOrder.toPreorder.{u3} γ (CompleteSemilatticeInf.toPartialOrder.{u3} γ (CompleteLattice.toCompleteSemilatticeInf.{u3} γ _inst_2)))) (Filter.bliminf.{u3, u1} γ β (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2) (Function.comp.{succ u1, succ u2, succ u3} β α γ (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (sInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) _x) (sInfHomClass.toFunLike.{max u2 u3, u2, u3} (sInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)) (sInfHom.instSInfHomClassSInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)))) g) u) f p) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (sInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) _x) (sInfHomClass.toFunLike.{max u2 u3, u2, u3} (sInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2))) α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)) (sInfHom.instSInfHomClassSInfHom.{u2, u3} α γ (ConditionallyCompleteLattice.toInfSet.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1)) (ConditionallyCompleteLattice.toInfSet.{u3} γ (CompleteLattice.toConditionallyCompleteLattice.{u3} γ _inst_2)))) g (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α _inst_1) u f p))
Case conversion may be inaccurate. Consider using '#align filter.Inf_hom.le_apply_bliminf Filter.InfHom.le_apply_bliminfₓ'. -/
theorem InfHom.le_apply_bliminf [CompleteLattice γ] (g : sInfHom α γ) :
    bliminf (g ∘ u) f p ≤ g (bliminf u f p) :=
  @SupHom.apply_blimsup_le αᵒᵈ β γᵒᵈ _ f p u _ g.dual
#align filter.Inf_hom.le_apply_bliminf Filter.InfHom.le_apply_bliminf

end CompleteLattice

section CompleteDistribLattice

variable [CompleteDistribLattice α] {f : Filter β} {p q : β → Prop} {u : β → α}

/- warning: filter.blimsup_or_eq_sup -> Filter.blimsup_or_eq_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, Eq.{succ u1} α (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f (fun (x : β) => Or (p x) (q x))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f p) (Filter.blimsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f q))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteDistribLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, Eq.{succ u2} α (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f (fun (x : β) => Or (p x) (q x))) (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1)))))) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f p) (Filter.blimsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f q))
Case conversion may be inaccurate. Consider using '#align filter.blimsup_or_eq_sup Filter.blimsup_or_eq_supₓ'. -/
@[simp]
theorem blimsup_or_eq_sup : (blimsup u f fun x => p x ∨ q x) = blimsup u f p ⊔ blimsup u f q :=
  by
  refine' le_antisymm _ blimsup_sup_le_or
  simp only [blimsup_eq, sInf_sup_eq, sup_sInf_eq, le_iInf₂_iff, mem_set_of_eq]
  refine' fun a' ha' a ha => sInf_le ((ha.And ha').mono fun b h hb => _)
  exact Or.elim hb (fun hb => le_sup_of_le_left <| h.1 hb) fun hb => le_sup_of_le_right <| h.2 hb
#align filter.blimsup_or_eq_sup Filter.blimsup_or_eq_sup

/- warning: filter.bliminf_or_eq_inf -> Filter.bliminf_or_eq_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, Eq.{succ u1} α (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f (fun (x : β) => Or (p x) (q x))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f p) (Filter.bliminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f q))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteDistribLattice.{u2} α] {f : Filter.{u1} β} {p : β -> Prop} {q : β -> Prop} {u : β -> α}, Eq.{succ u2} α (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f (fun (x : β) => Or (p x) (q x))) (Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))))) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f p) (Filter.bliminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f q))
Case conversion may be inaccurate. Consider using '#align filter.bliminf_or_eq_inf Filter.bliminf_or_eq_infₓ'. -/
@[simp]
theorem bliminf_or_eq_inf : (bliminf u f fun x => p x ∨ q x) = bliminf u f p ⊓ bliminf u f q :=
  @blimsup_or_eq_sup αᵒᵈ β _ f p q u
#align filter.bliminf_or_eq_inf Filter.bliminf_or_eq_inf

/- warning: filter.sup_limsup -> Filter.sup_limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) (fun (x : β) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (u x)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) (fun (x : β) => Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (u x)) f)
Case conversion may be inaccurate. Consider using '#align filter.sup_limsup Filter.sup_limsupₓ'. -/
theorem sup_limsup [NeBot f] (a : α) : a ⊔ limsup u f = limsup (fun x => a ⊔ u x) f :=
  by
  simp only [limsup_eq_infi_supr, iSup_sup_eq, sup_iInf₂_eq]
  congr ; ext s; congr ; ext hs; congr
  exact (biSup_const (nonempty_of_mem hs)).symm
#align filter.sup_limsup Filter.sup_limsup

/- warning: filter.inf_liminf -> Filter.inf_liminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) (fun (x : β) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (u x)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))))) a (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) (fun (x : β) => Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))))) a (u x)) f)
Case conversion may be inaccurate. Consider using '#align filter.inf_liminf Filter.inf_liminfₓ'. -/
theorem inf_liminf [NeBot f] (a : α) : a ⊓ liminf u f = liminf (fun x => a ⊓ u x) f :=
  @sup_limsup αᵒᵈ β _ f _ _ _
#align filter.inf_liminf Filter.inf_liminf

/- warning: filter.sup_liminf -> Filter.sup_liminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} (a : α), Eq.{succ u1} α (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) (fun (x : β) => Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (u x)) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteDistribLattice.{u2} α] {f : Filter.{u1} β} {u : β -> α} (a : α), Eq.{succ u2} α (Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1)))))) a (Filter.liminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f)) (Filter.liminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) (fun (x : β) => Sup.sup.{u2} α (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1)))))) a (u x)) f)
Case conversion may be inaccurate. Consider using '#align filter.sup_liminf Filter.sup_liminfₓ'. -/
theorem sup_liminf (a : α) : a ⊔ liminf u f = liminf (fun x => a ⊔ u x) f :=
  by
  simp only [liminf_eq_supr_infi]
  rw [sup_comm, biSup_sup (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [iInf₂_sup_eq, @sup_comm _ _ a]
#align filter.sup_liminf Filter.sup_liminf

/- warning: filter.inf_limsup -> Filter.inf_limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteDistribLattice.{u1} α] {f : Filter.{u2} β} {u : β -> α} (a : α), Eq.{succ u1} α (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) u f)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1))) (fun (x : β) => Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α _inst_1)))))) a (u x)) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteDistribLattice.{u2} α] {f : Filter.{u1} β} {u : β -> α} (a : α), Eq.{succ u2} α (Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))))) a (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) u f)) (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))) (fun (x : β) => Inf.inf.{u2} α (Lattice.toInf.{u2} α (ConditionallyCompleteLattice.toLattice.{u2} α (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α _inst_1))))) a (u x)) f)
Case conversion may be inaccurate. Consider using '#align filter.inf_limsup Filter.inf_limsupₓ'. -/
theorem inf_limsup (a : α) : a ⊓ limsup u f = limsup (fun x => a ⊓ u x) f :=
  @sup_liminf αᵒᵈ β _ f _ _
#align filter.inf_limsup Filter.inf_limsup

end CompleteDistribLattice

section CompleteBooleanAlgebra

variable [CompleteBooleanAlgebra α] (f : Filter β) (u : β → α)

/- warning: filter.limsup_compl -> Filter.limsup_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α), Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (Function.comp.{succ u2, succ u1, succ u1} β α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) u) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u2} α] (f : Filter.{u1} β) (u : β -> α), Eq.{succ u2} α (HasCompl.compl.{u2} α (BooleanAlgebra.toHasCompl.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1)) (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) u f)) (Filter.liminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) (Function.comp.{succ u1, succ u2, succ u2} β α α (HasCompl.compl.{u2} α (BooleanAlgebra.toHasCompl.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1))) u) f)
Case conversion may be inaccurate. Consider using '#align filter.limsup_compl Filter.limsup_complₓ'. -/
theorem limsup_compl : limsup u fᶜ = liminf (compl ∘ u) f := by
  simp only [limsup_eq_infi_supr, liminf_eq_supr_infi, compl_iInf, compl_iSup]
#align filter.limsup_compl Filter.limsup_compl

/- warning: filter.liminf_compl -> Filter.liminf_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α), Eq.{succ u1} α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (Function.comp.{succ u2, succ u1, succ u1} β α α (HasCompl.compl.{u1} α (BooleanAlgebra.toHasCompl.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1))) u) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u2} α] (f : Filter.{u1} β) (u : β -> α), Eq.{succ u2} α (HasCompl.compl.{u2} α (BooleanAlgebra.toHasCompl.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1)) (Filter.liminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) u f)) (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) (Function.comp.{succ u1, succ u2, succ u2} β α α (HasCompl.compl.{u2} α (BooleanAlgebra.toHasCompl.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1))) u) f)
Case conversion may be inaccurate. Consider using '#align filter.liminf_compl Filter.liminf_complₓ'. -/
theorem liminf_compl : liminf u fᶜ = limsup (compl ∘ u) f := by
  simp only [limsup_eq_infi_supr, liminf_eq_supr_infi, compl_iInf, compl_iSup]
#align filter.liminf_compl Filter.liminf_compl

/- warning: filter.limsup_sdiff -> Filter.limsup_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α) (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f) a) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (u b) a) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u2} α] (f : Filter.{u1} β) (u : β -> α) (a : α), Eq.{succ u2} α (SDiff.sdiff.{u2} α (BooleanAlgebra.toSDiff.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1)) (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) u f) a) (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u2} α (BooleanAlgebra.toSDiff.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1)) (u b) a) f)
Case conversion may be inaccurate. Consider using '#align filter.limsup_sdiff Filter.limsup_sdiffₓ'. -/
theorem limsup_sdiff (a : α) : limsup u f \ a = limsup (fun b => u b \ a) f :=
  by
  simp only [limsup_eq_infi_supr, sdiff_eq]
  rw [biInf_inf (⟨univ, univ_mem⟩ : ∃ i : Set β, i ∈ f)]
  simp_rw [inf_comm, inf_iSup₂_eq, inf_comm]
#align filter.limsup_sdiff Filter.limsup_sdiff

/- warning: filter.liminf_sdiff -> Filter.liminf_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α) [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f) a) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (u b) a) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α) [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f) a) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) (u b) a) f)
Case conversion may be inaccurate. Consider using '#align filter.liminf_sdiff Filter.liminf_sdiffₓ'. -/
theorem liminf_sdiff [NeBot f] (a : α) : liminf u f \ a = liminf (fun b => u b \ a) f := by
  simp only [sdiff_eq, @inf_comm _ _ _ (aᶜ), inf_liminf]
#align filter.liminf_sdiff Filter.liminf_sdiff

/- warning: filter.sdiff_limsup -> Filter.sdiff_limsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α) [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) a (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) a (u b)) f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α) [_inst_2 : Filter.NeBot.{u2} β f] (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) a (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f)) (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u1} α (BooleanAlgebra.toSDiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) a (u b)) f)
Case conversion may be inaccurate. Consider using '#align filter.sdiff_limsup Filter.sdiff_limsupₓ'. -/
theorem sdiff_limsup [NeBot f] (a : α) : a \ limsup u f = liminf (fun b => a \ u b) f :=
  by
  rw [← compl_inj_iff]
  simp only [sdiff_eq, liminf_compl, (· ∘ ·), compl_inf, compl_compl, sup_limsup]
#align filter.sdiff_limsup Filter.sdiff_limsup

/- warning: filter.sdiff_liminf -> Filter.sdiff_liminf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteBooleanAlgebra.{u1} α] (f : Filter.{u2} β) (u : β -> α) (a : α), Eq.{succ u1} α (SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) a (Filter.liminf.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) u f)) (Filter.limsup.{u1, u2} α β (CompleteLattice.toConditionallyCompleteLattice.{u1} α (Order.Coframe.toCompleteLattice.{u1} α (CompleteDistribLattice.toCoframe.{u1} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u1} α (BooleanAlgebra.toHasSdiff.{u1} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u1} α _inst_1)) a (u b)) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteBooleanAlgebra.{u2} α] (f : Filter.{u1} β) (u : β -> α) (a : α), Eq.{succ u2} α (SDiff.sdiff.{u2} α (BooleanAlgebra.toSDiff.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1)) a (Filter.liminf.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) u f)) (Filter.limsup.{u2, u1} α β (CompleteLattice.toConditionallyCompleteLattice.{u2} α (Order.Coframe.toCompleteLattice.{u2} α (CompleteDistribLattice.toCoframe.{u2} α (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} α _inst_1)))) (fun (b : β) => SDiff.sdiff.{u2} α (BooleanAlgebra.toSDiff.{u2} α (CompleteBooleanAlgebra.toBooleanAlgebra.{u2} α _inst_1)) a (u b)) f)
Case conversion may be inaccurate. Consider using '#align filter.sdiff_liminf Filter.sdiff_liminfₓ'. -/
theorem sdiff_liminf (a : α) : a \ liminf u f = limsup (fun b => a \ u b) f :=
  by
  rw [← compl_inj_iff]
  simp only [sdiff_eq, limsup_compl, (· ∘ ·), compl_inf, compl_compl, sup_liminf]
#align filter.sdiff_liminf Filter.sdiff_liminf

end CompleteBooleanAlgebra

section SetLattice

variable {p : ι → Prop} {s : ι → Set α}

/- warning: filter.cofinite.blimsup_set_eq -> Filter.cofinite.blimsup_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Filter.blimsup.{u1, u2} (Set.{u1} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.cofinite.{u2} ι) p) (setOf.{u1} α (fun (x : α) => Set.Infinite.{u2} ι (setOf.{u2} ι (fun (n : ι) => And (p n) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, Eq.{succ u2} (Set.{u2} α) (Filter.blimsup.{u2, u1} (Set.{u2} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) s (Filter.cofinite.{u1} ι) p) (setOf.{u2} α (fun (x : α) => Set.Infinite.{u1} ι (setOf.{u1} ι (fun (n : ι) => And (p n) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s n))))))
Case conversion may be inaccurate. Consider using '#align filter.cofinite.blimsup_set_eq Filter.cofinite.blimsup_set_eqₓ'. -/
theorem cofinite.blimsup_set_eq : blimsup s cofinite p = { x | { n | p n ∧ x ∈ s n }.Infinite } :=
  by
  simp only [blimsup_eq, le_eq_subset, eventually_cofinite, not_forall, Inf_eq_sInter, exists_prop]
  ext x
  refine' ⟨fun h => _, fun hx t h => _⟩ <;> contrapose! h
  · simp only [mem_sInter, mem_set_of_eq, not_forall, exists_prop]
    exact ⟨{x}ᶜ, by simpa using h, by simp⟩
  · exact hx.mono fun i hi => ⟨hi.1, fun hit => h (hit hi.2)⟩
#align filter.cofinite.blimsup_set_eq Filter.cofinite.blimsup_set_eq

/- warning: filter.cofinite.bliminf_set_eq -> Filter.cofinite.bliminf_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {p : ι -> Prop} {s : ι -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Filter.bliminf.{u1, u2} (Set.{u1} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.cofinite.{u2} ι) p) (setOf.{u1} α (fun (x : α) => Set.Finite.{u2} ι (setOf.{u2} ι (fun (n : ι) => And (p n) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n)))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {p : ι -> Prop} {s : ι -> (Set.{u2} α)}, Eq.{succ u2} (Set.{u2} α) (Filter.bliminf.{u2, u1} (Set.{u2} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) s (Filter.cofinite.{u1} ι) p) (setOf.{u2} α (fun (x : α) => Set.Finite.{u1} ι (setOf.{u1} ι (fun (n : ι) => And (p n) (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s n)))))))
Case conversion may be inaccurate. Consider using '#align filter.cofinite.bliminf_set_eq Filter.cofinite.bliminf_set_eqₓ'. -/
theorem cofinite.bliminf_set_eq : bliminf s cofinite p = { x | { n | p n ∧ x ∉ s n }.Finite } :=
  by
  rw [← compl_inj_iff]
  simpa only [bliminf_eq_supr_binfi, compl_iInf, compl_iSup, ← blimsup_eq_infi_bsupr,
    cofinite.blimsup_set_eq]
#align filter.cofinite.bliminf_set_eq Filter.cofinite.bliminf_set_eq

/- warning: filter.cofinite.limsup_set_eq -> Filter.cofinite.limsup_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : ι -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Filter.limsup.{u1, u2} (Set.{u1} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.cofinite.{u2} ι)) (setOf.{u1} α (fun (x : α) => Set.Infinite.{u2} ι (setOf.{u2} ι (fun (n : ι) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : ι -> (Set.{u2} α)}, Eq.{succ u2} (Set.{u2} α) (Filter.limsup.{u2, u1} (Set.{u2} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) s (Filter.cofinite.{u1} ι)) (setOf.{u2} α (fun (x : α) => Set.Infinite.{u1} ι (setOf.{u1} ι (fun (n : ι) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s n)))))
Case conversion may be inaccurate. Consider using '#align filter.cofinite.limsup_set_eq Filter.cofinite.limsup_set_eqₓ'. -/
/-- In other words, `limsup cofinite s` is the set of elements lying inside the family `s`
infinitely often. -/
theorem cofinite.limsup_set_eq : limsup s cofinite = { x | { n | x ∈ s n }.Infinite } := by
  simp only [← cofinite.blimsup_true s, cofinite.blimsup_set_eq, true_and_iff]
#align filter.cofinite.limsup_set_eq Filter.cofinite.limsup_set_eq

/- warning: filter.cofinite.liminf_set_eq -> Filter.cofinite.liminf_set_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {s : ι -> (Set.{u1} α)}, Eq.{succ u1} (Set.{u1} α) (Filter.liminf.{u1, u2} (Set.{u1} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) s (Filter.cofinite.{u2} ι)) (setOf.{u1} α (fun (x : α) => Set.Finite.{u2} ι (setOf.{u2} ι (fun (n : ι) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n))))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u1}} {s : ι -> (Set.{u2} α)}, Eq.{succ u2} (Set.{u2} α) (Filter.liminf.{u2, u1} (Set.{u2} α) ι (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) s (Filter.cofinite.{u1} ι)) (setOf.{u2} α (fun (x : α) => Set.Finite.{u1} ι (setOf.{u1} ι (fun (n : ι) => Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (s n))))))
Case conversion may be inaccurate. Consider using '#align filter.cofinite.liminf_set_eq Filter.cofinite.liminf_set_eqₓ'. -/
/-- In other words, `liminf cofinite s` is the set of elements lying outside the family `s`
finitely often. -/
theorem cofinite.liminf_set_eq : liminf s cofinite = { x | { n | x ∉ s n }.Finite } := by
  simp only [← cofinite.bliminf_true s, cofinite.bliminf_set_eq, true_and_iff]
#align filter.cofinite.liminf_set_eq Filter.cofinite.liminf_set_eq

/- warning: filter.exists_forall_mem_of_has_basis_mem_blimsup -> Filter.exists_forall_mem_of_hasBasis_mem_blimsup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {l : Filter.{u2} β} {b : ι -> (Set.{u2} β)} {q : ι -> Prop}, (Filter.HasBasis.{u2, succ u3} β ι l q b) -> (forall {u : β -> (Set.{u1} α)} {p : β -> Prop} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Filter.blimsup.{u1, u2} (Set.{u1} α) β (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) u l p)) -> (Exists.{max (succ u3) (succ u2)} ((coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))) -> β) (fun (f : (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))) -> β) => forall (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))), And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (u (f i))) (And (p (f i)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f i) (b ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))) ι (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))) ι (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))) ι (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) (setOf.{u3} ι (fun (i : ι) => q i))) ι (coeSubtype.{succ u3} ι (fun (x : ι) => Membership.Mem.{u3, u3} ι (Set.{u3} ι) (Set.hasMem.{u3} ι) x (setOf.{u3} ι (fun (i : ι) => q i))))))) i)))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {ι : Type.{u2}} {l : Filter.{u3} β} {b : ι -> (Set.{u3} β)} {q : ι -> Prop}, (Filter.HasBasis.{u3, succ u2} β ι l q b) -> (forall {u : β -> (Set.{u1} α)} {p : β -> Prop} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Filter.blimsup.{u1, u3} (Set.{u1} α) β (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) u l p)) -> (Exists.{max (succ u3) (succ u2)} ((Set.Elem.{u2} ι (setOf.{u2} ι (fun (i : ι) => q i))) -> β) (fun (f : (Set.Elem.{u2} ι (setOf.{u2} ι (fun (i : ι) => q i))) -> β) => forall (i : Set.Elem.{u2} ι (setOf.{u2} ι (fun (i : ι) => q i))), And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (u (f i))) (And (p (f i)) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) (f i) (b (Subtype.val.{succ u2} ι (fun (x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) x (setOf.{u2} ι (fun (i : ι) => q i))) i)))))))
Case conversion may be inaccurate. Consider using '#align filter.exists_forall_mem_of_has_basis_mem_blimsup Filter.exists_forall_mem_of_hasBasis_mem_blimsupₓ'. -/
theorem exists_forall_mem_of_hasBasis_mem_blimsup {l : Filter β} {b : ι → Set β} {q : ι → Prop}
    (hl : l.HasBasis q b) {u : β → Set α} {p : β → Prop} {x : α} (hx : x ∈ blimsup u l p) :
    ∃ f : { i | q i } → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i :=
  by
  rw [blimsup_eq_infi_bsupr] at hx
  simp only [supr_eq_Union, infi_eq_Inter, mem_Inter, mem_Union, exists_prop] at hx
  choose g hg hg' using hx
  refine' ⟨fun i : { i | q i } => g (b i) (hl.mem_of_mem i.2), fun i => ⟨_, _⟩⟩
  · exact hg' (b i) (hl.mem_of_mem i.2)
  · exact hg (b i) (hl.mem_of_mem i.2)
#align filter.exists_forall_mem_of_has_basis_mem_blimsup Filter.exists_forall_mem_of_hasBasis_mem_blimsup

/- warning: filter.exists_forall_mem_of_has_basis_mem_blimsup' -> Filter.exists_forall_mem_of_hasBasis_mem_blimsup' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {l : Filter.{u2} β} {b : ι -> (Set.{u2} β)}, (Filter.HasBasis.{u2, succ u3} β ι l (fun (_x : ι) => True) b) -> (forall {u : β -> (Set.{u1} α)} {p : β -> Prop} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Filter.blimsup.{u1, u2} (Set.{u1} α) β (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) u l p)) -> (Exists.{max (succ u3) (succ u2)} (ι -> β) (fun (f : ι -> β) => forall (i : ι), And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (u (f i))) (And (p (f i)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f i) (b i))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {ι : Type.{u2}} {l : Filter.{u3} β} {b : ι -> (Set.{u3} β)}, (Filter.HasBasis.{u3, succ u2} β ι l (fun (_x : ι) => True) b) -> (forall {u : β -> (Set.{u1} α)} {p : β -> Prop} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Filter.blimsup.{u1, u3} (Set.{u1} α) β (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) u l p)) -> (Exists.{max (succ u3) (succ u2)} (ι -> β) (fun (f : ι -> β) => forall (i : ι), And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (u (f i))) (And (p (f i)) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) (f i) (b i))))))
Case conversion may be inaccurate. Consider using '#align filter.exists_forall_mem_of_has_basis_mem_blimsup' Filter.exists_forall_mem_of_hasBasis_mem_blimsup'ₓ'. -/
theorem exists_forall_mem_of_hasBasis_mem_blimsup' {l : Filter β} {b : ι → Set β}
    (hl : l.HasBasis (fun _ => True) b) {u : β → Set α} {p : β → Prop} {x : α}
    (hx : x ∈ blimsup u l p) : ∃ f : ι → β, ∀ i, x ∈ u (f i) ∧ p (f i) ∧ f i ∈ b i :=
  by
  obtain ⟨f, hf⟩ := exists_forall_mem_of_has_basis_mem_blimsup hl hx
  exact ⟨fun i => f ⟨i, trivial⟩, fun i => hf ⟨i, trivial⟩⟩
#align filter.exists_forall_mem_of_has_basis_mem_blimsup' Filter.exists_forall_mem_of_hasBasis_mem_blimsup'

end SetLattice

section ConditionallyCompleteLinearOrder

/- warning: filter.frequently_lt_of_lt_Limsup -> Filter.frequently_lt_of_lt_limsSup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.frequently_lt_of_lt_Limsup Filter.frequently_lt_of_lt_limsSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_lt_limsSup {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≤ ·) := by
      run_tac
        is_bounded_default)
    (h : a < limsSup f) : ∃ᶠ n in f, a < n :=
  by
  contrapose! h
  simp only [not_frequently, not_lt] at h
  exact Limsup_le_of_le hf h
#align filter.frequently_lt_of_lt_Limsup Filter.frequently_lt_of_lt_limsSup

/- warning: filter.frequently_lt_of_Liminf_lt -> Filter.frequently_lt_of_limsInf_lt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.frequently_lt_of_Liminf_lt Filter.frequently_lt_of_limsInf_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_limsInf_lt {f : Filter α} [ConditionallyCompleteLinearOrder α] {a : α}
    (hf : f.IsCobounded (· ≥ ·) := by
      run_tac
        is_bounded_default)
    (h : limsInf f < a) : ∃ᶠ n in f, n < a :=
  @frequently_lt_of_lt_limsSup (OrderDual α) f _ a hf h
#align filter.frequently_lt_of_Liminf_lt Filter.frequently_lt_of_limsInf_lt

/- warning: filter.eventually_lt_of_lt_liminf -> Filter.eventually_lt_of_lt_liminf is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.eventually_lt_of_lt_liminf Filter.eventually_lt_of_lt_liminfₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem eventually_lt_of_lt_liminf {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : b < liminf u f)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ a in f, b < u a :=
  by
  obtain ⟨c, hc, hbc⟩ : ∃ (c : β)(hc : c ∈ { c : β | ∀ᶠ n : α in f, c ≤ u n }), b < c :=
    exists_lt_of_lt_csSup hu h
  exact hc.mono fun x hx => lt_of_lt_of_le hbc hx
#align filter.eventually_lt_of_lt_liminf Filter.eventually_lt_of_lt_liminf

/- warning: filter.eventually_lt_of_limsup_lt -> Filter.eventually_lt_of_limsup_lt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.eventually_lt_of_limsup_lt Filter.eventually_lt_of_limsup_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem eventually_lt_of_limsup_lt {f : Filter α} [ConditionallyCompleteLinearOrder β] {u : α → β}
    {b : β} (h : limsup u f < b)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    ∀ᶠ a in f, u a < b :=
  @eventually_lt_of_lt_liminf _ βᵒᵈ _ _ _ _ h hu
#align filter.eventually_lt_of_limsup_lt Filter.eventually_lt_of_limsup_lt

/- warning: filter.le_limsup_of_frequently_le -> Filter.le_limsup_of_frequently_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.le_limsup_of_frequently_le Filter.le_limsup_of_frequently_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem le_limsup_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β} (hu_le : ∃ᶠ x in f, b ≤ u x)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default) :
    b ≤ limsup u f := by
  revert hu_le
  rw [← not_imp_not, not_frequently]
  simp_rw [← lt_iff_not_ge]
  exact fun h => eventually_lt_of_limsup_lt h hu
#align filter.le_limsup_of_frequently_le Filter.le_limsup_of_frequently_le

/- warning: filter.liminf_le_of_frequently_le -> Filter.liminf_le_of_frequently_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.liminf_le_of_frequently_le Filter.liminf_le_of_frequently_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem liminf_le_of_frequently_le {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β} (hu_le : ∃ᶠ x in f, u x ≤ b)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default) :
    liminf u f ≤ b :=
  @le_limsup_of_frequently_le _ βᵒᵈ _ f u b hu_le hu
#align filter.liminf_le_of_frequently_le Filter.liminf_le_of_frequently_le

/- warning: filter.frequently_lt_of_lt_limsup -> Filter.frequently_lt_of_lt_limsup is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.frequently_lt_of_lt_limsup Filter.frequently_lt_of_lt_limsupₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_lt_limsup {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (h : b < limsup u f) : ∃ᶠ x in f, b < u x :=
  by
  contrapose! h
  apply Limsup_le_of_le hu
  simpa using h
#align filter.frequently_lt_of_lt_limsup Filter.frequently_lt_of_lt_limsup

/- warning: filter.frequently_lt_of_liminf_lt -> Filter.frequently_lt_of_liminf_lt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align filter.frequently_lt_of_liminf_lt Filter.frequently_lt_of_liminf_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem frequently_lt_of_liminf_lt {α β} [ConditionallyCompleteLinearOrder β] {f : Filter α}
    {u : α → β} {b : β}
    (hu : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (h : liminf u f < b) : ∃ᶠ x in f, u x < b :=
  @frequently_lt_of_lt_limsup _ βᵒᵈ _ f u b hu h
#align filter.frequently_lt_of_liminf_lt Filter.frequently_lt_of_liminf_lt

end ConditionallyCompleteLinearOrder

end Filter

section Order

open Filter

/- warning: monotone.is_bounded_under_le_comp -> Monotone.isBoundedUnder_le_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u2} β] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u3} γ] [_inst_4 : NoMaxOrder.{u3} γ (Preorder.toHasLt.{u3} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Monotone.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) _inst_3 g) -> (Filter.Tendsto.{u2, u3} β γ g (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (Filter.atTop.{u3} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u3, u1} γ α (LE.le.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) l (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Filter.IsBoundedUnder.{u2, u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) l f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Nonempty.{succ u3} β] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u2} γ] [_inst_4 : NoMaxOrder.{u2} γ (Preorder.toLT.{u2} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Monotone.{u3, u2} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2))))) _inst_3 g) -> (Filter.Tendsto.{u3, u2} β γ g (Filter.atTop.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) (Filter.atTop.{u2} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u2, u1} γ α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14292 : γ) (x._@.Mathlib.Order.LiminfLimsup._hyg.14294 : γ) => LE.le.{u2} γ (Preorder.toLE.{u2} γ _inst_3) x._@.Mathlib.Order.LiminfLimsup._hyg.14292 x._@.Mathlib.Order.LiminfLimsup._hyg.14294) l (Function.comp.{succ u1, succ u3, succ u2} α β γ g f)) (Filter.IsBoundedUnder.{u3, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14316 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.14318 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) x._@.Mathlib.Order.LiminfLimsup._hyg.14316 x._@.Mathlib.Order.LiminfLimsup._hyg.14318) l f))
Case conversion may be inaccurate. Consider using '#align monotone.is_bounded_under_le_comp Monotone.isBoundedUnder_le_compₓ'. -/
theorem Monotone.isBoundedUnder_le_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atTop atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f :=
  by
  refine' ⟨_, fun h => h.IsBoundedUnder hg⟩
  rintro ⟨c, hc⟩; rw [eventually_map] at hc
  obtain ⟨b, hb⟩ : ∃ b, ∀ a ≥ b, c < g a := eventually_at_top.1 (hg'.eventually_gt_at_top c)
  exact ⟨b, hc.mono fun x hx => not_lt.1 fun h => (hb _ h.le).not_le hx⟩
#align monotone.is_bounded_under_le_comp Monotone.isBoundedUnder_le_comp

/- warning: monotone.is_bounded_under_ge_comp -> Monotone.isBoundedUnder_ge_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u2} β] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u3} γ] [_inst_4 : NoMinOrder.{u3} γ (Preorder.toHasLt.{u3} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Monotone.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) _inst_3 g) -> (Filter.Tendsto.{u2, u3} β γ g (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (Filter.atBot.{u3} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u3, u1} γ α (GE.ge.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) l (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Filter.IsBoundedUnder.{u2, u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) l f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Nonempty.{succ u3} β] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u2} γ] [_inst_4 : NoMinOrder.{u2} γ (Preorder.toLT.{u2} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Monotone.{u3, u2} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2))))) _inst_3 g) -> (Filter.Tendsto.{u3, u2} β γ g (Filter.atBot.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) (Filter.atBot.{u2} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u2, u1} γ α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14475 : γ) (x._@.Mathlib.Order.LiminfLimsup._hyg.14477 : γ) => GE.ge.{u2} γ (Preorder.toLE.{u2} γ _inst_3) x._@.Mathlib.Order.LiminfLimsup._hyg.14475 x._@.Mathlib.Order.LiminfLimsup._hyg.14477) l (Function.comp.{succ u1, succ u3, succ u2} α β γ g f)) (Filter.IsBoundedUnder.{u3, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14499 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.14501 : β) => GE.ge.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) x._@.Mathlib.Order.LiminfLimsup._hyg.14499 x._@.Mathlib.Order.LiminfLimsup._hyg.14501) l f))
Case conversion may be inaccurate. Consider using '#align monotone.is_bounded_under_ge_comp Monotone.isBoundedUnder_ge_compₓ'. -/
theorem Monotone.isBoundedUnder_ge_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Monotone g) (hg' : Tendsto g atBot atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual.isBoundedUnder_le_comp hg'
#align monotone.is_bounded_under_ge_comp Monotone.isBoundedUnder_ge_comp

/- warning: antitone.is_bounded_under_le_comp -> Antitone.isBoundedUnder_le_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u2} β] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u3} γ] [_inst_4 : NoMaxOrder.{u3} γ (Preorder.toHasLt.{u3} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Antitone.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) _inst_3 g) -> (Filter.Tendsto.{u2, u3} β γ g (Filter.atBot.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (Filter.atTop.{u3} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u3, u1} γ α (LE.le.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) l (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Filter.IsBoundedUnder.{u2, u1} β α (GE.ge.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) l f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Nonempty.{succ u3} β] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u2} γ] [_inst_4 : NoMaxOrder.{u2} γ (Preorder.toLT.{u2} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Antitone.{u3, u2} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2))))) _inst_3 g) -> (Filter.Tendsto.{u3, u2} β γ g (Filter.atBot.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) (Filter.atTop.{u2} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u2, u1} γ α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14558 : γ) (x._@.Mathlib.Order.LiminfLimsup._hyg.14560 : γ) => LE.le.{u2} γ (Preorder.toLE.{u2} γ _inst_3) x._@.Mathlib.Order.LiminfLimsup._hyg.14558 x._@.Mathlib.Order.LiminfLimsup._hyg.14560) l (Function.comp.{succ u1, succ u3, succ u2} α β γ g f)) (Filter.IsBoundedUnder.{u3, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14582 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.14584 : β) => GE.ge.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) x._@.Mathlib.Order.LiminfLimsup._hyg.14582 x._@.Mathlib.Order.LiminfLimsup._hyg.14584) l f))
Case conversion may be inaccurate. Consider using '#align antitone.is_bounded_under_le_comp Antitone.isBoundedUnder_le_compₓ'. -/
theorem Antitone.isBoundedUnder_le_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMaxOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atBot atTop) :
    IsBoundedUnder (· ≤ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≥ ·) l f :=
  hg.dual_right.isBoundedUnder_ge_comp hg'
#align antitone.is_bounded_under_le_comp Antitone.isBoundedUnder_le_comp

/- warning: antitone.is_bounded_under_ge_comp -> Antitone.isBoundedUnder_ge_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u2} β] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : Preorder.{u3} γ] [_inst_4 : NoMinOrder.{u3} γ (Preorder.toHasLt.{u3} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Antitone.{u2, u3} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))) _inst_3 g) -> (Filter.Tendsto.{u2, u3} β γ g (Filter.atTop.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))))) (Filter.atBot.{u3} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u3, u1} γ α (GE.ge.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) l (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (Filter.IsBoundedUnder.{u2, u1} β α (LE.le.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) l f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Nonempty.{succ u3} β] [_inst_2 : LinearOrder.{u3} β] [_inst_3 : Preorder.{u2} γ] [_inst_4 : NoMinOrder.{u2} γ (Preorder.toLT.{u2} γ _inst_3)] {g : β -> γ} {f : α -> β} {l : Filter.{u1} α}, (Antitone.{u3, u2} β γ (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2))))) _inst_3 g) -> (Filter.Tendsto.{u3, u2} β γ g (Filter.atTop.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) (Filter.atBot.{u2} γ _inst_3)) -> (Iff (Filter.IsBoundedUnder.{u2, u1} γ α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14641 : γ) (x._@.Mathlib.Order.LiminfLimsup._hyg.14643 : γ) => GE.ge.{u2} γ (Preorder.toLE.{u2} γ _inst_3) x._@.Mathlib.Order.LiminfLimsup._hyg.14641 x._@.Mathlib.Order.LiminfLimsup._hyg.14643) l (Function.comp.{succ u1, succ u3, succ u2} α β γ g f)) (Filter.IsBoundedUnder.{u3, u1} β α (fun (x._@.Mathlib.Order.LiminfLimsup._hyg.14665 : β) (x._@.Mathlib.Order.LiminfLimsup._hyg.14667 : β) => LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β (Lattice.toSemilatticeInf.{u3} β (DistribLattice.toLattice.{u3} β (instDistribLattice.{u3} β _inst_2)))))) x._@.Mathlib.Order.LiminfLimsup._hyg.14665 x._@.Mathlib.Order.LiminfLimsup._hyg.14667) l f))
Case conversion may be inaccurate. Consider using '#align antitone.is_bounded_under_ge_comp Antitone.isBoundedUnder_ge_compₓ'. -/
theorem Antitone.isBoundedUnder_ge_comp [Nonempty β] [LinearOrder β] [Preorder γ] [NoMinOrder γ]
    {g : β → γ} {f : α → β} {l : Filter α} (hg : Antitone g) (hg' : Tendsto g atTop atBot) :
    IsBoundedUnder (· ≥ ·) l (g ∘ f) ↔ IsBoundedUnder (· ≤ ·) l f :=
  hg.dual_right.isBoundedUnder_le_comp hg'
#align antitone.is_bounded_under_ge_comp Antitone.isBoundedUnder_ge_comp

/- warning: galois_connection.l_limsup_le -> GaloisConnection.l_limsup_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align galois_connection.l_limsup_le GaloisConnection.l_limsup_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem GaloisConnection.l_limsup_le [ConditionallyCompleteLattice β]
    [ConditionallyCompleteLattice γ] {f : Filter α} {v : α → β} {l : β → γ} {u : γ → β}
    (gc : GaloisConnection l u)
    (hlv : f.IsBoundedUnder (· ≤ ·) fun x => l (v x) := by
      run_tac
        is_bounded_default)
    (hv_co : f.IsCoboundedUnder (· ≤ ·) v := by
      run_tac
        is_bounded_default) :
    l (limsup v f) ≤ limsup (fun x => l (v x)) f :=
  by
  refine' le_Limsup_of_le hlv fun c hc => _
  rw [Filter.eventually_map] at hc
  simp_rw [gc _ _] at hc⊢
  exact Limsup_le_of_le hv_co hc
#align galois_connection.l_limsup_le GaloisConnection.l_limsup_le

/- warning: order_iso.limsup_apply -> OrderIso.limsup_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align order_iso.limsup_apply OrderIso.limsup_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem OrderIso.limsup_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hu_co : f.IsCoboundedUnder (· ≤ ·) u := by
      run_tac
        is_bounded_default)
    (hgu : f.IsBoundedUnder (· ≤ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default)
    (hgu_co : f.IsCoboundedUnder (· ≤ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default) :
    g (limsup u f) = limsup (fun x => g (u x)) f :=
  by
  refine' le_antisymm (g.to_galois_connection.l_limsup_le hgu hu_co) _
  rw [← g.symm.symm_apply_apply <| limsup (fun x => g (u x)) f, g.symm_symm]
  refine' g.monotone _
  have hf : u = fun i => g.symm (g (u i)) := funext fun i => (g.symm_apply_apply (u i)).symm
  nth_rw 1 [hf]
  refine' g.symm.to_galois_connection.l_limsup_le _ hgu_co
  simp_rw [g.symm_apply_apply]
  exact hu
#align order_iso.limsup_apply OrderIso.limsup_apply

/- warning: order_iso.liminf_apply -> OrderIso.liminf_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align order_iso.liminf_apply OrderIso.liminf_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic is_bounded_default -/
theorem OrderIso.liminf_apply {γ} [ConditionallyCompleteLattice β] [ConditionallyCompleteLattice γ]
    {f : Filter α} {u : α → β} (g : β ≃o γ)
    (hu : f.IsBoundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hu_co : f.IsCoboundedUnder (· ≥ ·) u := by
      run_tac
        is_bounded_default)
    (hgu : f.IsBoundedUnder (· ≥ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default)
    (hgu_co : f.IsCoboundedUnder (· ≥ ·) fun x => g (u x) := by
      run_tac
        is_bounded_default) :
    g (liminf u f) = liminf (fun x => g (u x)) f :=
  @OrderIso.limsup_apply α βᵒᵈ γᵒᵈ _ _ f u g.dual hu hu_co hgu hgu_co
#align order_iso.liminf_apply OrderIso.liminf_apply

end Order

