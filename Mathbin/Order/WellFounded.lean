/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module order.well_founded
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.ByContra
import Mathbin.Data.Set.Image

/-!
# Well-founded relations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α , β x`.

The predicate `well_founded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `well_founded.min`, `well_founded.sup`, and `well_founded.succ`,
and an induction principle `well_founded.induction_bot`.
-/


variable {α : Type _}

namespace WellFounded

#print WellFounded.isAsymm /-
protected theorem isAsymm {α : Sort _} {r : α → α → Prop} (h : WellFounded r) : IsAsymm α r :=
  ⟨h.asymmetric⟩
#align well_founded.is_asymm WellFounded.isAsymm
-/

instance {α : Sort _} [WellFoundedRelation α] : IsAsymm α WellFoundedRelation.R :=
  WellFoundedRelation.wf.IsAsymm

#print WellFounded.isIrrefl /-
protected theorem isIrrefl {α : Sort _} {r : α → α → Prop} (h : WellFounded r) : IsIrrefl α r :=
  @IsAsymm.isIrrefl α r h.IsAsymm
#align well_founded.is_irrefl WellFounded.isIrrefl
-/

instance {α : Sort _} [WellFoundedRelation α] : IsIrrefl α WellFoundedRelation.R :=
  IsAsymm.isIrrefl

/- warning: well_founded.has_min -> WellFounded.has_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, (WellFounded.{succ u1} α r) -> (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Not (r x a))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, (WellFounded.{succ u1} α r) -> (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Not (r x a))))))
Case conversion may be inaccurate. Consider using '#align well_founded.has_min WellFounded.has_minₓ'. -/
/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : WellFounded r) (s : Set α) :
    s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
  | ⟨a, ha⟩ =>
    (Acc.recOn (H.apply a) fun x _ IH =>
        not_imp_not.1 fun hne hx => hne <| ⟨x, hx, fun y hy hyx => hne <| IH y hyx hy⟩)
      ha
#align well_founded.has_min WellFounded.has_min

#print WellFounded.min /-
/-- A minimal element of a nonempty set in a well-founded order.

If you're working with a nonempty linear order, consider defining a
`conditionally_complete_linear_order_bot` instance via
`well_founded.conditionally_complete_linear_order_with_bot` and using `Inf` instead. -/
noncomputable def min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) : α :=
  Classical.choose (H.has_min s h)
#align well_founded.min WellFounded.min
-/

#print WellFounded.min_mem /-
theorem min_mem {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) :
    H.min s h ∈ s :=
  let ⟨h, _⟩ := Classical.choose_spec (H.has_min s h)
  h
#align well_founded.min_mem WellFounded.min_mem
-/

#print WellFounded.not_lt_min /-
theorem not_lt_min {r : α → α → Prop} (H : WellFounded r) (s : Set α) (h : s.Nonempty) {x}
    (hx : x ∈ s) : ¬r x (H.min s h) :=
  let ⟨_, h'⟩ := Classical.choose_spec (H.has_min s h)
  h' _ hx
#align well_founded.not_lt_min WellFounded.not_lt_min
-/

/- warning: well_founded.well_founded_iff_has_min -> WellFounded.wellFounded_iff_has_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (WellFounded.{succ u1} α r) (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m s) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Not (r x m))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Iff (WellFounded.{succ u1} α r) (forall (s : Set.{u1} α), (Set.Nonempty.{u1} α s) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m s) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Not (r x m))))))
Case conversion may be inaccurate. Consider using '#align well_founded.well_founded_iff_has_min WellFounded.wellFounded_iff_has_minₓ'. -/
theorem wellFounded_iff_has_min {r : α → α → Prop} :
    WellFounded r ↔ ∀ s : Set α, s.Nonempty → ∃ m ∈ s, ∀ x ∈ s, ¬r x m :=
  by
  refine' ⟨fun h => h.has_min, fun h => ⟨fun x => _⟩⟩
  by_contra hx
  obtain ⟨m, hm, hm'⟩ := h _ ⟨x, hx⟩
  refine' hm ⟨_, fun y hy => _⟩
  by_contra hy'
  exact hm' y hy' hy
#align well_founded.well_founded_iff_has_min WellFounded.wellFounded_iff_has_min

#print WellFounded.eq_iff_not_lt_of_le /-
theorem eq_iff_not_lt_of_le {α} [PartialOrder α] {x y : α} : x ≤ y → y = x ↔ ¬x < y :=
  by
  constructor
  · intro xle nge
    cases le_not_le_of_lt nge
    rw [xle left] at nge
    exact lt_irrefl x nge
  · intro ngt xle
    contrapose! ngt
    exact lt_of_le_of_ne xle (Ne.symm ngt)
#align well_founded.eq_iff_not_lt_of_le WellFounded.eq_iff_not_lt_of_le
-/

/- warning: well_founded.well_founded_iff_has_max' -> WellFounded.wellFounded_iff_has_max' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Iff (WellFounded.{succ u1} α (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (forall (p : Set.{u1} α), (Set.Nonempty.{u1} α p) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m p) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m p) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x p) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m x) -> (Eq.{succ u1} α x m)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Iff (WellFounded.{succ u1} α (fun (x._@.Mathlib.Order.WellFounded._hyg.641 : α) (x._@.Mathlib.Order.WellFounded._hyg.643 : α) => GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Order.WellFounded._hyg.641 x._@.Mathlib.Order.WellFounded._hyg.643)) (forall (p : Set.{u1} α), (Set.Nonempty.{u1} α p) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m p) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x p) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) m x) -> (Eq.{succ u1} α x m)))))
Case conversion may be inaccurate. Consider using '#align well_founded.well_founded_iff_has_max' WellFounded.wellFounded_iff_has_max'ₓ'. -/
theorem wellFounded_iff_has_max' [PartialOrder α] :
    WellFounded ((· > ·) : α → α → Prop) ↔
      ∀ p : Set α, p.Nonempty → ∃ m ∈ p, ∀ x ∈ p, m ≤ x → x = m :=
  by simp only [eq_iff_not_lt_of_le, well_founded_iff_has_min]
#align well_founded.well_founded_iff_has_max' WellFounded.wellFounded_iff_has_max'

/- warning: well_founded.well_founded_iff_has_min' -> WellFounded.wellFounded_iff_has_min' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Iff (WellFounded.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (forall (p : Set.{u1} α), (Set.Nonempty.{u1} α p) -> (Exists.{succ u1} α (fun (m : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m p) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) m p) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x p) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x m) -> (Eq.{succ u1} α x m)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Iff (WellFounded.{succ u1} α (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (forall (p : Set.{u1} α), (Set.Nonempty.{u1} α p) -> (Exists.{succ u1} α (fun (m : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) m p) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x p) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x m) -> (Eq.{succ u1} α x m)))))
Case conversion may be inaccurate. Consider using '#align well_founded.well_founded_iff_has_min' WellFounded.wellFounded_iff_has_min'ₓ'. -/
theorem wellFounded_iff_has_min' [PartialOrder α] :
    WellFounded (LT.lt : α → α → Prop) ↔
      ∀ p : Set α, p.Nonempty → ∃ m ∈ p, ∀ x ∈ p, x ≤ m → x = m :=
  @wellFounded_iff_has_max' αᵒᵈ _
#align well_founded.well_founded_iff_has_min' WellFounded.wellFounded_iff_has_min'

open Set

#print WellFounded.sup /-
/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {r : α → α → Prop} (wf : WellFounded r) (s : Set α)
    (h : Bounded r s) : α :=
  wf.min { x | ∀ a ∈ s, r a x } h
#align well_founded.sup WellFounded.sup
-/

#print WellFounded.lt_sup /-
protected theorem lt_sup {r : α → α → Prop} (wf : WellFounded r) {s : Set α} (h : Bounded r s) {x}
    (hx : x ∈ s) : r x (wf.sup s h) :=
  min_mem wf { x | ∀ a ∈ s, r a x } h x hx
#align well_founded.lt_sup WellFounded.lt_sup
-/

section

open Classical

#print WellFounded.succ /-
/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {r : α → α → Prop} (wf : WellFounded r) (x : α) : α :=
  if h : ∃ y, r x y then wf.min { y | r x y } h else x
#align well_founded.succ WellFounded.succ
-/

#print WellFounded.lt_succ /-
protected theorem lt_succ {r : α → α → Prop} (wf : WellFounded r) {x : α} (h : ∃ y, r x y) :
    r x (wf.succ x) := by
  rw [WellFounded.succ, dif_pos h]
  apply min_mem
#align well_founded.lt_succ WellFounded.lt_succ
-/

end

#print WellFounded.lt_succ_iff /-
protected theorem lt_succ_iff {r : α → α → Prop} [wo : IsWellOrder α r] {x : α} (h : ∃ y, r x y)
    (y : α) : r y (wo.wf.succ x) ↔ r y x ∨ y = x :=
  by
  constructor
  · intro h'
    have : ¬r x y := by
      intro hy
      rw [WellFounded.succ, dif_pos] at h'
      exact wo.wf.not_lt_min _ h hy h'
    rcases trichotomous_of r x y with (hy | hy | hy)
    exfalso
    exact this hy
    right
    exact hy.symm
    left
    exact hy
  rintro (hy | rfl); exact trans hy (wo.wf.lt_succ h); exact wo.wf.lt_succ h
#align well_founded.lt_succ_iff WellFounded.lt_succ_iff
-/

section LinearOrder

variable {β : Type _} [LinearOrder β] (h : WellFounded ((· < ·) : β → β → Prop)) {γ : Type _}
  [PartialOrder γ]

#print WellFounded.min_le /-
theorem min_le {x : β} {s : Set β} (hx : x ∈ s) (hne : s.Nonempty := ⟨x, hx⟩) : h.min s hne ≤ x :=
  not_lt.1 <| h.not_lt_min _ _ hx
#align well_founded.min_le WellFounded.min_le
-/

private theorem eq_strict_mono_iff_eq_range_aux {f g : β → γ} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : Set.range f = Set.range g) {b : β} (H : ∀ a < b, f a = g a) :
    f b ≤ g b :=
  by
  obtain ⟨c, hc⟩ : g b ∈ Set.range f := by
    rw [hfg]
    exact Set.mem_range_self b
  cases' lt_or_le c b with hcb hbc
  · rw [H c hcb] at hc
    rw [hg.injective hc] at hcb
    exact hcb.false.elim
  · rw [← hc]
    exact hf.monotone hbc
#align well_founded.eq_strict_mono_iff_eq_range_aux well_founded.eq_strict_mono_iff_eq_range_aux

include h

/- warning: well_founded.eq_strict_mono_iff_eq_range -> WellFounded.eq_strictMono_iff_eq_range is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β], (WellFounded.{succ u1} β (LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (LinearOrder.toLattice.{u1} β _inst_1))))))) -> (forall {γ : Type.{u2}} [_inst_2 : PartialOrder.{u2} γ] {f : β -> γ} {g : β -> γ}, (StrictMono.{u1, u2} β γ (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (LinearOrder.toLattice.{u1} β _inst_1)))) (PartialOrder.toPreorder.{u2} γ _inst_2) f) -> (StrictMono.{u1, u2} β γ (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (LinearOrder.toLattice.{u1} β _inst_1)))) (PartialOrder.toPreorder.{u2} γ _inst_2) g) -> (Iff (Eq.{succ u2} (Set.{u2} γ) (Set.range.{u2, succ u1} γ β f) (Set.range.{u2, succ u1} γ β g)) (Eq.{max (succ u1) (succ u2)} (β -> γ) f g)))
but is expected to have type
  forall {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β], (WellFounded.{succ u2} β (fun (x._@.Mathlib.Order.WellFounded._hyg.1491 : β) (x._@.Mathlib.Order.WellFounded._hyg.1493 : β) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) x._@.Mathlib.Order.WellFounded._hyg.1491 x._@.Mathlib.Order.WellFounded._hyg.1493)) -> (forall {γ : Type.{u1}} [_inst_2 : PartialOrder.{u1} γ] {f : β -> γ} {g : β -> γ}, (StrictMono.{u2, u1} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1))))) (PartialOrder.toPreorder.{u1} γ _inst_2) f) -> (StrictMono.{u2, u1} β γ (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1))))) (PartialOrder.toPreorder.{u1} γ _inst_2) g) -> (Iff (Eq.{succ u1} (Set.{u1} γ) (Set.range.{u1, succ u2} γ β f) (Set.range.{u1, succ u2} γ β g)) (Eq.{max (succ u2) (succ u1)} (β -> γ) f g)))
Case conversion may be inaccurate. Consider using '#align well_founded.eq_strict_mono_iff_eq_range WellFounded.eq_strictMono_iff_eq_rangeₓ'. -/
theorem eq_strictMono_iff_eq_range {f g : β → γ} (hf : StrictMono f) (hg : StrictMono g) :
    Set.range f = Set.range g ↔ f = g :=
  ⟨fun hfg => by
    funext a
    apply h.induction a
    exact fun b H =>
      le_antisymm (eq_strict_mono_iff_eq_range_aux hf hg hfg H)
        (eq_strict_mono_iff_eq_range_aux hg hf hfg.symm fun a hab => (H a hab).symm),
    congr_arg _⟩
#align well_founded.eq_strict_mono_iff_eq_range WellFounded.eq_strictMono_iff_eq_range

#print WellFounded.self_le_of_strictMono /-
theorem self_le_of_strictMono {f : β → β} (hf : StrictMono f) : ∀ n, n ≤ f n :=
  by
  by_contra' h₁
  have h₂ := h.min_mem _ h₁
  exact h.not_lt_min _ h₁ (hf h₂) h₂
#align well_founded.self_le_of_strict_mono WellFounded.self_le_of_strictMono
-/

end LinearOrder

end WellFounded

namespace Function

variable {β : Type _} (f : α → β)

section LT

variable [LT β] (h : WellFounded ((· < ·) : β → β → Prop))

#print Function.argmin /-
/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `function.not_lt_argmin`. -/
noncomputable def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f h) Set.univ Set.univ_nonempty
#align function.argmin Function.argmin
-/

/- warning: function.not_lt_argmin -> Function.not_lt_argmin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) [_inst_1 : LT.{u2} β] (h : WellFounded.{succ u2} β (LT.lt.{u2} β _inst_1)) [_inst_2 : Nonempty.{succ u1} α] (a : α), Not (LT.lt.{u2} β _inst_1 (f a) (f (Function.argmin.{u1, u2} α β f _inst_1 h _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) [_inst_1 : LT.{u1} β] (h : WellFounded.{succ u1} β (fun (x._@.Mathlib.Order.WellFounded._hyg.1797 : β) (x._@.Mathlib.Order.WellFounded._hyg.1799 : β) => LT.lt.{u1} β _inst_1 x._@.Mathlib.Order.WellFounded._hyg.1797 x._@.Mathlib.Order.WellFounded._hyg.1799)) [_inst_2 : Nonempty.{succ u2} α] (a : α), Not (LT.lt.{u1} β _inst_1 (f a) (f (Function.argmin.{u2, u1} α β f _inst_1 h _inst_2)))
Case conversion may be inaccurate. Consider using '#align function.not_lt_argmin Function.not_lt_argminₓ'. -/
theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f h) :=
  WellFounded.not_lt_min (InvImage.wf f h) _ _ (Set.mem_univ a)
#align function.not_lt_argmin Function.not_lt_argmin

#print Function.argminOn /-
/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`function.not_lt_argmin_on`. -/
noncomputable def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f h) s hs
#align function.argmin_on Function.argminOn
-/

/- warning: function.argmin_on_mem -> Function.argminOn_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) [_inst_1 : LT.{u2} β] (h : WellFounded.{succ u2} β (LT.lt.{u2} β _inst_1)) (s : Set.{u1} α) (hs : Set.Nonempty.{u1} α s), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Function.argminOn.{u1, u2} α β f _inst_1 h s hs) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) [_inst_1 : LT.{u1} β] (h : WellFounded.{succ u1} β (fun (x._@.Mathlib.Order.WellFounded._hyg.1905 : β) (x._@.Mathlib.Order.WellFounded._hyg.1907 : β) => LT.lt.{u1} β _inst_1 x._@.Mathlib.Order.WellFounded._hyg.1905 x._@.Mathlib.Order.WellFounded._hyg.1907)) (s : Set.{u2} α) (hs : Set.Nonempty.{u2} α s), Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Function.argminOn.{u2, u1} α β f _inst_1 h s hs) s
Case conversion may be inaccurate. Consider using '#align function.argmin_on_mem Function.argminOn_memₓ'. -/
@[simp]
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f h s hs ∈ s :=
  WellFounded.min_mem _ _ _
#align function.argmin_on_mem Function.argminOn_mem

/- warning: function.not_lt_argmin_on -> Function.not_lt_argminOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) [_inst_1 : LT.{u2} β] (h : WellFounded.{succ u2} β (LT.lt.{u2} β _inst_1)) (s : Set.{u1} α) {a : α} (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (hs : optParam.{0} (Set.Nonempty.{u1} α s) (Set.nonempty_of_mem.{u1} α s a ha)), Not (LT.lt.{u2} β _inst_1 (f a) (f (Function.argminOn.{u1, u2} α β f _inst_1 h s hs)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) [_inst_1 : LT.{u1} β] (h : WellFounded.{succ u1} β (fun (x._@.Mathlib.Order.WellFounded._hyg.1954 : β) (x._@.Mathlib.Order.WellFounded._hyg.1956 : β) => LT.lt.{u1} β _inst_1 x._@.Mathlib.Order.WellFounded._hyg.1954 x._@.Mathlib.Order.WellFounded._hyg.1956)) (s : Set.{u2} α) {a : α} (ha : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (hs : optParam.{0} (Set.Nonempty.{u2} α s) (Set.nonempty_of_mem.{u2} α s a ha)), Not (LT.lt.{u1} β _inst_1 (f a) (f (Function.argminOn.{u2, u1} α β f _inst_1 h s hs)))
Case conversion may be inaccurate. Consider using '#align function.not_lt_argmin_on Function.not_lt_argminOnₓ'. -/
@[simp]
theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s)
    (hs : s.Nonempty := Set.nonempty_of_mem ha) : ¬f a < f (argminOn f h s hs) :=
  WellFounded.not_lt_min (InvImage.wf f h) s hs ha
#align function.not_lt_argmin_on Function.not_lt_argminOn

end LT

section LinearOrder

variable [LinearOrder β] (h : WellFounded ((· < ·) : β → β → Prop))

/- warning: function.argmin_le -> Function.argmin_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) [_inst_1 : LinearOrder.{u2} β] (h : WellFounded.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))))) (a : α) [_inst_2 : Nonempty.{succ u1} α], LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f (Function.argmin.{u1, u2} α β f (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) h _inst_2)) (f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) [_inst_1 : LinearOrder.{u1} β] (h : WellFounded.{succ u1} β (fun (x._@.Mathlib.Order.WellFounded._hyg.2060 : β) (x._@.Mathlib.Order.WellFounded._hyg.2062 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) x._@.Mathlib.Order.WellFounded._hyg.2060 x._@.Mathlib.Order.WellFounded._hyg.2062)) (a : α) [_inst_2 : Nonempty.{succ u2} α], LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f (Function.argmin.{u2, u1} α β f (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) h _inst_2)) (f a)
Case conversion may be inaccurate. Consider using '#align function.argmin_le Function.argmin_leₓ'. -/
@[simp]
theorem argmin_le (a : α) [Nonempty α] : f (argmin f h) ≤ f a :=
  not_lt.mp <| not_lt_argmin f h a
#align function.argmin_le Function.argmin_le

/- warning: function.argmin_on_le -> Function.argminOn_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) [_inst_1 : LinearOrder.{u2} β] (h : WellFounded.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))))) (s : Set.{u1} α) {a : α} (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (hs : optParam.{0} (Set.Nonempty.{u1} α s) (Set.nonempty_of_mem.{u1} α s a ha)), LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f (Function.argminOn.{u1, u2} α β f (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) h s hs)) (f a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β) [_inst_1 : LinearOrder.{u1} β] (h : WellFounded.{succ u1} β (fun (x._@.Mathlib.Order.WellFounded._hyg.2115 : β) (x._@.Mathlib.Order.WellFounded._hyg.2117 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) x._@.Mathlib.Order.WellFounded._hyg.2115 x._@.Mathlib.Order.WellFounded._hyg.2117)) (s : Set.{u2} α) {a : α} (ha : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (hs : optParam.{0} (Set.Nonempty.{u2} α s) (Set.nonempty_of_mem.{u2} α s a ha)), LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f (Function.argminOn.{u2, u1} α β f (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) h s hs)) (f a)
Case conversion may be inaccurate. Consider using '#align function.argmin_on_le Function.argminOn_leₓ'. -/
@[simp]
theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    f (argminOn f h s hs) ≤ f a :=
  not_lt.mp <| not_lt_argminOn f h s ha hs
#align function.argmin_on_le Function.argminOn_le

end LinearOrder

end Function

section Induction

/- warning: acc.induction_bot' -> Acc.induction_bot' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {r : α -> α -> Prop} {a : α} {bot : α}, (Acc.{u1} α r a) -> (forall {C : β -> Prop} {f : α -> β}, (forall (b : α), (Ne.{u2} β (f b) (f bot)) -> (C (f b)) -> (Exists.{u1} α (fun (c : α) => And (r c b) (C (f c))))) -> (C (f a)) -> (C (f bot)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {r : α -> α -> Prop} {a : α} {bot : α}, (Acc.{u2} α r a) -> (forall {C : β -> Prop} {f : α -> β}, (forall (b : α), (Ne.{u1} β (f b) (f bot)) -> (C (f b)) -> (Exists.{u2} α (fun (c : α) => And (r c b) (C (f c))))) -> (C (f a)) -> (C (f bot)))
Case conversion may be inaccurate. Consider using '#align acc.induction_bot' Acc.induction_bot'ₓ'. -/
/-- Let `r` be a relation on `α`, let `f : α → β` be a function, let `C : β → Prop`, and
let `bot : α`. This induction principle shows that `C (f bot)` holds, given that
* some `a` that is accessible by `r` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
theorem Acc.induction_bot' {α β} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : β → Prop}
    {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) : C (f a) → C (f bot) :=
  @Acc.recOn _ _ (fun x => C (f x) → C (f bot)) _ ha fun x ac ih' hC =>
    (eq_or_ne (f x) (f bot)).elim (fun h => h ▸ hC) fun h =>
      let ⟨y, hy₁, hy₂⟩ := ih x h hC
      ih' y hy₁ hy₂
#align acc.induction_bot' Acc.induction_bot'

#print Acc.induction_bot /-
/-- Let `r` be a relation on `α`, let `C : α → Prop` and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` that is accessible by `r` satisfies `C a`, and
* for each `b ≠ bot` such that `C b` holds, there is `c` satisfying `r c b` and `C c`. -/
theorem Acc.induction_bot {α} {r : α → α → Prop} {a bot : α} (ha : Acc r a) {C : α → Prop}
    (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  ha.induction_bot' ih
#align acc.induction_bot Acc.induction_bot
-/

/- warning: well_founded.induction_bot' -> WellFounded.induction_bot' is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {β : Sort.{u2}} {r : α -> α -> Prop}, (WellFounded.{u1} α r) -> (forall {a : α} {bot : α} {C : β -> Prop} {f : α -> β}, (forall (b : α), (Ne.{u2} β (f b) (f bot)) -> (C (f b)) -> (Exists.{u1} α (fun (c : α) => And (r c b) (C (f c))))) -> (C (f a)) -> (C (f bot)))
but is expected to have type
  forall {α : Sort.{u2}} {β : Sort.{u1}} {r : α -> α -> Prop}, (WellFounded.{u2} α r) -> (forall {a : α} {bot : α} {C : β -> Prop} {f : α -> β}, (forall (b : α), (Ne.{u1} β (f b) (f bot)) -> (C (f b)) -> (Exists.{u2} α (fun (c : α) => And (r c b) (C (f c))))) -> (C (f a)) -> (C (f bot)))
Case conversion may be inaccurate. Consider using '#align well_founded.induction_bot' WellFounded.induction_bot'ₓ'. -/
/-- Let `r` be a well-founded relation on `α`, let `f : α → β` be a function,
let `C : β → Prop`, and  let `bot : α`.
This induction principle shows that `C (f bot)` holds, given that
* some `a` satisfies `C (f a)`, and
* for each `b` such that `f b ≠ f bot` and `C (f b)` holds, there is `c`
  satisfying `r c b` and `C (f c)`. -/
theorem WellFounded.induction_bot' {α β} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : β → Prop} {f : α → β} (ih : ∀ b, f b ≠ f bot → C (f b) → ∃ c, r c b ∧ C (f c)) :
    C (f a) → C (f bot) :=
  (hwf.apply a).induction_bot' ih
#align well_founded.induction_bot' WellFounded.induction_bot'

#print WellFounded.induction_bot /-
/-- Let `r` be a well-founded relation on `α`, let `C : α → Prop`, and let `bot : α`.
This induction principle shows that `C bot` holds, given that
* some `a` satisfies `C a`, and
* for each `b` that satisfies `C b`, there is `c` satisfying `r c b` and `C c`.

The naming is inspired by the fact that when `r` is transitive, it follows that `bot` is
the smallest element w.r.t. `r` that satisfies `C`. -/
theorem WellFounded.induction_bot {α} {r : α → α → Prop} (hwf : WellFounded r) {a bot : α}
    {C : α → Prop} (ih : ∀ b, b ≠ bot → C b → ∃ c, r c b ∧ C c) : C a → C bot :=
  hwf.induction_bot' ih
#align well_founded.induction_bot WellFounded.induction_bot
-/

end Induction

