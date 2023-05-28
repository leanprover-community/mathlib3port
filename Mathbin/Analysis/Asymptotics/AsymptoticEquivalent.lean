/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.asymptotics.asymptotic_equivalent
! leanprover-community/mathlib commit ce38d86c0b2d427ce208c3cee3159cb421d2b3c4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Analysis.Normed.Order.Basic

/-!
# Asymptotic equivalence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define the relation `is_equivalent l u v`, which means that `u-v` is little o of
`v` along the filter `l`.

Unlike `is_[oO]` relations, this one requires `u` and `v` to have the same codomain `β`. While the
definition only requires `β` to be a `normed_add_comm_group`, most interesting properties require it
to be a `normed_field`.

## Notations

We introduce the notation `u ~[l] v := is_equivalent l u v`, which you can use by opening the
`asymptotics` locale.

## Main results

If `β` is a `normed_add_comm_group` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `tendsto u l (𝓝 c)` (see `is_equivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `is_equivalent_zero_iff_eventually_zero`)

If `β` is a `normed_field` :

- Alternative characterization of the relation (see `is_equivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ tendsto (u/v) l (𝓝 1)`
  (see `is_equivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c)`
  (see `is_equivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `is_equivalent.mul` and `is_equivalent.div`)

If `β` is a `normed_linear_ordered_field` :

- If `u ~[l] v`, we have `tendsto u l at_top ↔ tendsto v l at_top`
  (see `is_equivalent.tendsto_at_top_iff`)

## Implementation Notes

Note that `is_equivalent` takes the parameters `(l : filter α) (u v : α → β)` in that order.
This is to enable `calc` support, as `calc` requires that the last two explicit arguments are `u v`.

-/


namespace Asymptotics

open Filter Function

open Topology

section NormedAddCommGroup

variable {α β : Type _} [NormedAddCommGroup β]

#print Asymptotics.IsEquivalent /-
/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as x converges along `l`. -/
def IsEquivalent (l : Filter α) (u v : α → β) :=
  (u - v) =o[l] v
#align asymptotics.is_equivalent Asymptotics.IsEquivalent
-/

-- mathport name: asymptotics.is_equivalent
scoped notation:50 u " ~[" l:50 "] " v:50 => Asymptotics.IsEquivalent l u v

variable {u v w : α → β} {l : Filter α}

/- warning: asymptotics.is_equivalent.is_o -> Asymptotics.IsEquivalent.isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsLittleO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))) u v) v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsLittleO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHSub.{max u2 u1} (α -> β) (Pi.instSub.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u1} β (AddGroup.toSubNegMonoid.{u1} β (NormedAddGroup.toAddGroup.{u1} β (NormedAddCommGroup.toNormedAddGroup.{u1} β _inst_1)))))) u v) v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.is_o Asymptotics.IsEquivalent.isLittleOₓ'. -/
theorem IsEquivalent.isLittleO (h : u ~[l] v) : (u - v) =o[l] v :=
  h
#align asymptotics.is_equivalent.is_o Asymptotics.IsEquivalent.isLittleO

/- warning: asymptotics.is_equivalent.is_O -> Asymptotics.IsEquivalent.isBigO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsBigO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l u v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsBigO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.is_O Asymptotics.IsEquivalent.isBigOₓ'. -/
theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.IsBigO.symm).mp (isBigO_refl _ _)
#align asymptotics.is_equivalent.is_O Asymptotics.IsEquivalent.isBigO

/- warning: asymptotics.is_equivalent.is_O_symm -> Asymptotics.IsEquivalent.isBigO_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsBigO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l v u)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsBigO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l v u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.is_O_symm Asymptotics.IsEquivalent.isBigO_symmₓ'. -/
theorem IsEquivalent.isBigO_symm (h : u ~[l] v) : v =O[l] u :=
  by
  convert h.is_o.right_is_O_add
  ext
  simp
#align asymptotics.is_equivalent.is_O_symm Asymptotics.IsEquivalent.isBigO_symm

/- warning: asymptotics.is_equivalent.refl -> Asymptotics.IsEquivalent.refl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {l : Filter.{u1} α}, Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u u
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {l : Filter.{u2} α}, Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u u
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.refl Asymptotics.IsEquivalent.reflₓ'. -/
@[refl]
theorem IsEquivalent.refl : u ~[l] u :=
  by
  rw [is_equivalent, sub_self]
  exact is_o_zero _ _
#align asymptotics.is_equivalent.refl Asymptotics.IsEquivalent.refl

/- warning: asymptotics.is_equivalent.symm -> Asymptotics.IsEquivalent.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l v u)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l v u)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.symm Asymptotics.IsEquivalent.symmₓ'. -/
@[symm]
theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.IsLittleO.trans_isBigO h.isBigO_symm).symm
#align asymptotics.is_equivalent.symm Asymptotics.IsEquivalent.symm

/- warning: asymptotics.is_equivalent.trans -> Asymptotics.IsEquivalent.trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {u : α -> β} {v : α -> β} {w : α -> β}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l v w) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u w)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {l : Filter.{u2} α} {u : α -> β} {v : α -> β} {w : α -> β}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l v w) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u w)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.trans Asymptotics.IsEquivalent.transₓ'. -/
@[trans]
theorem IsEquivalent.trans {l : Filter α} {u v w : α → β} (huv : u ~[l] v) (hvw : v ~[l] w) :
    u ~[l] w :=
  (huv.IsLittleO.trans_isBigO hvw.IsBigO).triangle hvw.IsLittleO
#align asymptotics.is_equivalent.trans Asymptotics.IsEquivalent.trans

/- warning: asymptotics.is_equivalent.congr_left -> Asymptotics.IsEquivalent.congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Filter.EventuallyEq.{u1, u2} α β l u w) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l w v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Filter.EventuallyEq.{u2, u1} α β l u w) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l w v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.congr_left Asymptotics.IsEquivalent.congr_leftₓ'. -/
theorem IsEquivalent.congr_left {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) :
    w ~[l] v :=
  huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)
#align asymptotics.is_equivalent.congr_left Asymptotics.IsEquivalent.congr_left

/- warning: asymptotics.is_equivalent.congr_right -> Asymptotics.IsEquivalent.congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Filter.EventuallyEq.{u1, u2} α β l v w) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u w)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Filter.EventuallyEq.{u2, u1} α β l v w) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u w)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.congr_right Asymptotics.IsEquivalent.congr_rightₓ'. -/
theorem IsEquivalent.congr_right {u v w : α → β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) :
    u ~[l] w :=
  (huv.symm.congr_left hvw).symm
#align asymptotics.is_equivalent.congr_right Asymptotics.IsEquivalent.congr_right

/- warning: asymptotics.is_equivalent_zero_iff_eventually_zero -> Asymptotics.isEquivalent_zero_iff_eventually_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {l : Filter.{u1} α}, Iff (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1))))))))))) (Filter.EventuallyEq.{u1, u2} α β l u (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {l : Filter.{u2} α}, Iff (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.Analysis.Asymptotics.AsymptoticEquivalent._hyg.27 : α) => β) (fun (i : α) => NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β (NormedAddCommGroup.toAddCommGroup.{u1} β _inst_1)))))))))) (Filter.EventuallyEq.{u2, u1} α β l u (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.Analysis.Asymptotics.AsymptoticEquivalent._hyg.27 : α) => β) (fun (i : α) => NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β (NormedAddCommGroup.toAddCommGroup.{u1} β _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_zero_iff_eventually_zero Asymptotics.isEquivalent_zero_iff_eventually_zeroₓ'. -/
theorem isEquivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 :=
  by
  rw [is_equivalent, sub_zero]
  exact is_o_zero_right_iff
#align asymptotics.is_equivalent_zero_iff_eventually_zero Asymptotics.isEquivalent_zero_iff_eventually_zero

/- warning: asymptotics.is_equivalent_zero_iff_is_O_zero -> Asymptotics.isEquivalent_zero_iff_isBigO_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {l : Filter.{u1} α}, Iff (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1))))))))))) (Asymptotics.IsBigO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l u (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {l : Filter.{u2} α}, Iff (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.Analysis.Asymptotics.AsymptoticEquivalent._hyg.27 : α) => β) (fun (i : α) => NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β (NormedAddCommGroup.toAddCommGroup.{u1} β _inst_1)))))))))) (Asymptotics.IsBigO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l u (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.Analysis.Asymptotics.AsymptoticEquivalent._hyg.27 : α) => β) (fun (i : α) => NegZeroClass.toZero.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β (NormedAddCommGroup.toAddCommGroup.{u1} β _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_zero_iff_is_O_zero Asymptotics.isEquivalent_zero_iff_isBigO_zeroₓ'. -/
theorem isEquivalent_zero_iff_isBigO_zero : u ~[l] 0 ↔ u =O[l] (0 : α → β) :=
  by
  refine' ⟨is_equivalent.is_O, fun h => _⟩
  rw [is_equivalent_zero_iff_eventually_zero, eventually_eq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, is_O_zero_right_iff.mp h, fun x hx => hx⟩
#align asymptotics.is_equivalent_zero_iff_is_O_zero Asymptotics.isEquivalent_zero_iff_isBigO_zero

/- warning: asymptotics.is_equivalent_const_iff_tendsto -> Asymptotics.isEquivalent_const_iff_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {l : Filter.{u1} α} {c : β}, (Ne.{succ u2} β c (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))))) -> (Iff (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u (Function.const.{succ u2, succ u1} β α c)) (Filter.Tendsto.{u1, u2} α β u l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {l : Filter.{u1} α} {c : β}, (Ne.{succ u2} β c (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_1))))))))) -> (Iff (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u (Function.const.{succ u2, succ u1} β α c)) (Filter.Tendsto.{u1, u2} α β u l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_const_iff_tendsto Asymptotics.isEquivalent_const_iff_tendstoₓ'. -/
theorem isEquivalent_const_iff_tendsto {c : β} (h : c ≠ 0) : u ~[l] const _ c ↔ Tendsto u l (𝓝 c) :=
  by
  rw [is_equivalent, is_o_const_iff h]
  constructor <;> intro h <;>
          [· have := h.sub tendsto_const_nhds;
            rw [zero_sub (-c)] at this;· have := h.sub tendsto_const_nhds; rw [← sub_self c]] <;>
        convert this <;>
      try ext <;>
    simp
#align asymptotics.is_equivalent_const_iff_tendsto Asymptotics.isEquivalent_const_iff_tendsto

/- warning: asymptotics.is_equivalent.tendsto_const -> Asymptotics.IsEquivalent.tendsto_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {l : Filter.{u1} α} {c : β}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u (Function.const.{succ u2, succ u1} β α c)) -> (Filter.Tendsto.{u1, u2} α β u l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {l : Filter.{u2} α} {c : β}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u (Function.const.{succ u1, succ u2} β α c)) -> (Filter.Tendsto.{u2, u1} α β u l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} β _inst_1)))) c))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.tendsto_const Asymptotics.IsEquivalent.tendsto_constₓ'. -/
theorem IsEquivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : Tendsto u l (𝓝 c) :=
  by
  rcases em <| c = 0 with ⟨rfl, h⟩
  · exact (tendsto_congr' <| is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (is_equivalent_const_iff_tendsto h).mp hu
#align asymptotics.is_equivalent.tendsto_const Asymptotics.IsEquivalent.tendsto_const

/- warning: asymptotics.is_equivalent.tendsto_nhds -> Asymptotics.IsEquivalent.tendsto_nhds is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α} {c : β}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Filter.Tendsto.{u1, u2} α β u l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c)) -> (Filter.Tendsto.{u1, u2} α β v l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α} {c : β}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Filter.Tendsto.{u2, u1} α β u l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} β _inst_1)))) c)) -> (Filter.Tendsto.{u2, u1} α β v l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} β _inst_1)))) c))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.tendsto_nhds Asymptotics.IsEquivalent.tendsto_nhdsₓ'. -/
theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) :
    Tendsto v l (𝓝 c) := by
  by_cases h : c = 0
  · subst c; rw [← is_o_one_iff ℝ] at hu⊢
    simpa using (huv.symm.is_o.trans hu).add hu
  · rw [← is_equivalent_const_iff_tendsto h] at hu⊢
    exact huv.symm.trans hu
#align asymptotics.is_equivalent.tendsto_nhds Asymptotics.IsEquivalent.tendsto_nhds

/- warning: asymptotics.is_equivalent.tendsto_nhds_iff -> Asymptotics.IsEquivalent.tendsto_nhds_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α} {c : β}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Iff (Filter.Tendsto.{u1, u2} α β u l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c)) (Filter.Tendsto.{u1, u2} α β v l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α} {c : β}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Iff (Filter.Tendsto.{u2, u1} α β u l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} β _inst_1)))) c)) (Filter.Tendsto.{u2, u1} α β v l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} β _inst_1)))) c)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.tendsto_nhds_iff Asymptotics.IsEquivalent.tendsto_nhds_iffₓ'. -/
theorem IsEquivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) :
    Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩
#align asymptotics.is_equivalent.tendsto_nhds_iff Asymptotics.IsEquivalent.tendsto_nhds_iff

/- warning: asymptotics.is_equivalent.add_is_o -> Asymptotics.IsEquivalent.add_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsLittleO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l w v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))) u w) v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsLittleO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l w v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHAdd.{max u2 u1} (α -> β) (Pi.instAdd.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (SubNegMonoid.toAddMonoid.{u1} β (AddGroup.toSubNegMonoid.{u1} β (NormedAddGroup.toAddGroup.{u1} β (NormedAddCommGroup.toNormedAddGroup.{u1} β _inst_1)))))))) u w) v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.add_is_o Asymptotics.IsEquivalent.add_isLittleOₓ'. -/
theorem IsEquivalent.add_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u + w ~[l] v := by
  simpa only [is_equivalent, add_sub_right_comm] using huv.add hwv
#align asymptotics.is_equivalent.add_is_o Asymptotics.IsEquivalent.add_isLittleO

/- warning: asymptotics.is_equivalent.sub_is_o -> Asymptotics.IsEquivalent.sub_isLittleO is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsLittleO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l w v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))) u w) v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsLittleO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l w v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHSub.{max u2 u1} (α -> β) (Pi.instSub.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u1} β (AddGroup.toSubNegMonoid.{u1} β (NormedAddGroup.toAddGroup.{u1} β (NormedAddCommGroup.toNormedAddGroup.{u1} β _inst_1)))))) u w) v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.sub_is_o Asymptotics.IsEquivalent.sub_isLittleOₓ'. -/
theorem IsEquivalent.sub_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u - w ~[l] v := by
  simpa only [sub_eq_add_neg] using huv.add_is_o hwv.neg_left
#align asymptotics.is_equivalent.sub_is_o Asymptotics.IsEquivalent.sub_isLittleO

/- warning: asymptotics.is_o.add_is_equivalent -> Asymptotics.IsLittleO.add_isEquivalent is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l u w) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l v w) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))) u v) w)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsLittleO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l u w) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l v w) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l (HAdd.hAdd.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHAdd.{max u2 u1} (α -> β) (Pi.instAdd.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toAdd.{u1} β (AddMonoid.toAddZeroClass.{u1} β (SubNegMonoid.toAddMonoid.{u1} β (AddGroup.toSubNegMonoid.{u1} β (NormedAddGroup.toAddGroup.{u1} β (NormedAddCommGroup.toNormedAddGroup.{u1} β _inst_1)))))))) u v) w)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.add_is_equivalent Asymptotics.IsLittleO.add_isEquivalentₓ'. -/
theorem IsLittleO.add_isEquivalent (hu : u =o[l] w) (hv : v ~[l] w) : u + v ~[l] w :=
  add_comm v u ▸ hv.add_isLittleO hu
#align asymptotics.is_o.add_is_equivalent Asymptotics.IsLittleO.add_isEquivalent

/- warning: asymptotics.is_o.is_equivalent -> Asymptotics.IsLittleO.isEquivalent is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsLittleO.{u1, u2, u2} α β β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))) u v) v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsLittleO.{u2, u1, u1} α β β (NormedAddCommGroup.toNorm.{u1} β _inst_1) (NormedAddCommGroup.toNorm.{u1} β _inst_1) l (HSub.hSub.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHSub.{max u2 u1} (α -> β) (Pi.instSub.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u1} β (AddGroup.toSubNegMonoid.{u1} β (NormedAddGroup.toAddGroup.{u1} β (NormedAddCommGroup.toNormedAddGroup.{u1} β _inst_1)))))) u v) v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.is_equivalent Asymptotics.IsLittleO.isEquivalentₓ'. -/
theorem IsLittleO.isEquivalent (huv : (u - v) =o[l] v) : u ~[l] v :=
  huv
#align asymptotics.is_o.is_equivalent Asymptotics.IsLittleO.isEquivalent

/- warning: asymptotics.is_equivalent.neg -> Asymptotics.IsEquivalent.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))) (u x)) (fun (x : α) => Neg.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))) (v x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l (fun (x : α) => Neg.neg.{u1} β (NegZeroClass.toNeg.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β (NormedAddCommGroup.toAddCommGroup.{u1} β _inst_1)))))) (u x)) (fun (x : α) => Neg.neg.{u1} β (NegZeroClass.toNeg.{u1} β (SubNegZeroMonoid.toNegZeroClass.{u1} β (SubtractionMonoid.toSubNegZeroMonoid.{u1} β (SubtractionCommMonoid.toSubtractionMonoid.{u1} β (AddCommGroup.toDivisionAddCommMonoid.{u1} β (NormedAddCommGroup.toAddCommGroup.{u1} β _inst_1)))))) (v x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.neg Asymptotics.IsEquivalent.negₓ'. -/
theorem IsEquivalent.neg (huv : u ~[l] v) : (fun x => -u x) ~[l] fun x => -v x :=
  by
  rw [is_equivalent]
  convert huv.is_o.neg_left.neg_right
  ext
  simp
#align asymptotics.is_equivalent.neg Asymptotics.IsEquivalent.neg

end NormedAddCommGroup

open Asymptotics

section NormedField

variable {α β : Type _} [NormedField β] {t u v w : α → β} {l : Filter α}

/- warning: asymptotics.is_equivalent_iff_exists_eq_mul -> Asymptotics.isEquivalent_iff_exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, Iff (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v) (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (φ : α -> β) => Exists.{0} (Filter.Tendsto.{u1, u2} α β φ l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) (fun (hφ : Filter.Tendsto.{u1, u2} α β φ l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) => Filter.EventuallyEq.{u1, u2} α β l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, Iff (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l u v) (Exists.{max (succ u2) (succ u1)} (α -> β) (fun (φ : α -> β) => Exists.{0} (Filter.Tendsto.{u2, u1} α β φ l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedRing.toPseudoMetricSpace.{u1} β (SeminormedCommRing.toSeminormedRing.{u1} β (NormedCommRing.toSeminormedCommRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (DivisionSemiring.toSemiring.{u1} β (Semifield.toDivisionSemiring.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))) (fun (hφ : Filter.Tendsto.{u2, u1} α β φ l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedRing.toPseudoMetricSpace.{u1} β (SeminormedCommRing.toSeminormedRing.{u1} β (NormedCommRing.toSeminormedCommRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (DivisionSemiring.toSemiring.{u1} β (Semifield.toDivisionSemiring.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))) => Filter.EventuallyEq.{u2, u1} α β l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β (NormedRing.toRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_iff_exists_eq_mul Asymptotics.isEquivalent_iff_exists_eq_mulₓ'. -/
theorem isEquivalent_iff_exists_eq_mul :
    u ~[l] v ↔ ∃ (φ : α → β)(hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  by
  rw [is_equivalent, is_o_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [use φ + 1;use φ - 1] <;> constructor
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert h.add (eventually_eq.refl l v) <;> ext <;> simp [add_mul]
  · conv in 𝓝 _ => rw [← sub_self (1 : β)]
    exact hφ.sub tendsto_const_nhds
  · convert h.sub (eventually_eq.refl l v) <;> ext <;> simp [sub_mul]
#align asymptotics.is_equivalent_iff_exists_eq_mul Asymptotics.isEquivalent_iff_exists_eq_mul

/- warning: asymptotics.is_equivalent.exists_eq_mul -> Asymptotics.IsEquivalent.exists_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v) -> (Exists.{max (succ u1) (succ u2)} (α -> β) (fun (φ : α -> β) => Exists.{0} (Filter.Tendsto.{u1, u2} α β φ l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) (fun (hφ : Filter.Tendsto.{u1, u2} α β φ l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) => Filter.EventuallyEq.{u1, u2} α β l u (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))) φ v))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l u v) -> (Exists.{max (succ u2) (succ u1)} (α -> β) (fun (φ : α -> β) => Exists.{0} (Filter.Tendsto.{u2, u1} α β φ l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedRing.toPseudoMetricSpace.{u1} β (SeminormedCommRing.toSeminormedRing.{u1} β (NormedCommRing.toSeminormedCommRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (DivisionSemiring.toSemiring.{u1} β (Semifield.toDivisionSemiring.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))) (fun (hφ : Filter.Tendsto.{u2, u1} α β φ l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedRing.toPseudoMetricSpace.{u1} β (SeminormedCommRing.toSeminormedRing.{u1} β (NormedCommRing.toSeminormedCommRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (DivisionSemiring.toSemiring.{u1} β (Semifield.toDivisionSemiring.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))) => Filter.EventuallyEq.{u2, u1} α β l u (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β (NormedRing.toRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))))) φ v))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.exists_eq_mul Asymptotics.IsEquivalent.exists_eq_mulₓ'. -/
theorem IsEquivalent.exists_eq_mul (huv : u ~[l] v) :
    ∃ (φ : α → β)(hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  isEquivalent_iff_exists_eq_mul.mp huv
#align asymptotics.is_equivalent.exists_eq_mul Asymptotics.IsEquivalent.exists_eq_mul

/- warning: asymptotics.is_equivalent_of_tendsto_one -> Asymptotics.isEquivalent_of_tendsto_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => (Eq.{succ u2} β (v x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) -> (Eq.{succ u2} β (u x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))))))))) l) -> (Filter.Tendsto.{u1, u2} α β (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1)))))) u v) l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Filter.Eventually.{u2} α (fun (x : α) => (Eq.{succ u1} β (v x) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β (Semifield.toCommGroupWithZero.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1)))))))) -> (Eq.{succ u1} β (u x) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β (Semifield.toCommGroupWithZero.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))) l) -> (Filter.Tendsto.{u2, u1} α β (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHDiv.{max u2 u1} (α -> β) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => Field.toDiv.{u1} β (NormedField.toField.{u1} β _inst_1)))) u v) l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedRing.toPseudoMetricSpace.{u1} β (SeminormedCommRing.toSeminormedRing.{u1} β (NormedCommRing.toSeminormedCommRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (DivisionSemiring.toSemiring.{u1} β (Semifield.toDivisionSemiring.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))) -> (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_of_tendsto_one Asymptotics.isEquivalent_of_tendsto_oneₓ'. -/
theorem isEquivalent_of_tendsto_one (hz : ∀ᶠ x in l, v x = 0 → u x = 0)
    (huv : Tendsto (u / v) l (𝓝 1)) : u ~[l] v :=
  by
  rw [is_equivalent_iff_exists_eq_mul]
  refine' ⟨u / v, huv, hz.mono fun x hz' => (div_mul_cancel_of_imp hz').symm⟩
#align asymptotics.is_equivalent_of_tendsto_one Asymptotics.isEquivalent_of_tendsto_one

/- warning: asymptotics.is_equivalent_of_tendsto_one' -> Asymptotics.isEquivalent_of_tendsto_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (forall (x : α), (Eq.{succ u2} β (v x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) -> (Eq.{succ u2} β (u x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))))))))) -> (Filter.Tendsto.{u1, u2} α β (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1)))))) u v) l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (forall (x : α), (Eq.{succ u2} β (v x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (CommMonoidWithZero.toZero.{u2} β (CommGroupWithZero.toCommMonoidWithZero.{u2} β (Semifield.toCommGroupWithZero.{u2} β (Field.toSemifield.{u2} β (NormedField.toField.{u2} β _inst_1)))))))) -> (Eq.{succ u2} β (u x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β (CommMonoidWithZero.toZero.{u2} β (CommGroupWithZero.toCommMonoidWithZero.{u2} β (Semifield.toCommGroupWithZero.{u2} β (Field.toSemifield.{u2} β (NormedField.toField.{u2} β _inst_1))))))))) -> (Filter.Tendsto.{u1, u2} α β (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Field.toDiv.{u2} β (NormedField.toField.{u2} β _inst_1)))) u v) l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSeminormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β (Semiring.toOne.{u2} β (DivisionSemiring.toSemiring.{u2} β (Semifield.toDivisionSemiring.{u2} β (Field.toSemifield.{u2} β (NormedField.toField.{u2} β _inst_1))))))))) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v)
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_of_tendsto_one' Asymptotics.isEquivalent_of_tendsto_one'ₓ'. -/
theorem isEquivalent_of_tendsto_one' (hz : ∀ x, v x = 0 → u x = 0) (huv : Tendsto (u / v) l (𝓝 1)) :
    u ~[l] v :=
  isEquivalent_of_tendsto_one (eventually_of_forall hz) huv
#align asymptotics.is_equivalent_of_tendsto_one' Asymptotics.isEquivalent_of_tendsto_one'

/- warning: asymptotics.is_equivalent_iff_tendsto_one -> Asymptotics.isEquivalent_iff_tendsto_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Filter.Eventually.{u1} α (fun (x : α) => Ne.{succ u2} β (v x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β (MulZeroClass.toHasZero.{u2} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} β (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))) l) -> (Iff (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v) (Filter.Tendsto.{u1, u2} α β (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1)))))) u v) l (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedRing.toPseudoMetricSpace.{u2} β (SeminormedCommRing.toSemiNormedRing.{u2} β (NormedCommRing.toSeminormedCommRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (AddMonoidWithOne.toOne.{u2} β (AddGroupWithOne.toAddMonoidWithOne.{u2} β (AddCommGroupWithOne.toAddGroupWithOne.{u2} β (Ring.toAddCommGroupWithOne.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Filter.Eventually.{u2} α (fun (x : α) => Ne.{succ u1} β (v x) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β (CommMonoidWithZero.toZero.{u1} β (CommGroupWithZero.toCommMonoidWithZero.{u1} β (Semifield.toCommGroupWithZero.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1)))))))) l) -> (Iff (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l u v) (Filter.Tendsto.{u2, u1} α β (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHDiv.{max u2 u1} (α -> β) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => Field.toDiv.{u1} β (NormedField.toField.{u1} β _inst_1)))) u v) l (nhds.{u1} β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedRing.toPseudoMetricSpace.{u1} β (SeminormedCommRing.toSeminormedRing.{u1} β (NormedCommRing.toSeminormedCommRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β (Semiring.toOne.{u1} β (DivisionSemiring.toSemiring.{u1} β (Semifield.toDivisionSemiring.{u1} β (Field.toSemifield.{u1} β (NormedField.toField.{u1} β _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent_iff_tendsto_one Asymptotics.isEquivalent_iff_tendsto_oneₓ'. -/
theorem isEquivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) :
    u ~[l] v ↔ Tendsto (u / v) l (𝓝 1) := by
  constructor
  · intro hequiv
    have := hequiv.is_o.tendsto_div_nhds_zero
    simp only [Pi.sub_apply, sub_div] at this
    have key : tendsto (fun x => v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz => @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert this.add key
    · ext; simp
    · norm_num
  · exact is_equivalent_of_tendsto_one (hz.mono fun x hnvz hz => (hnvz hz).elim)
#align asymptotics.is_equivalent_iff_tendsto_one Asymptotics.isEquivalent_iff_tendsto_one

end NormedField

section Smul

/- warning: asymptotics.is_equivalent.smul -> Asymptotics.IsEquivalent.smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.smul Asymptotics.IsEquivalent.smulₓ'. -/
theorem IsEquivalent.smul {α E 𝕜 : Type _} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : α → 𝕜} {u v : α → E} {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
    (fun x => a x • u x) ~[l] fun x => b x • v x :=
  by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have :
    ((fun x : α => a x • u x) - fun x : α => b x • v x) =ᶠ[l] fun x => b x • (φ x • u x - v x) :=
    by
    convert(habφ.comp₂ (· • ·) <| eventually_eq.refl _ u).sub
        (eventually_eq.refl _ fun x => b x • v x)
    ext
    rw [Pi.mul_apply, mul_comm, mul_smul, ← smul_sub]
  refine' (is_o_congr this.symm <| eventually_eq.rfl).mp ((is_O_refl b l).smul_isLittleO _)
  rcases huv.is_O.exists_pos with ⟨C, hC, hCuv⟩
  rw [is_equivalent] at *
  rw [is_o_iff] at *
  rw [is_O_with] at hCuv
  simp only [Metric.tendsto_nhds, dist_eq_norm] at hφ
  intro c hc
  specialize hφ (c / 2 / C) (div_pos (by linarith) hC)
  specialize huv (show 0 < c / 2 by linarith)
  refine' hφ.mp (huv.mp <| hCuv.mono fun x hCuvx huvx hφx => _)
  have key :=
    calc
      ‖φ x - 1‖ * ‖u x‖ ≤ c / 2 / C * ‖u x‖ :=
        mul_le_mul_of_nonneg_right hφx.le (norm_nonneg <| u x)
      _ ≤ c / 2 / C * (C * ‖v x‖) := (mul_le_mul_of_nonneg_left hCuvx (div_pos (by linarith) hC).le)
      _ = c / 2 * ‖v x‖ := by field_simp [hC.ne.symm] ; ring
      
  calc
    ‖((fun x : α => φ x • u x) - v) x‖ = ‖(φ x - 1) • u x + (u x - v x)‖ := by
      simp [sub_smul, sub_add]
    _ ≤ ‖(φ x - 1) • u x‖ + ‖u x - v x‖ := (norm_add_le _ _)
    _ = ‖φ x - 1‖ * ‖u x‖ + ‖u x - v x‖ := by rw [norm_smul]
    _ ≤ c / 2 * ‖v x‖ + ‖u x - v x‖ := (add_le_add_right key _)
    _ ≤ c / 2 * ‖v x‖ + c / 2 * ‖v x‖ := (add_le_add_left huvx _)
    _ = c * ‖v x‖ := by ring
    
#align asymptotics.is_equivalent.smul Asymptotics.IsEquivalent.smul

end Smul

section mul_inv

variable {α β : Type _} [NormedField β] {t u v w : α → β} {l : Filter α}

/- warning: asymptotics.is_equivalent.mul -> Asymptotics.IsEquivalent.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {t : α -> β} {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l t u) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l v w) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))) t v) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))) u w))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {t : α -> β} {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l t u) -> (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l v w) -> (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β (NormedRing.toRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))))) t v) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> β) (α -> β) (α -> β) (instHMul.{max u2 u1} (α -> β) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u1} β (NonAssocRing.toNonUnitalNonAssocRing.{u1} β (Ring.toNonAssocRing.{u1} β (NormedRing.toRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))))))) u w))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.mul Asymptotics.IsEquivalent.mulₓ'. -/
theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
  htu.smul hvw
#align asymptotics.is_equivalent.mul Asymptotics.IsEquivalent.mul

/- warning: asymptotics.is_equivalent.inv -> Asymptotics.IsEquivalent.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l u v) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l (fun (x : α) => Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1)))) (u x)) (fun (x : α) => Inv.inv.{u2} β (DivInvMonoid.toHasInv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1)))) (v x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l u v) -> (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l (fun (x : α) => Inv.inv.{u1} β (Field.toInv.{u1} β (NormedField.toField.{u1} β _inst_1)) (u x)) (fun (x : α) => Inv.inv.{u1} β (Field.toInv.{u1} β (NormedField.toField.{u1} β _inst_1)) (v x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.inv Asymptotics.IsEquivalent.invₓ'. -/
theorem IsEquivalent.inv (huv : u ~[l] v) : (fun x => (u x)⁻¹) ~[l] fun x => (v x)⁻¹ :=
  by
  rw [is_equivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine' ⟨fun x => (φ x)⁻¹, tendsto.inv₀ hφ (by norm_num), _⟩
  convert h.inv
  ext
  simp [mul_inv]
#align asymptotics.is_equivalent.inv Asymptotics.IsEquivalent.inv

/- warning: asymptotics.is_equivalent.div -> Asymptotics.IsEquivalent.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {t : α -> β} {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u1} α}, (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l t u) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l v w) -> (Asymptotics.IsEquivalent.{u1, u2} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u2} β (NormedRing.toNonUnitalNormedRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))) l (fun (x : α) => HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1))))) (t x) (v x)) (fun (x : α) => HDiv.hDiv.{u2, u2, u2} β β β (instHDiv.{u2} β (DivInvMonoid.toHasDiv.{u2} β (DivisionRing.toDivInvMonoid.{u2} β (NormedDivisionRing.toDivisionRing.{u2} β (NormedField.toNormedDivisionRing.{u2} β _inst_1))))) (u x) (w x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedField.{u1} β] {t : α -> β} {u : α -> β} {v : α -> β} {w : α -> β} {l : Filter.{u2} α}, (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l t u) -> (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l v w) -> (Asymptotics.IsEquivalent.{u2, u1} α β (NonUnitalNormedRing.toNormedAddCommGroup.{u1} β (NormedRing.toNonUnitalNormedRing.{u1} β (NormedCommRing.toNormedRing.{u1} β (NormedField.toNormedCommRing.{u1} β _inst_1)))) l (fun (x : α) => HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (Field.toDiv.{u1} β (NormedField.toField.{u1} β _inst_1))) (t x) (v x)) (fun (x : α) => HDiv.hDiv.{u1, u1, u1} β β β (instHDiv.{u1} β (Field.toDiv.{u1} β (NormedField.toField.{u1} β _inst_1))) (u x) (w x)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_equivalent.div Asymptotics.IsEquivalent.divₓ'. -/
theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) :
    (fun x => t x / v x) ~[l] fun x => u x / w x := by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv
#align asymptotics.is_equivalent.div Asymptotics.IsEquivalent.div

end mul_inv

section NormedLinearOrderedField

variable {α β : Type _} [NormedLinearOrderedField β] {u v : α → β} {l : Filter α}

#print Asymptotics.IsEquivalent.tendsto_atTop /-
theorem IsEquivalent.tendsto_atTop [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop) :
    Tendsto v l atTop :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul zero_lt_one hφ)
#align asymptotics.is_equivalent.tendsto_at_top Asymptotics.IsEquivalent.tendsto_atTop
-/

#print Asymptotics.IsEquivalent.tendsto_atTop_iff /-
theorem IsEquivalent.tendsto_atTop_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atTop ↔ Tendsto v l atTop :=
  ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩
#align asymptotics.is_equivalent.tendsto_at_top_iff Asymptotics.IsEquivalent.tendsto_atTop_iff
-/

#print Asymptotics.IsEquivalent.tendsto_atBot /-
theorem IsEquivalent.tendsto_atBot [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot) :
    Tendsto v l atBot :=
  by
  convert tendsto_neg_at_top_at_bot.comp
      (huv.neg.tendsto_at_top <| tendsto_neg_at_bot_at_top.comp hu)
  ext
  simp
#align asymptotics.is_equivalent.tendsto_at_bot Asymptotics.IsEquivalent.tendsto_atBot
-/

#print Asymptotics.IsEquivalent.tendsto_atBot_iff /-
theorem IsEquivalent.tendsto_atBot_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atBot ↔ Tendsto v l atBot :=
  ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩
#align asymptotics.is_equivalent.tendsto_at_bot_iff Asymptotics.IsEquivalent.tendsto_atBot_iff
-/

end NormedLinearOrderedField

end Asymptotics

open Filter Asymptotics

open Asymptotics

variable {α β : Type _} [NormedAddCommGroup β]

/- warning: filter.eventually_eq.is_equivalent -> Filter.EventuallyEq.isEquivalent is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {u : α -> β} {v : α -> β} {l : Filter.{u1} α}, (Filter.EventuallyEq.{u1, u2} α β l u v) -> (Asymptotics.IsEquivalent.{u1, u2} α β _inst_1 l u v)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} β] {u : α -> β} {v : α -> β} {l : Filter.{u2} α}, (Filter.EventuallyEq.{u2, u1} α β l u v) -> (Asymptotics.IsEquivalent.{u2, u1} α β _inst_1 l u v)
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.is_equivalent Filter.EventuallyEq.isEquivalentₓ'. -/
theorem Filter.EventuallyEq.isEquivalent {u v : α → β} {l : Filter α} (h : u =ᶠ[l] v) : u ~[l] v :=
  IsEquivalent.congr_right (isLittleO_refl_left _ _) h
#align filter.eventually_eq.is_equivalent Filter.EventuallyEq.isEquivalent

