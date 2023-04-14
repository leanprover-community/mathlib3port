/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler

! This file was ported from Lean 3 source module order.filter.zero_and_bounded_at_filter
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Submodule.Basic
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `zero_at_filter` as well as being
`bounded_at_filter`. Alongside this we construct the `submodule`, `add_submonoid` of functions
that are `zero_at_filter`. Similarly, we construct the `submodule` and `subalgebra` of functions
that are `bounded_at_filter`.

-/


namespace Filter

variable {α β : Type _}

open Topology

#print Filter.ZeroAtFilter /-
/-- If `l` is a filter on `α`, then a function `f : α → β` is `zero_at_filter l`
  if it tends to zero along `l`. -/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)
#align filter.zero_at_filter Filter.ZeroAtFilter
-/

#print Filter.zero_zeroAtFilter /-
theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds
#align filter.zero_zero_at_filter Filter.zero_zeroAtFilter
-/

/- warning: filter.zero_at_filter.add -> Filter.ZeroAtFilter.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : AddZeroClass.{u2} β] [_inst_3 : ContinuousAdd.{u2} β _inst_1 (AddZeroClass.toHasAdd.{u2} β _inst_2)] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β _inst_2) _inst_1 l f) -> (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β _inst_2) _inst_1 l g) -> (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β _inst_2) _inst_1 l (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasAdd.{u2} β _inst_2))) f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : AddZeroClass.{u2} β] [_inst_3 : ContinuousAdd.{u2} β _inst_1 (AddZeroClass.toAdd.{u2} β _inst_2)] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toZero.{u2} β _inst_2) _inst_1 l f) -> (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toZero.{u2} β _inst_2) _inst_1 l g) -> (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toZero.{u2} β _inst_2) _inst_1 l (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toAdd.{u2} β _inst_2))) f g))
Case conversion may be inaccurate. Consider using '#align filter.zero_at_filter.add Filter.ZeroAtFilter.addₓ'. -/
theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β] {l : Filter α}
    {f g : α → β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) : ZeroAtFilter l (f + g) := by
  simpa using hf.add hg
#align filter.zero_at_filter.add Filter.ZeroAtFilter.add

/- warning: filter.zero_at_filter.neg -> Filter.ZeroAtFilter.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : AddGroup.{u2} β] [_inst_3 : ContinuousNeg.{u2} β _inst_1 (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] {l : Filter.{u1} α} {f : α -> β}, (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) _inst_1 l f) -> (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) _inst_1 l (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : AddGroup.{u2} β] [_inst_3 : ContinuousNeg.{u2} β _inst_1 (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))] {l : Filter.{u1} α} {f : α -> β}, (Filter.ZeroAtFilter.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) _inst_1 l f) -> (Filter.ZeroAtFilter.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) _inst_1 l (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) f))
Case conversion may be inaccurate. Consider using '#align filter.zero_at_filter.neg Filter.ZeroAtFilter.negₓ'. -/
theorem ZeroAtFilter.neg [TopologicalSpace β] [AddGroup β] [ContinuousNeg β] {l : Filter α}
    {f : α → β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by simpa using hf.neg
#align filter.zero_at_filter.neg Filter.ZeroAtFilter.neg

#print Filter.ZeroAtFilter.smul /-
theorem ZeroAtFilter.smul {𝕜 : Type _} [TopologicalSpace 𝕜] [TopologicalSpace β] [Zero 𝕜] [Zero β]
    [SMulWithZero 𝕜 β] [ContinuousSMul 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using hf.const_smul c
#align filter.zero_at_filter.smul Filter.ZeroAtFilter.smul
-/

/- warning: filter.zero_at_filter_submodule -> Filter.zeroAtFilterSubmodule is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : Semiring.{u2} β] [_inst_3 : ContinuousAdd.{u2} β _inst_1 (Distrib.toHasAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2))))] [_inst_4 : ContinuousMul.{u2} β _inst_1 (Distrib.toHasMul.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2))))], (Filter.{u1} α) -> (Submodule.{u2, max u1 u2} β (α -> β) _inst_2 (Pi.addCommMonoid.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2)))) (Pi.Function.module.{u1, u2, u2} α β β _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2))) (Semiring.toModule.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : Semiring.{u2} β] [_inst_3 : ContinuousAdd.{u2} β _inst_1 (Distrib.toAdd.{u2} β (NonUnitalNonAssocSemiring.toDistrib.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2))))] [_inst_4 : ContinuousMul.{u2} β _inst_1 (NonUnitalNonAssocSemiring.toMul.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2)))], (Filter.{u1} α) -> (Submodule.{u2, max u1 u2} β (α -> β) _inst_2 (Pi.addCommMonoid.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2)))) (Pi.module.{u1, u2, u2} α (fun (a._@.Mathlib.Order.Filter.ZeroAndBoundedAtFilter._hyg.224 : α) => β) β _inst_2 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} β (Semiring.toNonAssocSemiring.{u2} β _inst_2))) (fun (i : α) => Semiring.toModule.{u2} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align filter.zero_at_filter_submodule Filter.zeroAtFilterSubmoduleₓ'. -/
/-- `zero_at_filter_submodule l` is the submodule of `f : α → β` which
tend to zero along `l`. -/
def zeroAtFilterSubmodule [TopologicalSpace β] [Semiring β] [ContinuousAdd β] [ContinuousMul β]
    (l : Filter α) : Submodule β (α → β)
    where
  carrier := ZeroAtFilter l
  zero_mem' := zero_zeroAtFilter l
  add_mem' a b ha hb := ha.add hb
  smul_mem' c f hf := hf.smul c
#align filter.zero_at_filter_submodule Filter.zeroAtFilterSubmodule

/- warning: filter.zero_at_filter_add_submonoid -> Filter.zeroAtFilterAddSubmonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : AddZeroClass.{u2} β] [_inst_3 : ContinuousAdd.{u2} β _inst_1 (AddZeroClass.toHasAdd.{u2} β _inst_2)], (Filter.{u1} α) -> (AddSubmonoid.{max u1 u2} (α -> β) (Pi.addZeroClass.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} β] [_inst_2 : AddZeroClass.{u2} β] [_inst_3 : ContinuousAdd.{u2} β _inst_1 (AddZeroClass.toAdd.{u2} β _inst_2)], (Filter.{u1} α) -> (AddSubmonoid.{max u1 u2} (α -> β) (Pi.addZeroClass.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_2)))
Case conversion may be inaccurate. Consider using '#align filter.zero_at_filter_add_submonoid Filter.zeroAtFilterAddSubmonoidₓ'. -/
/-- `zero_at_filter_add_submonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β)
    where
  carrier := ZeroAtFilter l
  add_mem' a b ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l
#align filter.zero_at_filter_add_submonoid Filter.zeroAtFilterAddSubmonoid

#print Filter.BoundedAtFilter /-
/-- If `l` is a filter on `α`, then a function `f: α → β` is `bounded_at_filter l`
if `f =O[l] 1`. -/
def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)
#align filter.bounded_at_filter Filter.BoundedAtFilter
-/

/- warning: filter.zero_at_filter.bounded_at_filter -> Filter.ZeroAtFilter.boundedAtFilter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {f : α -> β}, (Filter.ZeroAtFilter.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l f)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {f : α -> β}, (Filter.ZeroAtFilter.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_1)))))) (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_1)))) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toNorm.{u2} β _inst_1) l f)
Case conversion may be inaccurate. Consider using '#align filter.zero_at_filter.bounded_at_filter Filter.ZeroAtFilter.boundedAtFilterₓ'. -/
theorem ZeroAtFilter.boundedAtFilter [NormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f :=
  by
  rw [zero_at_filter, ← Asymptotics.isLittleO_const_iff (one_ne_zero' ℝ)] at hf
  exact hf.is_O
#align filter.zero_at_filter.bounded_at_filter Filter.ZeroAtFilter.boundedAtFilter

#print Filter.const_boundedAtFilter /-
theorem const_boundedAtFilter [NormedField β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α → β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l
#align filter.const_bounded_at_filter Filter.const_boundedAtFilter
-/

/- warning: filter.bounded_at_filter.add -> Filter.BoundedAtFilter.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l g) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))) f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toNorm.{u2} β _inst_1) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toNorm.{u2} β _inst_1) l g) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toNorm.{u2} β _inst_1) l (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1)))))))) f g))
Case conversion may be inaccurate. Consider using '#align filter.bounded_at_filter.add Filter.BoundedAtFilter.addₓ'. -/
theorem BoundedAtFilter.add [NormedAddCommGroup β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using hf.add hg
#align filter.bounded_at_filter.add Filter.BoundedAtFilter.add

/- warning: filter.bounded_at_filter.neg -> Filter.BoundedAtFilter.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {f : α -> β}, (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toHasNorm.{u2} β _inst_1) l (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (NormedAddGroup.toAddGroup.{u2} β (NormedAddCommGroup.toNormedAddGroup.{u2} β _inst_1))))) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} β] {l : Filter.{u1} α} {f : α -> β}, (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toNorm.{u2} β _inst_1) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedAddCommGroup.toNorm.{u2} β _inst_1) l (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_1))))))) f))
Case conversion may be inaccurate. Consider using '#align filter.bounded_at_filter.neg Filter.BoundedAtFilter.negₓ'. -/
theorem BoundedAtFilter.neg [NormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left
#align filter.bounded_at_filter.neg Filter.BoundedAtFilter.neg

#print Filter.BoundedAtFilter.smul /-
theorem BoundedAtFilter.smul {𝕜 : Type _} [NormedField 𝕜] [NormedAddCommGroup β] [NormedSpace 𝕜 β]
    {l : Filter α} {f : α → β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c
#align filter.bounded_at_filter.smul Filter.BoundedAtFilter.smul
-/

/- warning: filter.bounded_at_filter.mul -> Filter.BoundedAtFilter.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.BoundedAtFilter.{u1, u2} α β (NormedField.toHasNorm.{u2} β _inst_1) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedField.toHasNorm.{u2} β _inst_1) l g) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedField.toHasNorm.{u2} β _inst_1) l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Distrib.toHasMul.{u2} β (Ring.toDistrib.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1))))))) f g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NormedField.{u2} β] {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.BoundedAtFilter.{u1, u2} α β (NormedField.toNorm.{u2} β _inst_1) l f) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedField.toNorm.{u2} β _inst_1) l g) -> (Filter.BoundedAtFilter.{u1, u2} α β (NormedField.toNorm.{u2} β _inst_1) l (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NonUnitalNonAssocRing.toMul.{u2} β (NonAssocRing.toNonUnitalNonAssocRing.{u2} β (Ring.toNonAssocRing.{u2} β (NormedRing.toRing.{u2} β (NormedCommRing.toNormedRing.{u2} β (NormedField.toNormedCommRing.{u2} β _inst_1)))))))) f g))
Case conversion may be inaccurate. Consider using '#align filter.bounded_at_filter.mul Filter.BoundedAtFilter.mulₓ'. -/
theorem BoundedAtFilter.mul [NormedField β] {l : Filter α} {f g : α → β} (hf : BoundedAtFilter l f)
    (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) :=
  by
  refine' (hf.mul hg).trans _
  convert Asymptotics.isBigO_refl _ l
  ext x
  simp
#align filter.bounded_at_filter.mul Filter.BoundedAtFilter.mul

#print Filter.boundedFilterSubmodule /-
/-- The submodule of functions that are bounded along a filter `l`. -/
def boundedFilterSubmodule [NormedField β] (l : Filter α) : Submodule β (α → β)
    where
  carrier := BoundedAtFilter l
  zero_mem' := const_boundedAtFilter l 0
  add_mem' f g hf hg := hf.add hg
  smul_mem' c f hf := hf.smul c
#align filter.bounded_filter_submodule Filter.boundedFilterSubmodule
-/

#print Filter.boundedFilterSubalgebra /-
/-- The subalgebra of functions that are bounded along a filter `l`. -/
def boundedFilterSubalgebra [NormedField β] (l : Filter α) : Subalgebra β (α → β) :=
  by
  refine' Submodule.toSubalgebra (bounded_filter_submodule l) _ fun f g hf hg => _
  · exact const_bounded_at_filter l (1 : β)
  · simpa only [Pi.one_apply, mul_one, norm_mul] using hf.mul hg
#align filter.bounded_filter_subalgebra Filter.boundedFilterSubalgebra
-/

end Filter

