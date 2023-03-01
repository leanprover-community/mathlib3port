/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.algebra.monoid
! leanprover-community/mathlib commit 6efec6bb9fcaed3cf1baaddb2eaadd8a2a06679c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.Order.Filter.Pointwise
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Algebra.BigOperators.Pi
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Theory of topological monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/


universe u v

open Classical Set Filter TopologicalSpace

open Classical Topology BigOperators Pointwise

variable {ι α X M N : Type _} [TopologicalSpace X]

#print continuous_one /-
@[to_additive]
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1
#align continuous_one continuous_one
#align continuous_zero continuous_zero
-/

#print ContinuousAdd /-
/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `add_monoid M` and `has_continuous_add M`.

Continuity in only the left/right argument can be stated using
`has_continuous_const_vadd α α`/`has_continuous_const_vadd αᵐᵒᵖ α`. -/
class ContinuousAdd (M : Type u) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2
#align has_continuous_add ContinuousAdd
-/

#print ContinuousMul /-
/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `monoid M`
and `has_continuous_mul M`.

Continuity in only the left/right argument can be stated using
`has_continuous_const_smul α α`/`has_continuous_const_smul αᵐᵒᵖ α`. -/
@[to_additive]
class ContinuousMul (M : Type u) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2
#align has_continuous_mul ContinuousMul
#align has_continuous_add ContinuousAdd
-/

section ContinuousMul

variable [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive]
instance : ContinuousMul Mᵒᵈ :=
  ‹ContinuousMul M›

/- warning: continuous_mul -> continuous_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3], Continuous.{u1, u1} (Prod.{u1, u1} M M) M (Prod.topologicalSpace.{u1, u1} M M _inst_2 _inst_2) _inst_2 (fun (p : Prod.{u1, u1} M M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (Prod.fst.{u1, u1} M M p) (Prod.snd.{u1, u1} M M p))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3], Continuous.{u1, u1} (Prod.{u1, u1} M M) M (instTopologicalSpaceProd.{u1, u1} M M _inst_2 _inst_2) _inst_2 (fun (p : Prod.{u1, u1} M M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (Prod.fst.{u1, u1} M M p) (Prod.snd.{u1, u1} M M p))
Case conversion may be inaccurate. Consider using '#align continuous_mul continuous_mulₓ'. -/
@[to_additive]
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  ContinuousMul.continuous_mul
#align continuous_mul continuous_mul
#align continuous_add continuous_add

#print ContinuousMul.to_continuousSMul /-
@[to_additive]
instance ContinuousMul.to_continuousSMul : ContinuousSMul M M :=
  ⟨continuous_mul⟩
#align has_continuous_mul.to_has_continuous_smul ContinuousMul.to_continuousSMul
#align has_continuous_add.to_has_continuous_vadd ContinuousAdd.to_continuousVAdd
-/

#print ContinuousMul.to_continuousSMul_op /-
@[to_additive]
instance ContinuousMul.to_continuousSMul_op : ContinuousSMul Mᵐᵒᵖ M :=
  ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) from
      continuous_mul.comp <|
        continuous_swap.comp <| Continuous.prod_map MulOpposite.continuous_unop continuous_id⟩
#align has_continuous_mul.to_has_continuous_smul_op ContinuousMul.to_continuousSMul_op
#align has_continuous_add.to_has_continuous_vadd_op ContinuousAdd.to_continuousVAdd_op
-/

/- warning: continuous.mul -> Continuous.mul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] {f : X -> M} {g : X -> M}, (Continuous.{u1, u2} X M _inst_1 _inst_2 f) -> (Continuous.{u1, u2} X M _inst_1 _inst_2 g) -> (Continuous.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) (f x) (g x)))
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {f : X -> M} {g : X -> M}, (Continuous.{u2, u1} X M _inst_1 _inst_2 f) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 g) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.mul Continuous.mulₓ'. -/
@[continuity, to_additive]
theorem Continuous.mul {f g : X → M} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x * g x :=
  continuous_mul.comp (hf.prod_mk hg : _)
#align continuous.mul Continuous.mul
#align continuous.add Continuous.add

#print continuous_mul_left /-
@[to_additive]
theorem continuous_mul_left (a : M) : Continuous fun b : M => a * b :=
  continuous_const.mul continuous_id
#align continuous_mul_left continuous_mul_left
#align continuous_add_left continuous_add_left
-/

#print continuous_mul_right /-
@[to_additive]
theorem continuous_mul_right (a : M) : Continuous fun b : M => b * a :=
  continuous_id.mul continuous_const
#align continuous_mul_right continuous_mul_right
#align continuous_add_right continuous_add_right
-/

/- warning: continuous_on.mul -> ContinuousOn.mul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] {f : X -> M} {g : X -> M} {s : Set.{u1} X}, (ContinuousOn.{u1, u2} X M _inst_1 _inst_2 f s) -> (ContinuousOn.{u1, u2} X M _inst_1 _inst_2 g s) -> (ContinuousOn.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) (f x) (g x)) s)
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {f : X -> M} {g : X -> M} {s : Set.{u2} X}, (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 f s) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 g s) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.mul ContinuousOn.mulₓ'. -/
@[to_additive]
theorem ContinuousOn.mul {f g : X → M} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x * g x) s :=
  (continuous_mul.comp_continuousOn (hf.Prod hg) : _)
#align continuous_on.mul ContinuousOn.mul
#align continuous_on.add ContinuousOn.add

/- warning: tendsto_mul -> tendsto_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {a : M} {b : M}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} M M) M (fun (p : Prod.{u1, u1} M M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (Prod.fst.{u1, u1} M M p) (Prod.snd.{u1, u1} M M p)) (nhds.{u1} (Prod.{u1, u1} M M) (Prod.topologicalSpace.{u1, u1} M M _inst_2 _inst_2) (Prod.mk.{u1, u1} M M a b)) (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) a b))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {a : M} {b : M}, Filter.Tendsto.{u1, u1} (Prod.{u1, u1} M M) M (fun (p : Prod.{u1, u1} M M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (Prod.fst.{u1, u1} M M p) (Prod.snd.{u1, u1} M M p)) (nhds.{u1} (Prod.{u1, u1} M M) (instTopologicalSpaceProd.{u1, u1} M M _inst_2 _inst_2) (Prod.mk.{u1, u1} M M a b)) (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) a b))
Case conversion may be inaccurate. Consider using '#align tendsto_mul tendsto_mulₓ'. -/
@[to_additive]
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)
#align tendsto_mul tendsto_mul
#align tendsto_add tendsto_add

/- warning: filter.tendsto.mul -> Filter.Tendsto.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] {f : α -> M} {g : α -> M} {x : Filter.{u1} α} {a : M} {b : M}, (Filter.Tendsto.{u1, u2} α M f x (nhds.{u2} M _inst_2 a)) -> (Filter.Tendsto.{u1, u2} α M g x (nhds.{u2} M _inst_2 b)) -> (Filter.Tendsto.{u1, u2} α M (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) (f x) (g x)) x (nhds.{u2} M _inst_2 (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) a b)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {f : α -> M} {g : α -> M} {x : Filter.{u2} α} {a : M} {b : M}, (Filter.Tendsto.{u2, u1} α M f x (nhds.{u1} M _inst_2 a)) -> (Filter.Tendsto.{u2, u1} α M g x (nhds.{u1} M _inst_2 b)) -> (Filter.Tendsto.{u2, u1} α M (fun (x : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (f x) (g x)) x (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) a b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.mul Filter.Tendsto.mulₓ'. -/
@[to_additive]
theorem Filter.Tendsto.mul {f g : α → M} {x : Filter α} {a b : M} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => f x * g x) x (𝓝 (a * b)) :=
  tendsto_mul.comp (hf.prod_mk_nhds hg)
#align filter.tendsto.mul Filter.Tendsto.mul
#align filter.tendsto.add Filter.Tendsto.add

/- warning: filter.tendsto.const_mul -> Filter.Tendsto.const_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] (b : M) {c : M} {f : α -> M} {l : Filter.{u1} α}, (Filter.Tendsto.{u1, u2} α M (fun (k : α) => f k) l (nhds.{u2} M _inst_2 c)) -> (Filter.Tendsto.{u1, u2} α M (fun (k : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) b (f k)) l (nhds.{u2} M _inst_2 (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) b c)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] (b : M) {c : M} {f : α -> M} {l : Filter.{u2} α}, (Filter.Tendsto.{u2, u1} α M (fun (k : α) => f k) l (nhds.{u1} M _inst_2 c)) -> (Filter.Tendsto.{u2, u1} α M (fun (k : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) b (f k)) l (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) b c)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.const_mul Filter.Tendsto.const_mulₓ'. -/
@[to_additive]
theorem Filter.Tendsto.const_mul (b : M) {c : M} {f : α → M} {l : Filter α}
    (h : Tendsto (fun k : α => f k) l (𝓝 c)) : Tendsto (fun k : α => b * f k) l (𝓝 (b * c)) :=
  tendsto_const_nhds.mul h
#align filter.tendsto.const_mul Filter.Tendsto.const_mul
#align filter.tendsto.const_add Filter.Tendsto.const_add

/- warning: filter.tendsto.mul_const -> Filter.Tendsto.mul_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] (b : M) {c : M} {f : α -> M} {l : Filter.{u1} α}, (Filter.Tendsto.{u1, u2} α M (fun (k : α) => f k) l (nhds.{u2} M _inst_2 c)) -> (Filter.Tendsto.{u1, u2} α M (fun (k : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) (f k) b) l (nhds.{u2} M _inst_2 (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) c b)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] (b : M) {c : M} {f : α -> M} {l : Filter.{u2} α}, (Filter.Tendsto.{u2, u1} α M (fun (k : α) => f k) l (nhds.{u1} M _inst_2 c)) -> (Filter.Tendsto.{u2, u1} α M (fun (k : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (f k) b) l (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) c b)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.mul_const Filter.Tendsto.mul_constₓ'. -/
@[to_additive]
theorem Filter.Tendsto.mul_const (b : M) {c : M} {f : α → M} {l : Filter α}
    (h : Tendsto (fun k : α => f k) l (𝓝 c)) : Tendsto (fun k : α => f k * b) l (𝓝 (c * b)) :=
  h.mul tendsto_const_nhds
#align filter.tendsto.mul_const Filter.Tendsto.mul_const
#align filter.tendsto.add_const Filter.Tendsto.add_const

/- warning: le_nhds_mul -> le_nhds_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] (a : M) (b : M), LE.le.{u1} (Filter.{u1} M) (Preorder.toLE.{u1} (Filter.{u1} M) (PartialOrder.toPreorder.{u1} (Filter.{u1} M) (Filter.partialOrder.{u1} M))) (HMul.hMul.{u1, u1, u1} (Filter.{u1} M) (Filter.{u1} M) (Filter.{u1} M) (instHMul.{u1} (Filter.{u1} M) (Filter.instMul.{u1} M _inst_3)) (nhds.{u1} M _inst_2 a) (nhds.{u1} M _inst_2 b)) (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) a b))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] (a : M) (b : M), LE.le.{u1} (Filter.{u1} M) (Preorder.toLE.{u1} (Filter.{u1} M) (PartialOrder.toPreorder.{u1} (Filter.{u1} M) (Filter.instPartialOrderFilter.{u1} M))) (HMul.hMul.{u1, u1, u1} (Filter.{u1} M) (Filter.{u1} M) (Filter.{u1} M) (instHMul.{u1} (Filter.{u1} M) (Filter.instMul.{u1} M _inst_3)) (nhds.{u1} M _inst_2 a) (nhds.{u1} M _inst_2 b)) (nhds.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) a b))
Case conversion may be inaccurate. Consider using '#align le_nhds_mul le_nhds_mulₓ'. -/
@[to_additive]
theorem le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b ≤ 𝓝 (a * b) :=
  by
  rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq]
  exact continuous_mul.tendsto _
#align le_nhds_mul le_nhds_mul
#align le_nhds_add le_nhds_add

/- warning: nhds_one_mul_nhds -> nhds_one_mul_nhds is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : TopologicalSpace.{u1} M] [_inst_7 : ContinuousMul.{u1} M _inst_6 (MulOneClass.toHasMul.{u1} M _inst_5)] (a : M), Eq.{succ u1} (Filter.{u1} M) (HMul.hMul.{u1, u1, u1} (Filter.{u1} M) (Filter.{u1} M) (Filter.{u1} M) (instHMul.{u1} (Filter.{u1} M) (Filter.instMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_5))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_5))))) (nhds.{u1} M _inst_6 a)) (nhds.{u1} M _inst_6 a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : TopologicalSpace.{u1} M] [_inst_7 : ContinuousMul.{u1} M _inst_6 (MulOneClass.toMul.{u1} M _inst_5)] (a : M), Eq.{succ u1} (Filter.{u1} M) (HMul.hMul.{u1, u1, u1} (Filter.{u1} M) (Filter.{u1} M) (Filter.{u1} M) (instHMul.{u1} (Filter.{u1} M) (Filter.instMul.{u1} M (MulOneClass.toMul.{u1} M _inst_5))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_5)))) (nhds.{u1} M _inst_6 a)) (nhds.{u1} M _inst_6 a)
Case conversion may be inaccurate. Consider using '#align nhds_one_mul_nhds nhds_one_mul_nhdsₓ'. -/
@[simp, to_additive]
theorem nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm <|
    le_mul_of_one_le_left' <| pure_le_nhds 1
#align nhds_one_mul_nhds nhds_one_mul_nhds
#align nhds_zero_add_nhds nhds_zero_add_nhds

/- warning: nhds_mul_nhds_one -> nhds_mul_nhds_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : TopologicalSpace.{u1} M] [_inst_7 : ContinuousMul.{u1} M _inst_6 (MulOneClass.toHasMul.{u1} M _inst_5)] (a : M), Eq.{succ u1} (Filter.{u1} M) (HMul.hMul.{u1, u1, u1} (Filter.{u1} M) (Filter.{u1} M) (Filter.{u1} M) (instHMul.{u1} (Filter.{u1} M) (Filter.instMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_5))) (nhds.{u1} M _inst_6 a) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_5)))))) (nhds.{u1} M _inst_6 a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : TopologicalSpace.{u1} M] [_inst_7 : ContinuousMul.{u1} M _inst_6 (MulOneClass.toMul.{u1} M _inst_5)] (a : M), Eq.{succ u1} (Filter.{u1} M) (HMul.hMul.{u1, u1, u1} (Filter.{u1} M) (Filter.{u1} M) (Filter.{u1} M) (instHMul.{u1} (Filter.{u1} M) (Filter.instMul.{u1} M (MulOneClass.toMul.{u1} M _inst_5))) (nhds.{u1} M _inst_6 a) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_5))))) (nhds.{u1} M _inst_6 a)
Case conversion may be inaccurate. Consider using '#align nhds_mul_nhds_one nhds_mul_nhds_oneₓ'. -/
@[simp, to_additive]
theorem nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 a * 𝓝 1 = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm <|
    le_mul_of_one_le_right' <| pure_le_nhds 1
#align nhds_mul_nhds_one nhds_mul_nhds_one
#align nhds_add_nhds_zero nhds_add_nhds_zero

section tendsto_nhds

variable {𝕜 : Type _} [Preorder 𝕜] [Zero 𝕜] [Mul 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
  {l : Filter α} {f : α → 𝕜} {b c : 𝕜} (hb : 0 < b)

#print Filter.TendstoNhdsWithinIoi.const_mul /-
theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] [PosMulReflectLT 𝕜]
    (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => b * f a) l (𝓝[>] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_left hb).mpr
#align filter.tendsto_nhds_within_Ioi.const_mul Filter.TendstoNhdsWithinIoi.const_mul
-/

#print Filter.TendstoNhdsWithinIio.const_mul /-
theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] [PosMulReflectLT 𝕜]
    (h : Tendsto f l (𝓝[<] c)) : Tendsto (fun a => b * f a) l (𝓝[<] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_left hb).mpr
#align filter.tendsto_nhds_within_Iio.const_mul Filter.TendstoNhdsWithinIio.const_mul
-/

#print Filter.TendstoNhdsWithinIoi.mul_const /-
theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] [MulPosReflectLT 𝕜]
    (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => f a * b) l (𝓝[>] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_right hb).mpr
#align filter.tendsto_nhds_within_Ioi.mul_const Filter.TendstoNhdsWithinIoi.mul_const
-/

#print Filter.TendstoNhdsWithinIio.mul_const /-
theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] [MulPosReflectLT 𝕜]
    (h : Tendsto f l (𝓝[<] c)) : Tendsto (fun a => f a * b) l (𝓝[<] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_right hb).mpr
#align filter.tendsto_nhds_within_Iio.mul_const Filter.TendstoNhdsWithinIio.mul_const
-/

end tendsto_nhds

/- warning: filter.tendsto.units -> Filter.Tendsto.units is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} N] [_inst_6 : Monoid.{u2} N] [_inst_7 : ContinuousMul.{u2} N _inst_5 (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_6))] [_inst_8 : T2Space.{u2} N _inst_5] {f : ι -> (Units.{u2} N _inst_6)} {r₁ : N} {r₂ : N} {l : Filter.{u1} ι} [_inst_9 : Filter.NeBot.{u1} ι l], (Filter.Tendsto.{u1, u2} ι N (fun (x : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} N _inst_6) N (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} N _inst_6) N (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} N _inst_6) N (coeBase.{succ u2, succ u2} (Units.{u2} N _inst_6) N (Units.hasCoe.{u2} N _inst_6)))) (f x)) l (nhds.{u2} N _inst_5 r₁)) -> (Filter.Tendsto.{u1, u2} ι N (fun (x : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} N _inst_6) N (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} N _inst_6) N (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} N _inst_6) N (coeBase.{succ u2, succ u2} (Units.{u2} N _inst_6) N (Units.hasCoe.{u2} N _inst_6)))) (Inv.inv.{u2} (Units.{u2} N _inst_6) (Units.hasInv.{u2} N _inst_6) (f x))) l (nhds.{u2} N _inst_5 r₂)) -> (Units.{u2} N _inst_6)
but is expected to have type
  forall {ι : Type.{u1}} {N : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} N] [_inst_6 : Monoid.{u2} N] [_inst_7 : ContinuousMul.{u2} N _inst_5 (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_6))] [_inst_8 : T2Space.{u2} N _inst_5] {f : ι -> (Units.{u2} N _inst_6)} {r₁ : N} {r₂ : N} {l : Filter.{u1} ι} [_inst_9 : Filter.NeBot.{u1} ι l], (Filter.Tendsto.{u1, u2} ι N (fun (x : ι) => Units.val.{u2} N _inst_6 (f x)) l (nhds.{u2} N _inst_5 r₁)) -> (Filter.Tendsto.{u1, u2} ι N (fun (x : ι) => Units.val.{u2} N _inst_6 (Inv.inv.{u2} (Units.{u2} N _inst_6) (Units.instInvUnits.{u2} N _inst_6) (f x))) l (nhds.{u2} N _inst_5 r₂)) -> (Units.{u2} N _inst_6)
Case conversion may be inaccurate. Consider using '#align filter.tendsto.units Filter.Tendsto.unitsₓ'. -/
/-- Construct a unit from limits of units and their inverses. -/
@[to_additive Filter.Tendsto.addUnits
      "Construct an additive unit from limits of additive units\nand their negatives.",
  simps]
def Filter.Tendsto.units [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2Space N] {f : ι → Nˣ}
    {r₁ r₂ : N} {l : Filter ι} [l.ne_bot] (h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁))
    (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ
    where
  val := r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁
#align filter.tendsto.units Filter.Tendsto.units
#align filter.tendsto.add_units Filter.Tendsto.addUnits

/- warning: continuous_at.mul -> ContinuousAt.mul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] {f : X -> M} {g : X -> M} {x : X}, (ContinuousAt.{u1, u2} X M _inst_1 _inst_2 f x) -> (ContinuousAt.{u1, u2} X M _inst_1 _inst_2 g x) -> (ContinuousAt.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) (f x) (g x)) x)
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {f : X -> M} {g : X -> M} {x : X}, (ContinuousAt.{u2, u1} X M _inst_1 _inst_2 f x) -> (ContinuousAt.{u2, u1} X M _inst_1 _inst_2 g x) -> (ContinuousAt.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (f x) (g x)) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.mul ContinuousAt.mulₓ'. -/
@[to_additive]
theorem ContinuousAt.mul {f g : X → M} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x * g x) x :=
  hf.mul hg
#align continuous_at.mul ContinuousAt.mul
#align continuous_at.add ContinuousAt.add

/- warning: continuous_within_at.mul -> ContinuousWithinAt.mul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Mul.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 _inst_3] {f : X -> M} {g : X -> M} {s : Set.{u1} X} {x : X}, (ContinuousWithinAt.{u1, u2} X M _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u1, u2} X M _inst_1 _inst_2 g s x) -> (ContinuousWithinAt.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_3) (f x) (g x)) s x)
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Mul.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 _inst_3] {f : X -> M} {g : X -> M} {s : Set.{u2} X} {x : X}, (ContinuousWithinAt.{u2, u1} X M _inst_1 _inst_2 f s x) -> (ContinuousWithinAt.{u2, u1} X M _inst_1 _inst_2 g s x) -> (ContinuousWithinAt.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_3) (f x) (g x)) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.mul ContinuousWithinAt.mulₓ'. -/
@[to_additive]
theorem ContinuousWithinAt.mul {f g : X → M} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun x => f x * g x) s x :=
  hf.mul hg
#align continuous_within_at.mul ContinuousWithinAt.mul
#align continuous_within_at.add ContinuousWithinAt.add

@[to_additive]
instance [TopologicalSpace N] [Mul N] [ContinuousMul N] : ContinuousMul (M × N) :=
  ⟨(continuous_fst.fst'.mul continuous_fst.snd').prod_mk
      (continuous_snd.fst'.mul continuous_snd.snd')⟩

#print Pi.continuousMul /-
@[to_additive]
instance Pi.continuousMul {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, ContinuousMul (C i)] : ContinuousMul (∀ i, C i)
    where continuous_mul :=
    continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'
#align pi.has_continuous_mul Pi.continuousMul
#align pi.has_continuous_add Pi.continuousAdd
-/

#print Pi.continuousMul' /-
/-- A version of `pi.has_continuous_mul` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_mul` for non-dependent functions. -/
@[to_additive
      "A version of `pi.has_continuous_add` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_add` for non-dependent functions."]
instance Pi.continuousMul' : ContinuousMul (ι → M) :=
  Pi.continuousMul
#align pi.has_continuous_mul' Pi.continuousMul'
#align pi.has_continuous_add' Pi.continuousAdd'
-/

#print continuousMul_of_discreteTopology /-
@[to_additive]
instance (priority := 100) continuousMul_of_discreteTopology [TopologicalSpace N] [Mul N]
    [DiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_discreteTopology⟩
#align has_continuous_mul_of_discrete_topology continuousMul_of_discreteTopology
#align has_continuous_add_of_discrete_topology continuousAdd_of_discreteTopology
-/

open Filter

open Function

/- warning: has_continuous_mul.of_nhds_one -> ContinuousMul.of_nhds_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : Monoid.{u1} M] [_inst_6 : TopologicalSpace.{u1} M], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} M M) M (Function.uncurry.{u1, u1, u1} M M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))))) (Filter.prod.{u1, u1} M M (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5)))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))))))) -> (forall (x₀ : M), Eq.{succ u1} (Filter.{u1} M) (nhds.{u1} M _inst_6 x₀) (Filter.map.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))) x₀ x) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5)))))))) -> (forall (x₀ : M), Eq.{succ u1} (Filter.{u1} M) (nhds.{u1} M _inst_6 x₀) (Filter.map.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))) x x₀) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5)))))))) -> (ContinuousMul.{u1} M _inst_6 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : Monoid.{u1} M] [_inst_6 : TopologicalSpace.{u1} M], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} M M) M (Function.uncurry.{u1, u1, u1} M M M (fun (x._@.Mathlib.Topology.Algebra.Monoid._hyg.2116 : M) (x._@.Mathlib.Topology.Algebra.Monoid._hyg.2118 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))) x._@.Mathlib.Topology.Algebra.Monoid._hyg.2116 x._@.Mathlib.Topology.Algebra.Monoid._hyg.2118)) (Filter.prod.{u1, u1} M M (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_5)))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_5))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_5))))) -> (forall (x₀ : M), Eq.{succ u1} (Filter.{u1} M) (nhds.{u1} M _inst_6 x₀) (Filter.map.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))) x₀ x) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_5)))))) -> (forall (x₀ : M), Eq.{succ u1} (Filter.{u1} M) (nhds.{u1} M _inst_6 x₀) (Filter.map.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5))) x x₀) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_5)))))) -> (ContinuousMul.{u1} M _inst_6 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_5)))
Case conversion may be inaccurate. Consider using '#align has_continuous_mul.of_nhds_one ContinuousMul.of_nhds_oneₓ'. -/
@[to_additive]
theorem ContinuousMul.of_nhds_one {M : Type u} [Monoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) <| 𝓝 1)
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : ContinuousMul M :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key :
      (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) :=
      by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x :=
      by
      ext x
      simp
    calc
      map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ᶠ 𝓝 y₀) := by
        rw [nhds_prod_eq]
      _ = map (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ᶠ 𝓝 1) := by
        rw [uncurry, hleft x₀, hright y₀, prod_map_map_eq, Filter.map_map]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1)) := by
        rw [key, ← Filter.map_map]
      _ ≤ map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) := (map_mono hmul)
      _ = 𝓝 (x₀ * y₀) := by rw [← Filter.map_map, ← hright, hleft y₀, Filter.map_map, key₂, ← hleft]
      ⟩
#align has_continuous_mul.of_nhds_one ContinuousMul.of_nhds_one
#align has_continuous_add.of_nhds_zero ContinuousAdd.of_nhds_zero

/- warning: has_continuous_mul_of_comm_of_nhds_one -> continuousMul_of_comm_of_nhds_one is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_5 : CommMonoid.{u1} M] [_inst_6 : TopologicalSpace.{u1} M], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} M M) M (Function.uncurry.{u1, u1, u1} M M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))))) (Filter.prod.{u1, u1} M M (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5))))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))))))) -> (forall (x₀ : M), Eq.{succ u1} (Filter.{u1} M) (nhds.{u1} M _inst_6 x₀) (Filter.map.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))) x₀ x) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5))))))))) -> (ContinuousMul.{u1} M _inst_6 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_5 : CommMonoid.{u1} M] [_inst_6 : TopologicalSpace.{u1} M], (Filter.Tendsto.{u1, u1} (Prod.{u1, u1} M M) M (Function.uncurry.{u1, u1, u1} M M M (fun (x._@.Mathlib.Topology.Algebra.Monoid._hyg.2836 : M) (x._@.Mathlib.Topology.Algebra.Monoid._hyg.2838 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))) x._@.Mathlib.Topology.Algebra.Monoid._hyg.2836 x._@.Mathlib.Topology.Algebra.Monoid._hyg.2838)) (Filter.prod.{u1, u1} M M (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))))) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))))) -> (forall (x₀ : M), Eq.{succ u1} (Filter.{u1} M) (nhds.{u1} M _inst_6 x₀) (Filter.map.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5)))) x₀ x) (nhds.{u1} M _inst_6 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5))))))) -> (ContinuousMul.{u1} M _inst_6 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_5))))
Case conversion may be inaccurate. Consider using '#align has_continuous_mul_of_comm_of_nhds_one continuousMul_of_comm_of_nhds_oneₓ'. -/
@[to_additive]
theorem continuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : ContinuousMul M :=
  by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]
#align has_continuous_mul_of_comm_of_nhds_one continuousMul_of_comm_of_nhds_one
#align has_continuous_add_of_comm_of_nhds_zero continuousAdd_of_comm_of_nhds_zero

end ContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type _) [TopologicalSpace M₂] [T2Space M₂]

/- warning: is_closed_set_of_map_one -> isClosed_setOf_map_one is a dubious translation:
lean 3 declaration is
  forall (M₁ : Type.{u1}) (M₂ : Type.{u2}) [_inst_2 : TopologicalSpace.{u2} M₂] [_inst_3 : T2Space.{u2} M₂ _inst_2] [_inst_4 : One.{u1} M₁] [_inst_5 : One.{u2} M₂], IsClosed.{max u1 u2} (M₁ -> M₂) (Pi.topologicalSpace.{u1, u2} M₁ (fun (ᾰ : M₁) => M₂) (fun (a : M₁) => _inst_2)) (setOf.{max u1 u2} (M₁ -> M₂) (fun (f : M₁ -> M₂) => Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_4)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_5)))))
but is expected to have type
  forall (M₁ : Type.{u2}) (M₂ : Type.{u1}) [_inst_2 : TopologicalSpace.{u1} M₂] [_inst_3 : T2Space.{u1} M₂ _inst_2] [_inst_4 : One.{u2} M₁] [_inst_5 : One.{u1} M₂], IsClosed.{max u2 u1} (M₁ -> M₂) (Pi.topologicalSpace.{u2, u1} M₁ (fun (ᾰ : M₁) => M₂) (fun (a : M₁) => _inst_2)) (setOf.{max u2 u1} (M₁ -> M₂) (fun (f : M₁ -> M₂) => Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (One.toOfNat1.{u2} M₁ _inst_4))) (OfNat.ofNat.{u1} M₂ 1 (One.toOfNat1.{u1} M₂ _inst_5))))
Case conversion may be inaccurate. Consider using '#align is_closed_set_of_map_one isClosed_setOf_map_oneₓ'. -/
@[to_additive]
theorem isClosed_setOf_map_one [One M₁] [One M₂] : IsClosed { f : M₁ → M₂ | f 1 = 1 } :=
  isClosed_eq (continuous_apply 1) continuous_const
#align is_closed_set_of_map_one isClosed_setOf_map_one
#align is_closed_set_of_map_zero isClosed_setOf_map_zero

/- warning: is_closed_set_of_map_mul -> isClosed_setOf_map_mul is a dubious translation:
lean 3 declaration is
  forall (M₁ : Type.{u1}) (M₂ : Type.{u2}) [_inst_2 : TopologicalSpace.{u2} M₂] [_inst_3 : T2Space.{u2} M₂ _inst_2] [_inst_4 : Mul.{u1} M₁] [_inst_5 : Mul.{u2} M₂] [_inst_6 : ContinuousMul.{u2} M₂ _inst_2 _inst_5], IsClosed.{max u1 u2} (M₁ -> M₂) (Pi.topologicalSpace.{u1, u2} M₁ (fun (ᾰ : M₁) => M₂) (fun (a : M₁) => _inst_2)) (setOf.{max u1 u2} (M₁ -> M₂) (fun (f : M₁ -> M₂) => forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_4) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_5) (f x) (f y))))
but is expected to have type
  forall (M₁ : Type.{u2}) (M₂ : Type.{u1}) [_inst_2 : TopologicalSpace.{u1} M₂] [_inst_3 : T2Space.{u1} M₂ _inst_2] [_inst_4 : Mul.{u2} M₁] [_inst_5 : Mul.{u1} M₂] [_inst_6 : ContinuousMul.{u1} M₂ _inst_2 _inst_5], IsClosed.{max u2 u1} (M₁ -> M₂) (Pi.topologicalSpace.{u2, u1} M₁ (fun (ᾰ : M₁) => M₂) (fun (a : M₁) => _inst_2)) (setOf.{max u2 u1} (M₁ -> M₂) (fun (f : M₁ -> M₂) => forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HMul.hMul.{u2, u2, u2} M₁ M₁ M₁ (instHMul.{u2} M₁ _inst_4) x y)) (HMul.hMul.{u1, u1, u1} M₂ M₂ M₂ (instHMul.{u1} M₂ _inst_5) (f x) (f y))))
Case conversion may be inaccurate. Consider using '#align is_closed_set_of_map_mul isClosed_setOf_map_mulₓ'. -/
@[to_additive]
theorem isClosed_setOf_map_mul [Mul M₁] [Mul M₂] [ContinuousMul M₂] :
    IsClosed { f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y } :=
  by
  simp only [set_of_forall]
  exact
    isClosed_interᵢ fun x =>
      isClosed_interᵢ fun y =>
        isClosed_eq (continuous_apply _) ((continuous_apply _).mul (continuous_apply _))
#align is_closed_set_of_map_mul isClosed_setOf_map_mul
#align is_closed_set_of_map_add isClosed_setOf_map_add

variable {M₁ M₂} [MulOneClass M₁] [MulOneClass M₂] [ContinuousMul M₂] {F : Type _}
  [MonoidHomClass F M₁ M₂] {l : Filter α}

/- warning: monoid_hom_of_mem_closure_range_coe -> monoidHomOfMemClosureRangeCoe is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} M₂] [_inst_3 : T2Space.{u2} M₂ _inst_2] [_inst_4 : MulOneClass.{u1} M₁] [_inst_5 : MulOneClass.{u2} M₂] [_inst_6 : ContinuousMul.{u2} M₂ _inst_2 (MulOneClass.toHasMul.{u2} M₂ _inst_5)] {F : Type.{u3}} [_inst_7 : MonoidHomClass.{u3, u1, u2} F M₁ M₂ _inst_4 _inst_5] (f : M₁ -> M₂), (Membership.Mem.{max u1 u2, max u1 u2} (M₁ -> M₂) (Set.{max u1 u2} (M₁ -> M₂)) (Set.hasMem.{max u1 u2} (M₁ -> M₂)) f (closure.{max u1 u2} (M₁ -> M₂) (Pi.topologicalSpace.{u1, u2} M₁ (fun (x : M₁) => M₂) (fun (a : M₁) => _inst_2)) (Set.range.{max u1 u2, succ u3} (M₁ -> M₂) F (fun (f : F) (x : M₁) => coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M₁ -> M₂) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M₁ (fun (_x : M₁) => M₂) (MulHomClass.toFunLike.{u3, u1, u2} F M₁ M₂ (MulOneClass.toHasMul.{u1} M₁ _inst_4) (MulOneClass.toHasMul.{u2} M₂ _inst_5) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M₁ M₂ _inst_4 _inst_5 _inst_7))) f x)))) -> (MonoidHom.{u1, u2} M₁ M₂ _inst_4 _inst_5)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} M₂] [_inst_3 : T2Space.{u2} M₂ _inst_2] [_inst_4 : MulOneClass.{u1} M₁] [_inst_5 : MulOneClass.{u2} M₂] [_inst_6 : ContinuousMul.{u2} M₂ _inst_2 (MulOneClass.toMul.{u2} M₂ _inst_5)] {F : Type.{u3}} [_inst_7 : MonoidHomClass.{u3, u1, u2} F M₁ M₂ _inst_4 _inst_5] (f : M₁ -> M₂), (Membership.mem.{max u1 u2, max u1 u2} (M₁ -> M₂) (Set.{max u1 u2} (forall (x : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x)) (Set.instMembershipSet.{max u1 u2} (forall (x : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x)) f (closure.{max u1 u2} (forall (x : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x) (Pi.topologicalSpace.{u1, u2} M₁ (fun (x : M₁) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x) (fun (a : M₁) => _inst_2)) (Set.range.{max u1 u2, succ u3} (forall (x : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x) F (fun (f : F) (x : M₁) => FunLike.coe.{succ u3, succ u1, succ u2} F M₁ (fun (_x : M₁) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) _x) (MulHomClass.toFunLike.{u3, u1, u2} F M₁ M₂ (MulOneClass.toMul.{u1} M₁ _inst_4) (MulOneClass.toMul.{u2} M₂ _inst_5) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M₁ M₂ _inst_4 _inst_5 _inst_7)) f x)))) -> (MonoidHom.{u1, u2} M₁ M₂ _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align monoid_hom_of_mem_closure_range_coe monoidHomOfMemClosureRangeCoeₓ'. -/
/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `monoid_hom_class` instance) to `M₁ → M₂`. -/
@[to_additive
      "Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`\nand a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another\ntype of bundled homomorphisms that has a `add_monoid_hom_class` instance) to `M₁ → M₂`.",
  simps (config := { fullyApplied := false })]
def monoidHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →* M₂
    where
  toFun := f
  map_one' := (isClosed_setOf_map_one M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOf_map_mul M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_mul) hf
#align monoid_hom_of_mem_closure_range_coe monoidHomOfMemClosureRangeCoe
#align add_monoid_hom_of_mem_closure_range_coe addMonoidHomOfMemClosureRangeCoe

/- warning: monoid_hom_of_tendsto -> monoidHomOfTendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M₁ : Type.{u2}} {M₂ : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} M₂] [_inst_3 : T2Space.{u3} M₂ _inst_2] [_inst_4 : MulOneClass.{u2} M₁] [_inst_5 : MulOneClass.{u3} M₂] [_inst_6 : ContinuousMul.{u3} M₂ _inst_2 (MulOneClass.toHasMul.{u3} M₂ _inst_5)] {F : Type.{u4}} [_inst_7 : MonoidHomClass.{u4, u2, u3} F M₁ M₂ _inst_4 _inst_5] {l : Filter.{u1} α} (f : M₁ -> M₂) (g : α -> F) [_inst_8 : Filter.NeBot.{u1} α l], (Filter.Tendsto.{u1, max u2 u3} α (M₁ -> M₂) (fun (a : α) (x : M₁) => coeFn.{succ u4, max (succ u2) (succ u3)} F (fun (_x : F) => M₁ -> M₂) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} F M₁ (fun (_x : M₁) => M₂) (MulHomClass.toFunLike.{u4, u2, u3} F M₁ M₂ (MulOneClass.toHasMul.{u2} M₁ _inst_4) (MulOneClass.toHasMul.{u3} M₂ _inst_5) (MonoidHomClass.toMulHomClass.{u4, u2, u3} F M₁ M₂ _inst_4 _inst_5 _inst_7))) (g a) x) l (nhds.{max u2 u3} (M₁ -> M₂) (Pi.topologicalSpace.{u2, u3} M₁ (fun (x : M₁) => M₂) (fun (a : M₁) => _inst_2)) f)) -> (MonoidHom.{u2, u3} M₁ M₂ _inst_4 _inst_5)
but is expected to have type
  forall {α : Type.{u1}} {M₁ : Type.{u2}} {M₂ : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} M₂] [_inst_3 : T2Space.{u3} M₂ _inst_2] [_inst_4 : MulOneClass.{u2} M₁] [_inst_5 : MulOneClass.{u3} M₂] [_inst_6 : ContinuousMul.{u3} M₂ _inst_2 (MulOneClass.toMul.{u3} M₂ _inst_5)] {F : Type.{u4}} [_inst_7 : MonoidHomClass.{u4, u2, u3} F M₁ M₂ _inst_4 _inst_5] {l : Filter.{u1} α} (f : M₁ -> M₂) (g : α -> F) [_inst_8 : Filter.NeBot.{u1} α l], (Filter.Tendsto.{u1, max u2 u3} α (forall (x : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x) (fun (a : α) (x : M₁) => FunLike.coe.{succ u4, succ u2, succ u3} F M₁ (fun (_x : M₁) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) _x) (MulHomClass.toFunLike.{u4, u2, u3} F M₁ M₂ (MulOneClass.toMul.{u2} M₁ _inst_4) (MulOneClass.toMul.{u3} M₂ _inst_5) (MonoidHomClass.toMulHomClass.{u4, u2, u3} F M₁ M₂ _inst_4 _inst_5 _inst_7)) (g a) x) l (nhds.{max u2 u3} (forall (x : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x) (Pi.topologicalSpace.{u2, u3} M₁ (fun (x : M₁) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) x) (fun (a : M₁) => _inst_2)) f)) -> (MonoidHom.{u2, u3} M₁ M₂ _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align monoid_hom_of_tendsto monoidHomOfTendstoₓ'. -/
/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive
      "Construct a bundled additive monoid homomorphism from a pointwise limit of additive\nmonoid homomorphisms",
  simps (config := { fullyApplied := false })]
def monoidHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.ne_bot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →* M₂ :=
  monoidHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| eventually_of_forall fun a => mem_range_self _
#align monoid_hom_of_tendsto monoidHomOfTendsto
#align add_monoid_hom_of_tendsto addMonoidHomOfTendsto

variable (M₁ M₂)

/- warning: monoid_hom.is_closed_range_coe -> MonoidHom.isClosed_range_coe is a dubious translation:
lean 3 declaration is
  forall (M₁ : Type.{u1}) (M₂ : Type.{u2}) [_inst_2 : TopologicalSpace.{u2} M₂] [_inst_3 : T2Space.{u2} M₂ _inst_2] [_inst_4 : MulOneClass.{u1} M₁] [_inst_5 : MulOneClass.{u2} M₂] [_inst_6 : ContinuousMul.{u2} M₂ _inst_2 (MulOneClass.toHasMul.{u2} M₂ _inst_5)], IsClosed.{max u1 u2} (M₁ -> M₂) (Pi.topologicalSpace.{u1, u2} M₁ (fun (ᾰ : M₁) => M₂) (fun (a : M₁) => _inst_2)) (Set.range.{max u1 u2, max (succ u2) (succ u1)} (M₁ -> M₂) (MonoidHom.{u1, u2} M₁ M₂ _inst_4 _inst_5) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M₁ M₂ _inst_4 _inst_5) (fun (ᾰ : MonoidHom.{u1, u2} M₁ M₂ _inst_4 _inst_5) => M₁ -> M₂) (MonoidHom.hasCoeToFun.{u1, u2} M₁ M₂ _inst_4 _inst_5)))
but is expected to have type
  forall (M₁ : Type.{u2}) (M₂ : Type.{u1}) [_inst_2 : TopologicalSpace.{u1} M₂] [_inst_3 : T2Space.{u1} M₂ _inst_2] [_inst_4 : MulOneClass.{u2} M₁] [_inst_5 : MulOneClass.{u1} M₂] [_inst_6 : ContinuousMul.{u1} M₂ _inst_2 (MulOneClass.toMul.{u1} M₂ _inst_5)], IsClosed.{max u2 u1} (forall (ᾰ : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) ᾰ) (Pi.topologicalSpace.{u2, u1} M₁ (fun (ᾰ : M₁) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) ᾰ) (fun (a : M₁) => _inst_2)) (Set.range.{max u2 u1, max (succ u2) (succ u1)} (forall (ᾰ : M₁), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) ᾰ) (MonoidHom.{u2, u1} M₁ M₂ _inst_4 _inst_5) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M₁ M₂ _inst_4 _inst_5) M₁ (fun (ᾰ : M₁) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M₁) => M₂) ᾰ) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M₁ M₂ _inst_4 _inst_5) M₁ M₂ (MulOneClass.toMul.{u2} M₁ _inst_4) (MulOneClass.toMul.{u1} M₂ _inst_5) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M₁ M₂ _inst_4 _inst_5) M₁ M₂ _inst_4 _inst_5 (MonoidHom.monoidHomClass.{u2, u1} M₁ M₂ _inst_4 _inst_5)))))
Case conversion may be inaccurate. Consider using '#align monoid_hom.is_closed_range_coe MonoidHom.isClosed_range_coeₓ'. -/
@[to_additive]
theorem MonoidHom.isClosed_range_coe : IsClosed (range (coeFn : (M₁ →* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩
#align monoid_hom.is_closed_range_coe MonoidHom.isClosed_range_coe
#align add_monoid_hom.is_closed_range_coe AddMonoidHom.isClosed_range_coe

end PointwiseLimits

/- warning: inducing.has_continuous_mul -> Inducing.continuousMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_2 : Mul.{u1} M] [_inst_3 : Mul.{u2} N] [_inst_4 : MulHomClass.{u3, u1, u2} F M N _inst_2 _inst_3] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : TopologicalSpace.{u2} N] [_inst_7 : ContinuousMul.{u2} N _inst_6 _inst_3] (f : F), (Inducing.{u1, u2} M N _inst_5 _inst_6 (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N _inst_2 _inst_3 _inst_4)) f)) -> (ContinuousMul.{u1} M _inst_5 _inst_2)
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {F : Type.{u1}} [_inst_2 : Mul.{u3} M] [_inst_3 : Mul.{u2} N] [_inst_4 : MulHomClass.{u1, u3, u2} F M N _inst_2 _inst_3] [_inst_5 : TopologicalSpace.{u3} M] [_inst_6 : TopologicalSpace.{u2} N] [_inst_7 : ContinuousMul.{u2} N _inst_6 _inst_3] (f : F), (Inducing.{u3, u2} M N _inst_5 _inst_6 (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N _inst_2 _inst_3 _inst_4) f)) -> (ContinuousMul.{u3} M _inst_5 _inst_2)
Case conversion may be inaccurate. Consider using '#align inducing.has_continuous_mul Inducing.continuousMulₓ'. -/
@[to_additive]
theorem Inducing.continuousMul {M N F : Type _} [Mul M] [Mul N] [MulHomClass F M N]
    [TopologicalSpace M] [TopologicalSpace N] [ContinuousMul N] (f : F) (hf : Inducing f) :
    ContinuousMul M :=
  ⟨hf.continuous_iff.2 <| by
      simpa only [(· ∘ ·), map_mul f] using hf.continuous.fst'.mul hf.continuous.snd'⟩
#align inducing.has_continuous_mul Inducing.continuousMul
#align inducing.has_continuous_add Inducing.continuousAdd

/- warning: has_continuous_mul_induced -> continuousMul_induced is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {F : Type.{u3}} [_inst_2 : Mul.{u1} M] [_inst_3 : Mul.{u2} N] [_inst_4 : MulHomClass.{u3, u1, u2} F M N _inst_2 _inst_3] [_inst_5 : TopologicalSpace.{u2} N] [_inst_6 : ContinuousMul.{u2} N _inst_5 _inst_3] (f : F), ContinuousMul.{u1} M (TopologicalSpace.induced.{u1, u2} M N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N _inst_2 _inst_3 _inst_4)) f) _inst_5) _inst_2
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {F : Type.{u1}} [_inst_2 : Mul.{u3} M] [_inst_3 : Mul.{u2} N] [_inst_4 : MulHomClass.{u1, u3, u2} F M N _inst_2 _inst_3] [_inst_5 : TopologicalSpace.{u2} N] [_inst_6 : ContinuousMul.{u2} N _inst_5 _inst_3] (f : F), ContinuousMul.{u3} M (TopologicalSpace.induced.{u3, u2} M N (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u1, u3, u2} F M N _inst_2 _inst_3 _inst_4) f) _inst_5) _inst_2
Case conversion may be inaccurate. Consider using '#align has_continuous_mul_induced continuousMul_inducedₓ'. -/
@[to_additive]
theorem continuousMul_induced {M N F : Type _} [Mul M] [Mul N] [MulHomClass F M N]
    [TopologicalSpace N] [ContinuousMul N] (f : F) : @ContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Inducing.continuousMul f ⟨rfl⟩
#align has_continuous_mul_induced continuousMul_induced
#align has_continuous_add_induced continuousAdd_induced

/- warning: subsemigroup.has_continuous_mul -> Subsemigroup.continuousMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Semigroup.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (Semigroup.toHasMul.{u1} M _inst_3)] (S : Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)), ContinuousMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_3))) S) (Subtype.topologicalSpace.{u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) (SetLike.hasMem.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) M (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_3))) x S) _inst_2) (MulMemClass.mul.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) (Semigroup.toHasMul.{u1} M _inst_3) (Subsemigroup.setLike.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) (Subsemigroup.mulMemClass.{u1} M (Semigroup.toHasMul.{u1} M _inst_3)) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Semigroup.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (Semigroup.toMul.{u1} M _inst_3)] (S : Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)), ContinuousMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3))) x S)) (instTopologicalSpaceSubtype.{u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3))) x S) _inst_2) (Semigroup.toMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) M (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3))) x S)) (MulMemClass.toSemigroup.{u1, u1} M _inst_3 (Subsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) (Subsemigroup.instSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) (Subsemigroup.instMulMemClassSubsemigroupInstSetLikeSubsemigroup.{u1} M (Semigroup.toMul.{u1} M _inst_3)) S))
Case conversion may be inaccurate. Consider using '#align subsemigroup.has_continuous_mul Subsemigroup.continuousMulₓ'. -/
@[to_additive]
instance Subsemigroup.continuousMul [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
    (S : Subsemigroup M) : ContinuousMul S :=
  Inducing.continuousMul (⟨coe, fun _ _ => rfl⟩ : MulHom S M) ⟨rfl⟩
#align subsemigroup.has_continuous_mul Subsemigroup.continuousMul
#align add_subsemigroup.has_continuous_add AddSubsemigroup.continuousAdd

/- warning: submonoid.has_continuous_mul -> Submonoid.continuousMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), ContinuousMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) S) (Subtype.topologicalSpace.{u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x S) _inst_2) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), ContinuousMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x S)) (instTopologicalSpaceSubtype.{u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x S) _inst_2) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) S)
Case conversion may be inaccurate. Consider using '#align submonoid.has_continuous_mul Submonoid.continuousMulₓ'. -/
@[to_additive]
instance Submonoid.continuousMul [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    (S : Submonoid M) : ContinuousMul S :=
  S.toSubsemigroup.ContinuousMul
#align submonoid.has_continuous_mul Submonoid.continuousMul
#align add_submonoid.has_continuous_add AddSubmonoid.continuousAdd

section ContinuousMul

variable [TopologicalSpace M] [Monoid M] [ContinuousMul M]

/- warning: submonoid.top_closure_mul_self_subset -> Submonoid.top_closure_mul_self_subset is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) (closure.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s)) (closure.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s))) (closure.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) (closure.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) s)) (closure.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) s))) (closure.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) s))
Case conversion may be inaccurate. Consider using '#align submonoid.top_closure_mul_self_subset Submonoid.top_closure_mul_self_subsetₓ'. -/
@[to_additive]
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    closure (s : Set M) * closure s ⊆ closure s :=
  image2_subset_iff.2 fun x hx y hy =>
    map_mem_closure₂ continuous_mul hx hy fun a ha b hb => s.mul_mem ha hb
#align submonoid.top_closure_mul_self_subset Submonoid.top_closure_mul_self_subset
#align add_submonoid.top_closure_add_self_subset AddSubmonoid.top_closure_add_self_subset

/- warning: submonoid.top_closure_mul_self_eq -> Submonoid.top_closure_mul_self_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), Eq.{succ u1} (Set.{u1} M) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) (closure.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s)) (closure.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s))) (closure.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), Eq.{succ u1} (Set.{u1} M) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) (closure.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) s)) (closure.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) s))) (closure.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) s))
Case conversion may be inaccurate. Consider using '#align submonoid.top_closure_mul_self_eq Submonoid.top_closure_mul_self_eqₓ'. -/
@[to_additive]
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    closure (s : Set M) * closure s = closure s :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, 1, hx, subset_closure s.one_mem, mul_one _⟩
#align submonoid.top_closure_mul_self_eq Submonoid.top_closure_mul_self_eq
#align add_submonoid.top_closure_add_self_eq AddSubmonoid.top_closure_add_self_eq

/- warning: submonoid.topological_closure -> Submonoid.topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))], (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) -> (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))], (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) -> (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))
Case conversion may be inaccurate. Consider using '#align submonoid.topological_closure Submonoid.topologicalClosureₓ'. -/
/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
@[to_additive
      "The (topological-space) closure of an additive submonoid of a space `M` with\n`has_continuous_add` is itself an additive submonoid."]
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M
    where
  carrier := closure (s : Set M)
  one_mem' := subset_closure s.one_mem
  mul_mem' a b ha hb := s.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩
#align submonoid.topological_closure Submonoid.topologicalClosure
#align add_submonoid.topological_closure AddSubmonoid.topologicalClosure

/- warning: submonoid.le_topological_closure -> Submonoid.le_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.instCompleteLatticeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) s (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s)
Case conversion may be inaccurate. Consider using '#align submonoid.le_topological_closure Submonoid.le_topologicalClosureₓ'. -/
@[to_additive]
theorem Submonoid.le_topologicalClosure (s : Submonoid M) : s ≤ s.topologicalClosure :=
  subset_closure
#align submonoid.le_topological_closure Submonoid.le_topologicalClosure
#align add_submonoid.le_topological_closure AddSubmonoid.le_topologicalClosure

/- warning: submonoid.is_closed_topological_closure -> Submonoid.isClosed_topologicalClosure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), IsClosed.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), IsClosed.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s))
Case conversion may be inaccurate. Consider using '#align submonoid.is_closed_topological_closure Submonoid.isClosed_topologicalClosureₓ'. -/
@[to_additive]
theorem Submonoid.isClosed_topologicalClosure (s : Submonoid M) :
    IsClosed (s.topologicalClosure : Set M) := by convert isClosed_closure
#align submonoid.is_closed_topological_closure Submonoid.isClosed_topologicalClosure
#align add_submonoid.is_closed_topological_closure AddSubmonoid.isClosed_topologicalClosure

/- warning: submonoid.topological_closure_minimal -> Submonoid.topologicalClosure_minimal is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) {t : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)}, (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) s t) -> (IsClosed.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) t)) -> (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s) t)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) {t : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)}, (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.instCompleteLatticeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) s t) -> (IsClosed.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) t)) -> (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.instCompleteLatticeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s) t)
Case conversion may be inaccurate. Consider using '#align submonoid.topological_closure_minimal Submonoid.topologicalClosure_minimalₓ'. -/
@[to_additive]
theorem Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align submonoid.topological_closure_minimal Submonoid.topologicalClosure_minimal
#align add_submonoid.topological_closure_minimal AddSubmonoid.topologicalClosure_minimal

/- warning: submonoid.comm_monoid_topological_closure -> Submonoid.commMonoidTopologicalClosure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] [_inst_5 : T2Space.{u1} M _inst_2] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), (forall (x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s)) x y) (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s)) y x)) -> (CommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] [_inst_5 : T2Space.{u1} M _inst_2] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), (forall (x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (y : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s)) x y) (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s)) y x)) -> (CommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x (Submonoid.topologicalClosure.{u1} M _inst_2 _inst_3 _inst_4 s))))
Case conversion may be inaccurate. Consider using '#align submonoid.comm_monoid_topological_closure Submonoid.commMonoidTopologicalClosureₓ'. -/
/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive
      "If a submonoid of an additive topological monoid is commutative, then so is its\ntopological closure."]
def Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M)
    (hs : ∀ x y : s, x * y = y * x) : CommMonoid s.topologicalClosure :=
  { s.topologicalClosure.toMonoid with
    mul_comm :=
      have : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      Subtype.ext <|
        eqOn_closure₂ this continuous_mul (continuous_snd.mul continuous_fst) x hx y hy }
#align submonoid.comm_monoid_topological_closure Submonoid.commMonoidTopologicalClosure
#align add_submonoid.add_comm_monoid_topological_closure AddSubmonoid.addCommMonoidTopologicalClosure

/- warning: exists_open_nhds_one_split -> exists_open_nhds_one_split is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M}, (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) s (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => And (IsOpen.{u1} M _inst_2 V) (And (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) V) (forall (v : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) v V) -> (forall (w : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) w V) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) v w) s))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M}, (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) s (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => And (IsOpen.{u1} M _inst_2 V) (And (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))) V) (forall (v : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) v V) -> (forall (w : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) w V) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) v w) s))))))
Case conversion may be inaccurate. Consider using '#align exists_open_nhds_one_split exists_open_nhds_one_splitₓ'. -/
@[to_additive exists_open_nhds_zero_half]
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s :=
  by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s ∈ 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using hs)
  simpa only [prod_subset_iff] using exists_nhds_square this
#align exists_open_nhds_one_split exists_open_nhds_one_split
#align exists_open_nhds_zero_half exists_open_nhds_zero_half

/- warning: exists_nhds_one_split -> exists_nhds_one_split is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M}, (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) s (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) V (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) V (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) => forall (v : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) v V) -> (forall (w : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) w V) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) v w) s)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M}, (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) s (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => And (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) V (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))))) (forall (v : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) v V) -> (forall (w : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) w V) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) v w) s)))))
Case conversion may be inaccurate. Consider using '#align exists_nhds_one_split exists_nhds_one_splitₓ'. -/
@[to_additive exists_nhds_zero_half]
theorem exists_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩
#align exists_nhds_one_split exists_nhds_one_split
#align exists_nhds_zero_half exists_nhds_zero_half

/- warning: exists_nhds_one_split4 -> exists_nhds_one_split4 is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {u : Set.{u1} M}, (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) u (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) V (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) V (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) => forall {v : M} {w : M} {s : M} {t : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) v V) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) w V) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) s V) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) t V) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) v w) s) t) u))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {u : Set.{u1} M}, (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) u (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => And (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) V (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))))) (forall {v : M} {w : M} {s : M} {t : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) v V) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) w V) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) s V) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) t V) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) v w) s) t) u))))
Case conversion may be inaccurate. Consider using '#align exists_nhds_one_split4 exists_nhds_one_split4ₓ'. -/
@[to_additive exists_nhds_zero_quarter]
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
  by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
#align exists_nhds_one_split4 exists_nhds_one_split4
#align exists_nhds_zero_quarter exists_nhds_zero_quarter

/- warning: exists_open_nhds_one_mul_subset -> exists_open_nhds_one_mul_subset is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {U : Set.{u1} M}, (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) U (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => And (IsOpen.{u1} M _inst_2 V) (And (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))))) V) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) V V) U))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {U : Set.{u1} M}, (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) U (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))))) -> (Exists.{succ u1} (Set.{u1} M) (fun (V : Set.{u1} M) => And (IsOpen.{u1} M _inst_2 V) (And (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3))) V) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) V V) U))))
Case conversion may be inaccurate. Consider using '#align exists_open_nhds_one_mul_subset exists_open_nhds_one_mul_subsetₓ'. -/
/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[to_additive
      "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`\n  such that `V + V ⊆ U`."]
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ V * V ⊆ U :=
  by
  rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩
  use V, Vo, V1
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact hV _ hx _ hy
#align exists_open_nhds_one_mul_subset exists_open_nhds_one_mul_subset
#align exists_open_nhds_zero_add_subset exists_open_nhds_zero_add_subset

/- warning: is_compact.mul -> IsCompact.mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M} {t : Set.{u1} M}, (IsCompact.{u1} M _inst_2 s) -> (IsCompact.{u1} M _inst_2 t) -> (IsCompact.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) s t))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M} {t : Set.{u1} M}, (IsCompact.{u1} M _inst_2 s) -> (IsCompact.{u1} M _inst_2 t) -> (IsCompact.{u1} M _inst_2 (HMul.hMul.{u1, u1, u1} (Set.{u1} M) (Set.{u1} M) (Set.{u1} M) (instHMul.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) s t))
Case conversion may be inaccurate. Consider using '#align is_compact.mul IsCompact.mulₓ'. -/
@[to_additive]
theorem IsCompact.mul {s t : Set M} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) :=
  by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul
#align is_compact.mul IsCompact.mul
#align is_compact.add IsCompact.add

/- warning: tendsto_list_prod -> tendsto_list_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {M : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : Monoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3))] {f : ι -> α -> M} {x : Filter.{u2} α} {a : ι -> M} (l : List.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (Filter.Tendsto.{u2, u3} α M (f i) x (nhds.{u3} M _inst_2 (a i)))) -> (Filter.Tendsto.{u2, u3} α M (fun (b : α) => List.prod.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (List.map.{u1, u3} ι M (fun (c : ι) => f c b) l)) x (nhds.{u3} M _inst_2 (List.prod.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (List.map.{u1, u3} ι M a l))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : ι -> α -> M} {x : Filter.{u3} α} {a : ι -> M} (l : List.{u2} ι), (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i l) -> (Filter.Tendsto.{u3, u1} α M (f i) x (nhds.{u1} M _inst_2 (a i)))) -> (Filter.Tendsto.{u3, u1} α M (fun (b : α) => List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Monoid.toOne.{u1} M _inst_3) (List.map.{u2, u1} ι M (fun (c : ι) => f c b) l)) x (nhds.{u1} M _inst_2 (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Monoid.toOne.{u1} M _inst_3) (List.map.{u2, u1} ι M a l))))
Case conversion may be inaccurate. Consider using '#align tendsto_list_prod tendsto_list_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
    ∀ l : List ι,
      (∀ i ∈ l, Tendsto (f i) x (𝓝 (a i))) →
        Tendsto (fun b => (l.map fun c => f c b).Prod) x (𝓝 (l.map a).Prod)
  | [], _ => by simp [tendsto_const_nhds]
  | f::l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact
      (h f (List.mem_cons_self _ _)).mul
        (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_mem _ hc))
#align tendsto_list_prod tendsto_list_prod
#align tendsto_list_sum tendsto_list_sum

/- warning: continuous_list_prod -> continuous_list_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : Monoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3))] {f : ι -> X -> M} (l : List.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (f i))) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (fun (a : X) => List.prod.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (List.map.{u1, u3} ι M (fun (i : ι) => f i a) l)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : ι -> X -> M} (l : List.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (List.{u3} ι) (List.instMembershipList.{u3} ι) i l) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (f i))) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (fun (a : X) => List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Monoid.toOne.{u1} M _inst_3) (List.map.{u3, u1} ι M (fun (i : ι) => f i a) l)))
Case conversion may be inaccurate. Consider using '#align continuous_list_prod continuous_list_prodₓ'. -/
@[to_additive]
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i ∈ l, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).Prod :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x
#align continuous_list_prod continuous_list_prod
#align continuous_list_sum continuous_list_sum

/- warning: continuous_on_list_prod -> continuousOn_list_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : Monoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3))] {f : ι -> X -> M} (l : List.{u1} ι) {t : Set.{u2} X}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i l) -> (ContinuousOn.{u2, u3} X M _inst_1 _inst_2 (f i) t)) -> (ContinuousOn.{u2, u3} X M _inst_1 _inst_2 (fun (a : X) => List.prod.{u3} M (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M _inst_3)) (List.map.{u1, u3} ι M (fun (i : ι) => f i a) l)) t)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : ι -> X -> M} (l : List.{u3} ι) {t : Set.{u2} X}, (forall (i : ι), (Membership.mem.{u3, u3} ι (List.{u3} ι) (List.instMembershipList.{u3} ι) i l) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (f i) t)) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (fun (a : X) => List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Monoid.toOne.{u1} M _inst_3) (List.map.{u3, u1} ι M (fun (i : ι) => f i a) l)) t)
Case conversion may be inaccurate. Consider using '#align continuous_on_list_prod continuousOn_list_prodₓ'. -/
@[to_additive]
theorem continuousOn_list_prod {f : ι → X → M} (l : List ι) {t : Set X}
    (h : ∀ i ∈ l, ContinuousOn (f i) t) : ContinuousOn (fun a => (l.map fun i => f i a).Prod) t :=
  by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx]
  refine' tendsto_list_prod _ fun i hi => _
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx] at h
  exact h
#align continuous_on_list_prod continuousOn_list_prod
#align continuous_on_list_sum continuousOn_list_sum

/- warning: continuous_pow -> continuous_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (n : Nat), Continuous.{u1, u1} M M _inst_2 _inst_2 (fun (a : M) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) a n)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (n : Nat), Continuous.{u1, u1} M M _inst_2 _inst_2 (fun (a : M) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) a n)
Case conversion may be inaccurate. Consider using '#align continuous_pow continuous_powₓ'. -/
@[continuity, to_additive]
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
  | 0 => by simpa using continuous_const
  | k + 1 => by
    simp only [pow_succ]
    exact continuous_id.mul (continuous_pow _)
#align continuous_pow continuous_pow
#align continuous_nsmul continuous_nsmul

/- warning: add_monoid.has_continuous_const_smul_nat -> AddMonoid.continuousConstSMul_nat is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_5 : AddMonoid.{u1} A] [_inst_6 : TopologicalSpace.{u1} A] [_inst_7 : ContinuousAdd.{u1} A _inst_6 (AddZeroClass.toHasAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_5))], ContinuousConstSMul.{0, u1} Nat A _inst_6 (AddMonoid.SMul.{u1} A _inst_5)
but is expected to have type
  forall {A : Type.{u1}} [_inst_5 : AddMonoid.{u1} A] [_inst_6 : TopologicalSpace.{u1} A] [_inst_7 : ContinuousAdd.{u1} A _inst_6 (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_5))], ContinuousConstSMul.{0, u1} Nat A _inst_6 (AddMonoid.SMul.{u1} A _inst_5)
Case conversion may be inaccurate. Consider using '#align add_monoid.has_continuous_const_smul_nat AddMonoid.continuousConstSMul_natₓ'. -/
instance AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousConstSMul ℕ A :=
  ⟨continuous_nsmul⟩
#align add_monoid.has_continuous_const_smul_nat AddMonoid.continuousConstSMul_nat

/- warning: add_monoid.has_continuous_smul_nat -> AddMonoid.continuousSMul_nat is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_5 : AddMonoid.{u1} A] [_inst_6 : TopologicalSpace.{u1} A] [_inst_7 : ContinuousAdd.{u1} A _inst_6 (AddZeroClass.toHasAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_5))], ContinuousSMul.{0, u1} Nat A (AddMonoid.SMul.{u1} A _inst_5) Nat.topologicalSpace _inst_6
but is expected to have type
  forall {A : Type.{u1}} [_inst_5 : AddMonoid.{u1} A] [_inst_6 : TopologicalSpace.{u1} A] [_inst_7 : ContinuousAdd.{u1} A _inst_6 (AddZeroClass.toAdd.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_5))], ContinuousSMul.{0, u1} Nat A (AddMonoid.SMul.{u1} A _inst_5) instTopologicalSpaceNat _inst_6
Case conversion may be inaccurate. Consider using '#align add_monoid.has_continuous_smul_nat AddMonoid.continuousSMul_natₓ'. -/
instance AddMonoid.continuousSMul_nat {A} [AddMonoid A] [TopologicalSpace A] [ContinuousAdd A] :
    ContinuousSMul ℕ A :=
  ⟨continuous_uncurry_of_discreteTopology continuous_nsmul⟩
#align add_monoid.has_continuous_smul_nat AddMonoid.continuousSMul_nat

/- warning: continuous.pow -> Continuous.pow is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Monoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))] {f : X -> M}, (Continuous.{u1, u2} X M _inst_1 _inst_2 f) -> (forall (n : Nat), Continuous.{u1, u2} X M _inst_1 _inst_2 (fun (b : X) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_3)) (f b) n))
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : X -> M}, (Continuous.{u2, u1} X M _inst_1 _inst_2 f) -> (forall (n : Nat), Continuous.{u2, u1} X M _inst_1 _inst_2 (fun (b : X) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) (f b) n))
Case conversion may be inaccurate. Consider using '#align continuous.pow Continuous.powₓ'. -/
@[continuity, to_additive Continuous.nsmul]
theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n :=
  (continuous_pow n).comp h
#align continuous.pow Continuous.pow
#align continuous.nsmul Continuous.nsmul

/- warning: continuous_on_pow -> continuousOn_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M} (n : Nat), ContinuousOn.{u1, u1} M M _inst_2 _inst_2 (fun (x : M) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) x n) s
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {s : Set.{u1} M} (n : Nat), ContinuousOn.{u1, u1} M M _inst_2 _inst_2 (fun (x : M) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) x n) s
Case conversion may be inaccurate. Consider using '#align continuous_on_pow continuousOn_powₓ'. -/
@[to_additive]
theorem continuousOn_pow {s : Set M} (n : ℕ) : ContinuousOn (fun x => x ^ n) s :=
  (continuous_pow n).ContinuousOn
#align continuous_on_pow continuousOn_pow
#align continuous_on_nsmul continuousOn_nsmul

/- warning: continuous_at_pow -> continuousAt_pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (x : M) (n : Nat), ContinuousAt.{u1, u1} M M _inst_2 _inst_2 (fun (x : M) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) x n) x
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] (x : M) (n : Nat), ContinuousAt.{u1, u1} M M _inst_2 _inst_2 (fun (x : M) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) x n) x
Case conversion may be inaccurate. Consider using '#align continuous_at_pow continuousAt_powₓ'. -/
@[to_additive]
theorem continuousAt_pow (x : M) (n : ℕ) : ContinuousAt (fun x => x ^ n) x :=
  (continuous_pow n).ContinuousAt
#align continuous_at_pow continuousAt_pow
#align continuous_at_nsmul continuousAt_nsmul

/- warning: filter.tendsto.pow -> Filter.Tendsto.pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Monoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))] {l : Filter.{u1} α} {f : α -> M} {x : M}, (Filter.Tendsto.{u1, u2} α M f l (nhds.{u2} M _inst_2 x)) -> (forall (n : Nat), Filter.Tendsto.{u1, u2} α M (fun (x : α) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_3)) (f x) n) l (nhds.{u2} M _inst_2 (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_3)) x n)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {l : Filter.{u2} α} {f : α -> M} {x : M}, (Filter.Tendsto.{u2, u1} α M f l (nhds.{u1} M _inst_2 x)) -> (forall (n : Nat), Filter.Tendsto.{u2, u1} α M (fun (x : α) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) (f x) n) l (nhds.{u1} M _inst_2 (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) x n)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.pow Filter.Tendsto.powₓ'. -/
@[to_additive Filter.Tendsto.nsmul]
theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuousAt_pow _ _).Tendsto.comp hf
#align filter.tendsto.pow Filter.Tendsto.pow
#align filter.tendsto.nsmul Filter.Tendsto.nsmul

/- warning: continuous_within_at.pow -> ContinuousWithinAt.pow is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Monoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))] {f : X -> M} {x : X} {s : Set.{u1} X}, (ContinuousWithinAt.{u1, u2} X M _inst_1 _inst_2 f s x) -> (forall (n : Nat), ContinuousWithinAt.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_3)) (f x) n) s x)
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : X -> M} {x : X} {s : Set.{u2} X}, (ContinuousWithinAt.{u2, u1} X M _inst_1 _inst_2 f s x) -> (forall (n : Nat), ContinuousWithinAt.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) (f x) n) s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.pow ContinuousWithinAt.powₓ'. -/
@[to_additive ContinuousWithinAt.nsmul]
theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
    (n : ℕ) : ContinuousWithinAt (fun x => f x ^ n) s x :=
  hf.pow n
#align continuous_within_at.pow ContinuousWithinAt.pow
#align continuous_within_at.nsmul ContinuousWithinAt.nsmul

/- warning: continuous_at.pow -> ContinuousAt.pow is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Monoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))] {f : X -> M} {x : X}, (ContinuousAt.{u1, u2} X M _inst_1 _inst_2 f x) -> (forall (n : Nat), ContinuousAt.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_3)) (f x) n) x)
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : X -> M} {x : X}, (ContinuousAt.{u2, u1} X M _inst_1 _inst_2 f x) -> (forall (n : Nat), ContinuousAt.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) (f x) n) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.pow ContinuousAt.powₓ'. -/
@[to_additive ContinuousAt.nsmul]
theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) :
    ContinuousAt (fun x => f x ^ n) x :=
  hf.pow n
#align continuous_at.pow ContinuousAt.pow
#align continuous_at.nsmul ContinuousAt.nsmul

/- warning: continuous_on.pow -> ContinuousOn.pow is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Monoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_3))] {f : X -> M} {s : Set.{u1} X}, (ContinuousOn.{u1, u2} X M _inst_1 _inst_2 f s) -> (forall (n : Nat), ContinuousOn.{u1, u2} X M _inst_1 _inst_2 (fun (x : X) => HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M _inst_3)) (f x) n) s)
but is expected to have type
  forall {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {f : X -> M} {s : Set.{u2} X}, (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 f s) -> (forall (n : Nat), ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (fun (x : X) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) (f x) n) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.pow ContinuousOn.powₓ'. -/
@[to_additive ContinuousOn.nsmul]
theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun x => f x ^ n) s := fun x hx => (hf x hx).pow n
#align continuous_on.pow ContinuousOn.pow
#align continuous_on.nsmul ContinuousOn.nsmul

/- warning: filter.tendsto_cocompact_mul_left -> Filter.tendsto_cocompact_mul_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) b a) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) -> (Filter.Tendsto.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) a x) (Filter.cocompact.{u1} M _inst_2) (Filter.cocompact.{u1} M _inst_2))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) b a) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3)))) -> (Filter.Tendsto.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) a x) (Filter.cocompact.{u1} M _inst_2) (Filter.cocompact.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_cocompact_mul_left Filter.tendsto_cocompact_mul_leftₓ'. -/
/-- Left-multiplication by a left-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
    Filter.Tendsto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M) :=
  by
  refine' Filter.Tendsto.of_tendsto_comp _ (Filter.comap_cocompact_le (continuous_mul_left b))
  convert Filter.tendsto_id
  ext x
  simp [ha]
#align filter.tendsto_cocompact_mul_left Filter.tendsto_cocompact_mul_left

/- warning: filter.tendsto_cocompact_mul_right -> Filter.tendsto_cocompact_mul_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) a b) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) -> (Filter.Tendsto.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x a) (Filter.cocompact.{u1} M _inst_2) (Filter.cocompact.{u1} M _inst_2))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Monoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))] {a : M} {b : M}, (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) a b) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3)))) -> (Filter.Tendsto.{u1, u1} M M (fun (x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x a) (Filter.cocompact.{u1} M _inst_2) (Filter.cocompact.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align filter.tendsto_cocompact_mul_right Filter.tendsto_cocompact_mul_rightₓ'. -/
/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
    Filter.Tendsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M) :=
  by
  refine' Filter.Tendsto.of_tendsto_comp _ (Filter.comap_cocompact_le (continuous_mul_right b))
  convert Filter.tendsto_id
  ext x
  simp [ha]
#align filter.tendsto_cocompact_mul_right Filter.tendsto_cocompact_mul_right

/- warning: is_scalar_tower.has_continuous_const_smul -> IsScalarTower.continuousConstSMul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_5 : Monoid.{u2} A] [_inst_6 : SMul.{u1, u2} R A] [_inst_7 : IsScalarTower.{u1, u2, u2} R A A _inst_6 (Mul.toSMul.{u2} A (MulOneClass.toHasMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_5))) _inst_6] [_inst_8 : TopologicalSpace.{u2} A] [_inst_9 : ContinuousMul.{u2} A _inst_8 (MulOneClass.toHasMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_5))], ContinuousConstSMul.{u1, u2} R A _inst_8 _inst_6
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_5 : Monoid.{u2} A] [_inst_6 : SMul.{u1, u2} R A] [_inst_7 : IsScalarTower.{u1, u2, u2} R A A _inst_6 (MulAction.toSMul.{u2, u2} A A _inst_5 (Monoid.toMulAction.{u2} A _inst_5)) _inst_6] [_inst_8 : TopologicalSpace.{u2} A] [_inst_9 : ContinuousMul.{u2} A _inst_8 (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_5))], ContinuousConstSMul.{u1, u2} R A _inst_8 _inst_6
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.has_continuous_const_smul IsScalarTower.continuousConstSMulₓ'. -/
/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instances applies when `R = A`, or when `[algebra R A]` is available. -/
@[to_additive
      "If `R` acts on `A` via `A`, then continuous addition implies\ncontinuous affine addition by constants."]
instance (priority := 100) IsScalarTower.continuousConstSMul {R A : Type _} [Monoid A] [SMul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [ContinuousMul A] : ContinuousConstSMul R A
    where continuous_const_smul q :=
    by
    simp (config := { singlePass := true }) only [← smul_one_mul q (_ : A)]
    exact continuous_const.mul continuous_id
#align is_scalar_tower.has_continuous_const_smul IsScalarTower.continuousConstSMul
#align vadd_assoc_class.has_continuous_const_vadd VAddAssocClass.continuousConstVAdd

/- warning: smul_comm_class.has_continuous_const_smul -> SMulCommClass.continuousConstSMul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_5 : Monoid.{u2} A] [_inst_6 : SMul.{u1, u2} R A] [_inst_7 : SMulCommClass.{u1, u2, u2} R A A _inst_6 (Mul.toSMul.{u2} A (MulOneClass.toHasMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_5)))] [_inst_8 : TopologicalSpace.{u2} A] [_inst_9 : ContinuousMul.{u2} A _inst_8 (MulOneClass.toHasMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_5))], ContinuousConstSMul.{u1, u2} R A _inst_8 _inst_6
but is expected to have type
  forall {R : Type.{u1}} {A : Type.{u2}} [_inst_5 : Monoid.{u2} A] [_inst_6 : SMul.{u1, u2} R A] [_inst_7 : SMulCommClass.{u1, u2, u2} R A A _inst_6 (MulAction.toSMul.{u2, u2} A A _inst_5 (Monoid.toMulAction.{u2} A _inst_5))] [_inst_8 : TopologicalSpace.{u2} A] [_inst_9 : ContinuousMul.{u2} A _inst_8 (MulOneClass.toMul.{u2} A (Monoid.toMulOneClass.{u2} A _inst_5))], ContinuousConstSMul.{u1, u2} R A _inst_8 _inst_6
Case conversion may be inaccurate. Consider using '#align smul_comm_class.has_continuous_const_smul SMulCommClass.continuousConstSMulₓ'. -/
/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instances applies when `R = Aᵐᵒᵖ` -/
@[to_additive
      "If the action of `R` on `A` commutes with left-addition, then\ncontinuous addition implies continuous affine addition by constants.\n\nNotably, this instances applies when `R = Aᵃᵒᵖ`. "]
instance (priority := 100) SMulCommClass.continuousConstSMul {R A : Type _} [Monoid A] [SMul R A]
    [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A] : ContinuousConstSMul R A
    where continuous_const_smul q :=
    by
    simp (config := { singlePass := true }) only [← mul_smul_one q (_ : A)]
    exact continuous_id.mul continuous_const
#align smul_comm_class.has_continuous_const_smul SMulCommClass.continuousConstSMul
#align vadd_comm_class.has_continuous_const_vadd VAddCommClass.continuousConstVAdd

end ContinuousMul

namespace MulOpposite

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [TopologicalSpace α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ :=
  ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoid α] [ContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `topology.algebra.group`,
because the predicate `has_continuous_inv` has not yet been defined. -/
@[to_additive
      "If addition on an additive monoid is continuous, then addition on the additive units\nof the monoid, with respect to the induced topology, is continuous.\n\nNegation is also continuous, but we register this in a later file, `topology.algebra.group`, because\nthe predicate `has_continuous_neg` has not yet been defined."]
instance : ContinuousMul αˣ :=
  inducing_embedProduct.ContinuousMul (embedProduct α)

end Units

/- warning: continuous.units_map -> Continuous.units_map is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_2 : Monoid.{u1} M] [_inst_3 : Monoid.{u2} N] [_inst_4 : TopologicalSpace.{u1} M] [_inst_5 : TopologicalSpace.{u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)), (Continuous.{u1, u2} M N _inst_4 _inst_5 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_2) (Monoid.toMulOneClass.{u2} N _inst_3)) f)) -> (Continuous.{u1, u2} (Units.{u1} M _inst_2) (Units.{u2} N _inst_3) (Units.topologicalSpace.{u1} M _inst_4 _inst_2) (Units.topologicalSpace.{u2} N _inst_5 _inst_3) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} M _inst_2) (Units.{u2} N _inst_3) (Units.mulOneClass.{u1} M _inst_2) (Units.mulOneClass.{u2} N _inst_3)) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} M _inst_2) (Units.{u2} N _inst_3) (Units.mulOneClass.{u1} M _inst_2) (Units.mulOneClass.{u2} N _inst_3)) => (Units.{u1} M _inst_2) -> (Units.{u2} N _inst_3)) (MonoidHom.hasCoeToFun.{u1, u2} (Units.{u1} M _inst_2) (Units.{u2} N _inst_3) (Units.mulOneClass.{u1} M _inst_2) (Units.mulOneClass.{u2} N _inst_3)) (Units.map.{u1, u2} M N _inst_2 _inst_3 f)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_2 : Monoid.{u2} M] [_inst_3 : Monoid.{u1} N] [_inst_4 : TopologicalSpace.{u2} M] [_inst_5 : TopologicalSpace.{u1} N] (f : MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)), (Continuous.{u2, u1} M N _inst_4 _inst_5 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)) M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_2) (Monoid.toMulOneClass.{u1} N _inst_3)))) f)) -> (Continuous.{u2, u1} (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (Units.instTopologicalSpaceUnits.{u2} M _inst_4 _inst_2) (Units.instTopologicalSpaceUnits.{u1} N _inst_5 _inst_3) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (Units.instMulOneClassUnits.{u2} M _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_3)) (Units.{u2} M _inst_2) (fun (_x : Units.{u2} M _inst_2) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Units.{u2} M _inst_2) => Units.{u1} N _inst_3) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (Units.instMulOneClassUnits.{u2} M _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_3)) (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_2) (Units.instMulOneClassUnits.{u2} M _inst_2)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_3) (Units.instMulOneClassUnits.{u1} N _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (Units.instMulOneClassUnits.{u2} M _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_3)) (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (Units.instMulOneClassUnits.{u2} M _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_3) (MonoidHom.monoidHomClass.{u2, u1} (Units.{u2} M _inst_2) (Units.{u1} N _inst_3) (Units.instMulOneClassUnits.{u2} M _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_3)))) (Units.map.{u2, u1} M N _inst_2 _inst_3 f)))
Case conversion may be inaccurate. Consider using '#align continuous.units_map Continuous.units_mapₓ'. -/
@[to_additive]
theorem Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →* N) (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩
#align continuous.units_map Continuous.units_map
#align continuous.add_units_map Continuous.addUnits_map

section

variable [TopologicalSpace M] [CommMonoid M]

/- warning: submonoid.mem_nhds_one -> Submonoid.mem_nhds_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))), (IsOpen.{u1} M _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))))) S)) -> (Membership.Mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (Filter.hasMem.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))))) S) (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))), (IsOpen.{u1} M _inst_2 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) S)) -> (Membership.mem.{u1, u1} (Set.{u1} M) (Filter.{u1} M) (instMembershipSetFilter.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))) S) (nhds.{u1} M _inst_2 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3))))))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_nhds_one Submonoid.mem_nhds_oneₓ'. -/
@[to_additive]
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) :
    (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem
#align submonoid.mem_nhds_one Submonoid.mem_nhds_one
#align add_submonoid.mem_nhds_zero AddSubmonoid.mem_nhds_zero

variable [ContinuousMul M]

/- warning: tendsto_multiset_prod -> tendsto_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {M : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> α -> M} {x : Filter.{u2} α} {a : ι -> M} (s : Multiset.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i s) -> (Filter.Tendsto.{u2, u3} α M (f i) x (nhds.{u3} M _inst_2 (a i)))) -> (Filter.Tendsto.{u2, u3} α M (fun (b : α) => Multiset.prod.{u3} M _inst_3 (Multiset.map.{u1, u3} ι M (fun (c : ι) => f c b) s)) x (nhds.{u3} M _inst_2 (Multiset.prod.{u3} M _inst_3 (Multiset.map.{u1, u3} ι M a s))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))] {f : ι -> α -> M} {x : Filter.{u3} α} {a : ι -> M} (s : Multiset.{u2} ι), (forall (i : ι), (Membership.mem.{u2, u2} ι (Multiset.{u2} ι) (Multiset.instMembershipMultiset.{u2} ι) i s) -> (Filter.Tendsto.{u3, u1} α M (f i) x (nhds.{u1} M _inst_2 (a i)))) -> (Filter.Tendsto.{u3, u1} α M (fun (b : α) => Multiset.prod.{u1} M _inst_3 (Multiset.map.{u2, u1} ι M (fun (c : ι) => f c b) s)) x (nhds.{u1} M _inst_2 (Multiset.prod.{u1} M _inst_3 (Multiset.map.{u2, u1} ι M a s))))
Case conversion may be inaccurate. Consider using '#align tendsto_multiset_prod tendsto_multiset_prodₓ'. -/
@[to_additive]
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => (s.map fun c => f c b).Prod) x (𝓝 (s.map a).Prod) :=
  by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l
#align tendsto_multiset_prod tendsto_multiset_prod
#align tendsto_multiset_sum tendsto_multiset_sum

/- warning: tendsto_finset_prod -> tendsto_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {M : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> α -> M} {x : Filter.{u2} α} {a : ι -> M} (s : Finset.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Filter.Tendsto.{u2, u3} α M (f i) x (nhds.{u3} M _inst_2 (a i)))) -> (Filter.Tendsto.{u2, u3} α M (fun (b : α) => Finset.prod.{u3, u1} M ι _inst_3 s (fun (c : ι) => f c b)) x (nhds.{u3} M _inst_2 (Finset.prod.{u3, u1} M ι _inst_3 s (fun (c : ι) => a c))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {M : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))] {f : ι -> α -> M} {x : Filter.{u3} α} {a : ι -> M} (s : Finset.{u2} ι), (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Filter.Tendsto.{u3, u1} α M (f i) x (nhds.{u1} M _inst_2 (a i)))) -> (Filter.Tendsto.{u3, u1} α M (fun (b : α) => Finset.prod.{u1, u2} M ι _inst_3 s (fun (c : ι) => f c b)) x (nhds.{u1} M _inst_2 (Finset.prod.{u1, u2} M ι _inst_3 s (fun (c : ι) => a c))))
Case conversion may be inaccurate. Consider using '#align tendsto_finset_prod tendsto_finset_prodₓ'. -/
@[to_additive]
theorem tendsto_finset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
  tendsto_multiset_prod _
#align tendsto_finset_prod tendsto_finset_prod
#align tendsto_finset_sum tendsto_finset_sum

/- warning: continuous_multiset_prod -> continuous_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> X -> M} (s : Multiset.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i s) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (f i))) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (fun (a : X) => Multiset.prod.{u3} M _inst_3 (Multiset.map.{u1, u3} ι M (fun (i : ι) => f i a) s)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))] {f : ι -> X -> M} (s : Multiset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Multiset.{u3} ι) (Multiset.instMembershipMultiset.{u3} ι) i s) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (f i))) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (fun (a : X) => Multiset.prod.{u1} M _inst_3 (Multiset.map.{u3, u1} ι M (fun (i : ι) => f i a) s)))
Case conversion may be inaccurate. Consider using '#align continuous_multiset_prod continuous_multiset_prodₓ'. -/
@[continuity, to_additive]
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).Prod :=
  by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l
#align continuous_multiset_prod continuous_multiset_prod
#align continuous_multiset_sum continuous_multiset_sum

/- warning: continuous_on_multiset_prod -> continuousOn_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> X -> M} (s : Multiset.{u1} ι) {t : Set.{u2} X}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i s) -> (ContinuousOn.{u2, u3} X M _inst_1 _inst_2 (f i) t)) -> (ContinuousOn.{u2, u3} X M _inst_1 _inst_2 (fun (a : X) => Multiset.prod.{u3} M _inst_3 (Multiset.map.{u1, u3} ι M (fun (i : ι) => f i a) s)) t)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))] {f : ι -> X -> M} (s : Multiset.{u3} ι) {t : Set.{u2} X}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Multiset.{u3} ι) (Multiset.instMembershipMultiset.{u3} ι) i s) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (f i) t)) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (fun (a : X) => Multiset.prod.{u1} M _inst_3 (Multiset.map.{u3, u1} ι M (fun (i : ι) => f i a) s)) t)
Case conversion may be inaccurate. Consider using '#align continuous_on_multiset_prod continuousOn_multiset_prodₓ'. -/
@[to_additive]
theorem continuousOn_multiset_prod {f : ι → X → M} (s : Multiset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => (s.map fun i => f i a).Prod) t :=
  by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l
#align continuous_on_multiset_prod continuousOn_multiset_prod
#align continuous_on_multiset_sum continuousOn_multiset_sum

/- warning: continuous_finset_prod -> continuous_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> X -> M} (s : Finset.{u1} ι), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (f i))) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (fun (a : X) => Finset.prod.{u3, u1} M ι _inst_3 s (fun (i : ι) => f i a)))
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))] {f : ι -> X -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (f i))) -> (Continuous.{u2, u1} X M _inst_1 _inst_2 (fun (a : X) => Finset.prod.{u1, u3} M ι _inst_3 s (fun (i : ι) => f i a)))
Case conversion may be inaccurate. Consider using '#align continuous_finset_prod continuous_finset_prodₓ'. -/
@[continuity, to_additive]
theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => ∏ i in s, f i a :=
  continuous_multiset_prod _
#align continuous_finset_prod continuous_finset_prod
#align continuous_finset_sum continuous_finset_sum

/- warning: continuous_on_finset_prod -> continuousOn_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> X -> M} (s : Finset.{u1} ι) {t : Set.{u2} X}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (ContinuousOn.{u2, u3} X M _inst_1 _inst_2 (f i) t)) -> (ContinuousOn.{u2, u3} X M _inst_1 _inst_2 (fun (a : X) => Finset.prod.{u3, u1} M ι _inst_3 s (fun (i : ι) => f i a)) t)
but is expected to have type
  forall {ι : Type.{u3}} {X : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : CommMonoid.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))] {f : ι -> X -> M} (s : Finset.{u3} ι) {t : Set.{u2} X}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (f i) t)) -> (ContinuousOn.{u2, u1} X M _inst_1 _inst_2 (fun (a : X) => Finset.prod.{u1, u3} M ι _inst_3 s (fun (i : ι) => f i a)) t)
Case conversion may be inaccurate. Consider using '#align continuous_on_finset_prod continuousOn_finset_prodₓ'. -/
@[to_additive]
theorem continuousOn_finset_prod {f : ι → X → M} (s : Finset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => ∏ i in s, f i a) t :=
  continuousOn_multiset_prod _
#align continuous_on_finset_prod continuousOn_finset_prod
#align continuous_on_finset_sum continuousOn_finset_sum

/- warning: eventually_eq_prod -> eventuallyEq_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_5 : CommMonoid.{u3} M] {s : Finset.{u1} ι} {l : Filter.{u2} X} {f : ι -> X -> M} {g : ι -> X -> M}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Filter.EventuallyEq.{u2, u3} X M l (f i) (g i))) -> (Filter.EventuallyEq.{u2, u3} X M l (Finset.prod.{max u2 u3, u1} (X -> M) ι (Pi.commMonoid.{u2, u3} X (fun (ᾰ : X) => M) (fun (i : X) => _inst_5)) s (fun (i : ι) => f i)) (Finset.prod.{max u2 u3, u1} (X -> M) ι (Pi.commMonoid.{u2, u3} X (fun (ᾰ : X) => M) (fun (i : X) => _inst_5)) s (fun (i : ι) => g i)))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u3}} {M : Type.{u2}} [_inst_5 : CommMonoid.{u2} M] {s : Finset.{u1} ι} {l : Filter.{u3} X} {f : ι -> X -> M} {g : ι -> X -> M}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Filter.EventuallyEq.{u3, u2} X M l (f i) (g i))) -> (Filter.EventuallyEq.{u3, u2} X M l (Finset.prod.{max u3 u2, u1} (X -> M) ι (Pi.commMonoid.{u3, u2} X (fun (ᾰ : X) => M) (fun (i : X) => _inst_5)) s (fun (i : ι) => f i)) (Finset.prod.{max u3 u2, u1} (X -> M) ι (Pi.commMonoid.{u3, u2} X (fun (ᾰ : X) => M) (fun (i : X) => _inst_5)) s (fun (i : ι) => g i)))
Case conversion may be inaccurate. Consider using '#align eventually_eq_prod eventuallyEq_prodₓ'. -/
@[to_additive]
theorem eventuallyEq_prod {X M : Type _} [CommMonoid M] {s : Finset ι} {l : Filter X}
    {f g : ι → X → M} (hs : ∀ i ∈ s, f i =ᶠ[l] g i) : (∏ i in s, f i) =ᶠ[l] ∏ i in s, g i :=
  by
  replace hs : ∀ᶠ x in l, ∀ i ∈ s, f i x = g i x
  · rwa [eventually_all_finset]
  filter_upwards [hs]with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]
#align eventually_eq_prod eventuallyEq_prod
#align eventually_eq_sum eventuallyEq_sum

open Function

/- warning: locally_finite.exists_finset_mul_support -> LocallyFinite.exists_finset_mulSupport is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {M : Type.{u3}} [_inst_5 : CommMonoid.{u3} M] {f : ι -> X -> M}, (LocallyFinite.{u1, u2} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u2, u3} X M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_5))) (f i))) -> (forall (x₀ : X), Exists.{succ u1} (Finset.{u1} ι) (fun (I : Finset.{u1} ι) => Filter.Eventually.{u2} X (fun (x : X) => HasSubset.Subset.{u1} (Set.{u1} ι) (Set.hasSubset.{u1} ι) (Function.mulSupport.{u1, u3} ι M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_5))) (fun (i : ι) => f i x)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) I)) (nhds.{u2} X _inst_1 x₀)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {M : Type.{u3}} [_inst_5 : CommMonoid.{u3} M] {f : ι -> X -> M}, (LocallyFinite.{u2, u1} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u1, u3} X M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_5)) (f i))) -> (forall (x₀ : X), Exists.{succ u2} (Finset.{u2} ι) (fun (I : Finset.{u2} ι) => Filter.Eventually.{u1} X (fun (x : X) => HasSubset.Subset.{u2} (Set.{u2} ι) (Set.instHasSubsetSet.{u2} ι) (Function.mulSupport.{u2, u3} ι M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_5)) (fun (i : ι) => f i x)) (Finset.toSet.{u2} ι I)) (nhds.{u1} X _inst_1 x₀)))
Case conversion may be inaccurate. Consider using '#align locally_finite.exists_finset_mul_support LocallyFinite.exists_finset_mulSupportₓ'. -/
@[to_additive]
theorem LocallyFinite.exists_finset_mulSupport {M : Type _} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) ⊆ I :=
  by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine' ⟨hUf.to_finset, mem_of_superset hxU fun y hy i hi => _⟩
  rw [hUf.coe_to_finset]
  exact ⟨y, hi, hy⟩
#align locally_finite.exists_finset_mul_support LocallyFinite.exists_finset_mulSupport
#align locally_finite.exists_finset_support LocallyFinite.exists_finset_support

/- warning: finprod_eventually_eq_prod -> finprod_eventually_eq_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} X] {M : Type.{u3}} [_inst_5 : CommMonoid.{u3} M] {f : ι -> X -> M}, (LocallyFinite.{u1, u2} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u2, u3} X M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_5))) (f i))) -> (forall (x : X), Exists.{succ u1} (Finset.{u1} ι) (fun (s : Finset.{u1} ι) => Filter.Eventually.{u2} X (fun (y : X) => Eq.{succ u3} M (finprod.{u3, succ u1} M ι _inst_5 (fun (i : ι) => f i y)) (Finset.prod.{u3, u1} M ι _inst_5 s (fun (i : ι) => f i y))) (nhds.{u2} X _inst_1 x)))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {M : Type.{u3}} [_inst_5 : CommMonoid.{u3} M] {f : ι -> X -> M}, (LocallyFinite.{u2, u1} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u1, u3} X M (Monoid.toOne.{u3} M (CommMonoid.toMonoid.{u3} M _inst_5)) (f i))) -> (forall (x : X), Exists.{succ u2} (Finset.{u2} ι) (fun (s : Finset.{u2} ι) => Filter.Eventually.{u1} X (fun (y : X) => Eq.{succ u3} M (finprod.{u3, succ u2} M ι _inst_5 (fun (i : ι) => f i y)) (Finset.prod.{u3, u2} M ι _inst_5 s (fun (i : ι) => f i y))) (nhds.{u1} X _inst_1 x)))
Case conversion may be inaccurate. Consider using '#align finprod_eventually_eq_prod finprod_eventually_eq_prodₓ'. -/
@[to_additive]
theorem finprod_eventually_eq_prod {M : Type _} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport (f i)) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, (∏ᶠ i, f i y) = ∏ i in s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun y hy => finprod_eq_prod_of_mulSupport_subset _ fun i hi => hy hi⟩
#align finprod_eventually_eq_prod finprod_eventually_eq_prod
#align finsum_eventually_eq_sum finsum_eventually_eq_sum

/- warning: continuous_finprod -> continuous_finprod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> X -> M}, (forall (i : ι), Continuous.{u2, u3} X M _inst_1 _inst_2 (f i)) -> (LocallyFinite.{u1, u2} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u2, u3} X M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3))) (f i))) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (fun (x : X) => finprod.{u3, succ u1} M ι _inst_3 (fun (i : ι) => f i x)))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u3}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommMonoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3)))] {f : ι -> X -> M}, (forall (i : ι), Continuous.{u3, u2} X M _inst_1 _inst_2 (f i)) -> (LocallyFinite.{u1, u3} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u3, u2} X M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3)) (f i))) -> (Continuous.{u3, u2} X M _inst_1 _inst_2 (fun (x : X) => finprod.{u2, succ u1} M ι _inst_3 (fun (i : ι) => f i x)))
Case conversion may be inaccurate. Consider using '#align continuous_finprod continuous_finprodₓ'. -/
@[to_additive]
theorem continuous_finprod {f : ι → X → M} (hc : ∀ i, Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x :=
  by
  refine' continuous_iff_continuousAt.2 fun x => _
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine' ContinuousAt.congr _ (eventually_eq.symm hs)
  exact tendsto_finset_prod _ fun i hi => (hc i).ContinuousAt
#align continuous_finprod continuous_finprod
#align continuous_finsum continuous_finsum

/- warning: continuous_finprod_cond -> continuous_finprod_cond is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} {M : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : CommMonoid.{u3} M] [_inst_4 : ContinuousMul.{u3} M _inst_2 (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3)))] {f : ι -> X -> M} {p : ι -> Prop}, (forall (i : ι), (p i) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (f i))) -> (LocallyFinite.{u1, u2} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u2, u3} X M (MulOneClass.toHasOne.{u3} M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_3))) (f i))) -> (Continuous.{u2, u3} X M _inst_1 _inst_2 (fun (x : X) => finprod.{u3, succ u1} M ι _inst_3 (fun (i : ι) => finprod.{u3, 0} M (p i) _inst_3 (fun (hi : p i) => f i x))))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u3}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} X] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommMonoid.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3)))] {f : ι -> X -> M} {p : ι -> Prop}, (forall (i : ι), (p i) -> (Continuous.{u3, u2} X M _inst_1 _inst_2 (f i))) -> (LocallyFinite.{u1, u3} ι X _inst_1 (fun (i : ι) => Function.mulSupport.{u3, u2} X M (Monoid.toOne.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3)) (f i))) -> (Continuous.{u3, u2} X M _inst_1 _inst_2 (fun (x : X) => finprod.{u2, succ u1} M ι _inst_3 (fun (i : ι) => finprod.{u2, 0} M (p i) _inst_3 (fun (hi : p i) => f i x))))
Case conversion may be inaccurate. Consider using '#align continuous_finprod_cond continuous_finprod_condₓ'. -/
@[to_additive]
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ (i) (hi : p i), f i x :=
  by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)
#align continuous_finprod_cond continuous_finprod_cond
#align continuous_finsum_cond continuous_finsum_cond

end

instance [TopologicalSpace M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M)
    where continuous_add := @continuous_mul M _ _ _

instance [TopologicalSpace M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M)
    where continuous_mul := @continuous_add M _ _ _

section LatticeOps

variable {ι' : Sort _} [Mul M]

/- warning: has_continuous_mul_Inf -> continuousMul_infₛ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : Mul.{u1} M] {ts : Set.{u1} (TopologicalSpace.{u1} M)}, (forall (t : TopologicalSpace.{u1} M), (Membership.Mem.{u1, u1} (TopologicalSpace.{u1} M) (Set.{u1} (TopologicalSpace.{u1} M)) (Set.hasMem.{u1} (TopologicalSpace.{u1} M)) t ts) -> (ContinuousMul.{u1} M t _inst_2)) -> (ContinuousMul.{u1} M (InfSet.infₛ.{u1} (TopologicalSpace.{u1} M) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} M) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} M) (TopologicalSpace.completeLattice.{u1} M))) ts) _inst_2)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : Mul.{u1} M] {ts : Set.{u1} (TopologicalSpace.{u1} M)}, (forall (t : TopologicalSpace.{u1} M), (Membership.mem.{u1, u1} (TopologicalSpace.{u1} M) (Set.{u1} (TopologicalSpace.{u1} M)) (Set.instMembershipSet.{u1} (TopologicalSpace.{u1} M)) t ts) -> (ContinuousMul.{u1} M t _inst_2)) -> (ContinuousMul.{u1} M (InfSet.infₛ.{u1} (TopologicalSpace.{u1} M) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} M) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} M) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} M))) ts) _inst_2)
Case conversion may be inaccurate. Consider using '#align has_continuous_mul_Inf continuousMul_infₛₓ'. -/
@[to_additive]
theorem continuousMul_infₛ {ts : Set (TopologicalSpace M)} (h : ∀ t ∈ ts, @ContinuousMul M t _) :
    @ContinuousMul M (infₛ ts) _ :=
  {
    continuous_mul :=
      continuous_infₛ_rng.2 fun t ht =>
        continuous_infₛ_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }
#align has_continuous_mul_Inf continuousMul_infₛ
#align has_continuous_add_Inf continuousAdd_infₛ

/- warning: has_continuous_mul_infi -> continuousMul_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι' : Sort.{u2}} [_inst_2 : Mul.{u1} M] {ts : ι' -> (TopologicalSpace.{u1} M)}, (forall (i : ι'), ContinuousMul.{u1} M (ts i) _inst_2) -> (ContinuousMul.{u1} M (infᵢ.{u1, u2} (TopologicalSpace.{u1} M) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} M) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} M) (TopologicalSpace.completeLattice.{u1} M))) ι' (fun (i : ι') => ts i)) _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {ι' : Sort.{u1}} [_inst_2 : Mul.{u2} M] {ts : ι' -> (TopologicalSpace.{u2} M)}, (forall (i : ι'), ContinuousMul.{u2} M (ts i) _inst_2) -> (ContinuousMul.{u2} M (infᵢ.{u2, u1} (TopologicalSpace.{u2} M) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} M) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} M) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} M))) ι' (fun (i : ι') => ts i)) _inst_2)
Case conversion may be inaccurate. Consider using '#align has_continuous_mul_infi continuousMul_infᵢₓ'. -/
@[to_additive]
theorem continuousMul_infᵢ {ts : ι' → TopologicalSpace M} (h' : ∀ i, @ContinuousMul M (ts i) _) :
    @ContinuousMul M (⨅ i, ts i) _ := by
  rw [← infₛ_range]
  exact continuousMul_infₛ (set.forall_range_iff.mpr h')
#align has_continuous_mul_infi continuousMul_infᵢ
#align has_continuous_add_infi continuousAdd_infᵢ

/- warning: has_continuous_mul_inf -> continuousMul_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : Mul.{u1} M] {t₁ : TopologicalSpace.{u1} M} {t₂ : TopologicalSpace.{u1} M}, (ContinuousMul.{u1} M t₁ _inst_2) -> (ContinuousMul.{u1} M t₂ _inst_2) -> (ContinuousMul.{u1} M (Inf.inf.{u1} (TopologicalSpace.{u1} M) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.{u1} M) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.{u1} M) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} M) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} M) (TopologicalSpace.completeLattice.{u1} M))))) t₁ t₂) _inst_2)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : Mul.{u1} M] {t₁ : TopologicalSpace.{u1} M} {t₂ : TopologicalSpace.{u1} M}, (ContinuousMul.{u1} M t₁ _inst_2) -> (ContinuousMul.{u1} M t₂ _inst_2) -> (ContinuousMul.{u1} M (Inf.inf.{u1} (TopologicalSpace.{u1} M) (Lattice.toInf.{u1} (TopologicalSpace.{u1} M) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.{u1} M) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} M) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} M)))) t₁ t₂) _inst_2)
Case conversion may be inaccurate. Consider using '#align has_continuous_mul_inf continuousMul_infₓ'. -/
@[to_additive]
theorem continuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
    (h₂ : @ContinuousMul M t₂ _) : @ContinuousMul M (t₁ ⊓ t₂) _ :=
  by
  rw [inf_eq_infᵢ]
  refine' continuousMul_infᵢ fun b => _
  cases b <;> assumption
#align has_continuous_mul_inf continuousMul_inf
#align has_continuous_add_inf continuousAdd_inf

end LatticeOps

namespace ContinuousMap

variable [Mul X] [ContinuousMul X]

/-- The continuous map `λ y, y * x` -/
@[to_additive "The continuous map `λ y, y + x"]
protected def mulRight (x : X) : C(X, X) :=
  mk _ (continuous_mul_right x)
#align continuous_map.mul_right ContinuousMap.mulRight
#align continuous_map.add_right ContinuousMap.addRight

@[to_additive, simp]
theorem coe_mulRight (x : X) : ⇑(ContinuousMap.mulRight x) = fun y => y * x :=
  rfl
#align continuous_map.coe_mul_right ContinuousMap.coe_mulRight
#align continuous_map.coe_add_right ContinuousMap.coe_add_right

/-- The continuous map `λ y, x * y` -/
@[to_additive "The continuous map `λ y, x + y"]
protected def mulLeft (x : X) : C(X, X) :=
  mk _ (continuous_mul_left x)
#align continuous_map.mul_left ContinuousMap.mulLeft
#align continuous_map.add_left ContinuousMap.addLeft

@[to_additive, simp]
theorem coe_mulLeft (x : X) : ⇑(ContinuousMap.mulLeft x) = fun y => x * y :=
  rfl
#align continuous_map.coe_mul_left ContinuousMap.coe_mulLeft
#align continuous_map.coe_add_left ContinuousMap.coe_add_left

end ContinuousMap

