/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.mul_action
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.AddTorsor
import Mathbin.Topology.Algebra.Constructions
import Mathbin.GroupTheory.GroupAction.Prod
import Mathbin.Topology.Algebra.ConstMulAction

/-!
# Continuous monoid action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M X` if `M` acts on
`X` and the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.
* `units.has_continuous_smul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/


open Topology Pointwise

open Filter

#print ContinuousSMul /-
/-- Class `has_continuous_smul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class ContinuousSMul (M X : Type _) [SMul M X] [TopologicalSpace M] [TopologicalSpace X] :
  Prop where
  continuous_smul : Continuous fun p : M × X => p.1 • p.2
#align has_continuous_smul ContinuousSMul
-/

export ContinuousSMul (continuous_smul)

#print ContinuousVAdd /-
/-- Class `has_continuous_vadd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class ContinuousVAdd (M X : Type _) [VAdd M X] [TopologicalSpace M] [TopologicalSpace X] :
  Prop where
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2
#align has_continuous_vadd ContinuousVAdd
-/

export ContinuousVAdd (continuous_vadd)

attribute [to_additive] ContinuousSMul

section Main

variable {M X Y α : Type _} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section SMul

variable [SMul M X] [ContinuousSMul M X]

#print ContinuousSMul.continuousConstSMul /-
@[to_additive]
instance (priority := 100) ContinuousSMul.continuousConstSMul : ContinuousConstSMul M X
    where continuous_const_smul _ := continuous_smul.comp (continuous_const.prod_mk continuous_id)
#align has_continuous_smul.has_continuous_const_smul ContinuousSMul.continuousConstSMul
#align has_continuous_vadd.has_continuous_const_vadd ContinuousVAdd.continuousConstVAdd
-/

/- warning: filter.tendsto.smul -> Filter.Tendsto.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_4 : SMul.{u1, u2} M X] [_inst_5 : ContinuousSMul.{u1, u2} M X _inst_4 _inst_1 _inst_2] {f : α -> M} {g : α -> X} {l : Filter.{u3} α} {c : M} {a : X}, (Filter.Tendsto.{u3, u1} α M f l (nhds.{u1} M _inst_1 c)) -> (Filter.Tendsto.{u3, u2} α X g l (nhds.{u2} X _inst_2 a)) -> (Filter.Tendsto.{u3, u2} α X (fun (x : α) => SMul.smul.{u1, u2} M X _inst_4 (f x) (g x)) l (nhds.{u2} X _inst_2 (SMul.smul.{u1, u2} M X _inst_4 c a)))
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : TopologicalSpace.{u1} X] [_inst_4 : SMul.{u2, u1} M X] [_inst_5 : ContinuousSMul.{u2, u1} M X _inst_4 _inst_1 _inst_2] {f : α -> M} {g : α -> X} {l : Filter.{u3} α} {c : M} {a : X}, (Filter.Tendsto.{u3, u2} α M f l (nhds.{u2} M _inst_1 c)) -> (Filter.Tendsto.{u3, u1} α X g l (nhds.{u1} X _inst_2 a)) -> (Filter.Tendsto.{u3, u1} α X (fun (x : α) => HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) (f x) (g x)) l (nhds.{u1} X _inst_2 (HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) c a)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.smul Filter.Tendsto.smulₓ'. -/
@[to_additive]
theorem Filter.Tendsto.smul {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X}
    (hf : Tendsto f l (𝓝 c)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.Tendsto _).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.smul Filter.Tendsto.smul
#align filter.tendsto.vadd Filter.Tendsto.vadd

/- warning: filter.tendsto.smul_const -> Filter.Tendsto.smul_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_4 : SMul.{u1, u2} M X] [_inst_5 : ContinuousSMul.{u1, u2} M X _inst_4 _inst_1 _inst_2] {f : α -> M} {l : Filter.{u3} α} {c : M}, (Filter.Tendsto.{u3, u1} α M f l (nhds.{u1} M _inst_1 c)) -> (forall (a : X), Filter.Tendsto.{u3, u2} α X (fun (x : α) => SMul.smul.{u1, u2} M X _inst_4 (f x) a) l (nhds.{u2} X _inst_2 (SMul.smul.{u1, u2} M X _inst_4 c a)))
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : TopologicalSpace.{u1} X] [_inst_4 : SMul.{u2, u1} M X] [_inst_5 : ContinuousSMul.{u2, u1} M X _inst_4 _inst_1 _inst_2] {f : α -> M} {l : Filter.{u3} α} {c : M}, (Filter.Tendsto.{u3, u2} α M f l (nhds.{u2} M _inst_1 c)) -> (forall (a : X), Filter.Tendsto.{u3, u1} α X (fun (x : α) => HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) (f x) a) l (nhds.{u1} X _inst_2 (HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) c a)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.smul_const Filter.Tendsto.smul_constₓ'. -/
@[to_additive]
theorem Filter.Tendsto.smul_const {f : α → M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c))
    (a : X) : Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds
#align filter.tendsto.smul_const Filter.Tendsto.smul_const
#align filter.tendsto.vadd_const Filter.Tendsto.vadd_const

variable {f : Y → M} {g : Y → X} {b : Y} {s : Set Y}

/- warning: continuous_within_at.smul -> ContinuousWithinAt.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u1, u2} M X] [_inst_5 : ContinuousSMul.{u1, u2} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X} {b : Y} {s : Set.{u3} Y}, (ContinuousWithinAt.{u3, u1} Y M _inst_3 _inst_1 f s b) -> (ContinuousWithinAt.{u3, u2} Y X _inst_3 _inst_2 g s b) -> (ContinuousWithinAt.{u3, u2} Y X _inst_3 _inst_2 (fun (x : Y) => SMul.smul.{u1, u2} M X _inst_4 (f x) (g x)) s b)
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : TopologicalSpace.{u1} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u2, u1} M X] [_inst_5 : ContinuousSMul.{u2, u1} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X} {b : Y} {s : Set.{u3} Y}, (ContinuousWithinAt.{u3, u2} Y M _inst_3 _inst_1 f s b) -> (ContinuousWithinAt.{u3, u1} Y X _inst_3 _inst_2 g s b) -> (ContinuousWithinAt.{u3, u1} Y X _inst_3 _inst_2 (fun (x : Y) => HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) (f x) (g x)) s b)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.smul ContinuousWithinAt.smulₓ'. -/
@[to_additive]
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (fun x => f x • g x) s b :=
  hf.smul hg
#align continuous_within_at.smul ContinuousWithinAt.smul
#align continuous_within_at.vadd ContinuousWithinAt.vadd

/- warning: continuous_at.smul -> ContinuousAt.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u1, u2} M X] [_inst_5 : ContinuousSMul.{u1, u2} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X} {b : Y}, (ContinuousAt.{u3, u1} Y M _inst_3 _inst_1 f b) -> (ContinuousAt.{u3, u2} Y X _inst_3 _inst_2 g b) -> (ContinuousAt.{u3, u2} Y X _inst_3 _inst_2 (fun (x : Y) => SMul.smul.{u1, u2} M X _inst_4 (f x) (g x)) b)
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : TopologicalSpace.{u1} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u2, u1} M X] [_inst_5 : ContinuousSMul.{u2, u1} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X} {b : Y}, (ContinuousAt.{u3, u2} Y M _inst_3 _inst_1 f b) -> (ContinuousAt.{u3, u1} Y X _inst_3 _inst_2 g b) -> (ContinuousAt.{u3, u1} Y X _inst_3 _inst_2 (fun (x : Y) => HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) (f x) (g x)) b)
Case conversion may be inaccurate. Consider using '#align continuous_at.smul ContinuousAt.smulₓ'. -/
@[to_additive]
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
    ContinuousAt (fun x => f x • g x) b :=
  hf.smul hg
#align continuous_at.smul ContinuousAt.smul
#align continuous_at.vadd ContinuousAt.vadd

/- warning: continuous_on.smul -> ContinuousOn.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u1, u2} M X] [_inst_5 : ContinuousSMul.{u1, u2} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X} {s : Set.{u3} Y}, (ContinuousOn.{u3, u1} Y M _inst_3 _inst_1 f s) -> (ContinuousOn.{u3, u2} Y X _inst_3 _inst_2 g s) -> (ContinuousOn.{u3, u2} Y X _inst_3 _inst_2 (fun (x : Y) => SMul.smul.{u1, u2} M X _inst_4 (f x) (g x)) s)
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : TopologicalSpace.{u1} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u2, u1} M X] [_inst_5 : ContinuousSMul.{u2, u1} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X} {s : Set.{u3} Y}, (ContinuousOn.{u3, u2} Y M _inst_3 _inst_1 f s) -> (ContinuousOn.{u3, u1} Y X _inst_3 _inst_2 g s) -> (ContinuousOn.{u3, u1} Y X _inst_3 _inst_2 (fun (x : Y) => HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.smul ContinuousOn.smulₓ'. -/
@[to_additive]
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x • g x) s := fun x hx => (hf x hx).smul (hg x hx)
#align continuous_on.smul ContinuousOn.smul
#align continuous_on.vadd ContinuousOn.vadd

/- warning: continuous.smul -> Continuous.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u1, u2} M X] [_inst_5 : ContinuousSMul.{u1, u2} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X}, (Continuous.{u3, u1} Y M _inst_3 _inst_1 f) -> (Continuous.{u3, u2} Y X _inst_3 _inst_2 g) -> (Continuous.{u3, u2} Y X _inst_3 _inst_2 (fun (x : Y) => SMul.smul.{u1, u2} M X _inst_4 (f x) (g x)))
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} {Y : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : TopologicalSpace.{u1} X] [_inst_3 : TopologicalSpace.{u3} Y] [_inst_4 : SMul.{u2, u1} M X] [_inst_5 : ContinuousSMul.{u2, u1} M X _inst_4 _inst_1 _inst_2] {f : Y -> M} {g : Y -> X}, (Continuous.{u3, u2} Y M _inst_3 _inst_1 f) -> (Continuous.{u3, u1} Y X _inst_3 _inst_2 g) -> (Continuous.{u3, u1} Y X _inst_3 _inst_2 (fun (x : Y) => HSMul.hSMul.{u2, u1, u1} M X X (instHSMul.{u2, u1} M X _inst_4) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align continuous.smul Continuous.smulₓ'. -/
@[continuity, to_additive]
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
  continuous_smul.comp (hf.prod_mk hg)
#align continuous.smul Continuous.smul
#align continuous.vadd Continuous.vadd

#print ContinuousSMul.op /-
/-- If a scalar action is central, then its right action is continuous when its left action is. -/
@[to_additive
      "If an additive action is central, then its right action is continuous when its left\naction is."]
instance ContinuousSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : ContinuousSMul Mᵐᵒᵖ X :=
  ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.Prod_map continuous_id)
    simpa only [op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩
#align has_continuous_smul.op ContinuousSMul.op
#align has_continuous_vadd.op ContinuousVAdd.op
-/

#print MulOpposite.continuousSMul /-
@[to_additive]
instance MulOpposite.continuousSMul : ContinuousSMul M Xᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <|
      continuous_smul.comp <| continuous_id.Prod_map MulOpposite.continuous_unop⟩
#align mul_opposite.has_continuous_smul MulOpposite.continuousSMul
#align add_opposite.has_continuous_vadd AddOpposite.continuousVAdd
-/

end SMul

section Monoid

variable [Monoid M] [MulAction M X] [ContinuousSMul M X]

/- warning: units.has_continuous_smul -> Units.continuousSMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_4 : Monoid.{u1} M] [_inst_5 : MulAction.{u1, u2} M X _inst_4] [_inst_6 : ContinuousSMul.{u1, u2} M X (MulAction.toHasSmul.{u1, u2} M X _inst_4 _inst_5) _inst_1 _inst_2], ContinuousSMul.{u1, u2} (Units.{u1} M _inst_4) X (Units.hasSmul.{u1, u2} M X _inst_4 (MulAction.toHasSmul.{u1, u2} M X _inst_4 _inst_5)) (Units.topologicalSpace.{u1} M _inst_1 _inst_4) _inst_2
but is expected to have type
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : TopologicalSpace.{u2} X] [_inst_4 : Monoid.{u1} M] [_inst_5 : MulAction.{u1, u2} M X _inst_4] [_inst_6 : ContinuousSMul.{u1, u2} M X (MulAction.toSMul.{u1, u2} M X _inst_4 _inst_5) _inst_1 _inst_2], ContinuousSMul.{u1, u2} (Units.{u1} M _inst_4) X (Units.instSMulUnits.{u1, u2} M X _inst_4 (MulAction.toSMul.{u1, u2} M X _inst_4 _inst_5)) (Units.instTopologicalSpaceUnits.{u1} M _inst_1 _inst_4) _inst_2
Case conversion may be inaccurate. Consider using '#align units.has_continuous_smul Units.continuousSMulₓ'. -/
@[to_additive]
instance Units.continuousSMul : ContinuousSMul Mˣ X
    where continuous_smul :=
    show Continuous ((fun p : M × X => p.fst • p.snd) ∘ fun p : Mˣ × X => (p.1, p.2)) from
      continuous_smul.comp ((Units.continuous_val.comp continuous_fst).prod_mk continuous_snd)
#align units.has_continuous_smul Units.continuousSMul
#align add_units.has_continuous_vadd AddUnits.continuousVAdd

end Monoid

@[to_additive]
instance [SMul M X] [SMul M Y] [ContinuousSMul M X] [ContinuousSMul M Y] :
    ContinuousSMul M (X × Y) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type _} {γ : ι → Type _} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousSMul M (γ i)] : ContinuousSMul M (∀ i, γ i) :=
  ⟨continuous_pi fun i =>
      (continuous_fst.smul continuous_snd).comp <|
        continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

end Main

section LatticeOps

variable {ι : Sort _} {M X : Type _} [TopologicalSpace M] [SMul M X]

/- warning: has_continuous_smul_Inf -> continuousSMul_infₛ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : SMul.{u1, u2} M X] {ts : Set.{u2} (TopologicalSpace.{u2} X)}, (forall (t : TopologicalSpace.{u2} X), (Membership.Mem.{u2, u2} (TopologicalSpace.{u2} X) (Set.{u2} (TopologicalSpace.{u2} X)) (Set.hasMem.{u2} (TopologicalSpace.{u2} X)) t ts) -> (ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 t)) -> (ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 (InfSet.infₛ.{u2} (TopologicalSpace.{u2} X) (ConditionallyCompleteLattice.toHasInf.{u2} (TopologicalSpace.{u2} X) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} X) (TopologicalSpace.completeLattice.{u2} X))) ts))
but is expected to have type
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : SMul.{u1, u2} M X] {ts : Set.{u2} (TopologicalSpace.{u2} X)}, (forall (t : TopologicalSpace.{u2} X), (Membership.mem.{u2, u2} (TopologicalSpace.{u2} X) (Set.{u2} (TopologicalSpace.{u2} X)) (Set.instMembershipSet.{u2} (TopologicalSpace.{u2} X)) t ts) -> (ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 t)) -> (ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 (InfSet.infₛ.{u2} (TopologicalSpace.{u2} X) (ConditionallyCompleteLattice.toInfSet.{u2} (TopologicalSpace.{u2} X) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} X) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} X))) ts))
Case conversion may be inaccurate. Consider using '#align has_continuous_smul_Inf continuousSMul_infₛₓ'. -/
@[to_additive]
theorem continuousSMul_infₛ {ts : Set (TopologicalSpace X)}
    (h : ∀ t ∈ ts, @ContinuousSMul M X _ _ t) : @ContinuousSMul M X _ _ (infₛ ts) :=
  {
    continuous_smul := by
      rw [← @infₛ_singleton _ _ ‹TopologicalSpace M›]
      exact
        continuous_infₛ_rng.2 fun t ht =>
          continuous_infₛ_dom₂ (Eq.refl _) ht (@ContinuousSMul.continuous_smul _ _ _ _ t (h t ht)) }
#align has_continuous_smul_Inf continuousSMul_infₛ
#align has_continuous_vadd_Inf continuousVAdd_infₛ

/- warning: has_continuous_smul_infi -> continuousSMul_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {M : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : SMul.{u2, u3} M X] {ts' : ι -> (TopologicalSpace.{u3} X)}, (forall (i : ι), ContinuousSMul.{u2, u3} M X _inst_2 _inst_1 (ts' i)) -> (ContinuousSMul.{u2, u3} M X _inst_2 _inst_1 (infᵢ.{u3, u1} (TopologicalSpace.{u3} X) (ConditionallyCompleteLattice.toHasInf.{u3} (TopologicalSpace.{u3} X) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} X) (TopologicalSpace.completeLattice.{u3} X))) ι (fun (i : ι) => ts' i)))
but is expected to have type
  forall {ι : Sort.{u1}} {M : Type.{u2}} {X : Type.{u3}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : SMul.{u2, u3} M X] {ts' : ι -> (TopologicalSpace.{u3} X)}, (forall (i : ι), ContinuousSMul.{u2, u3} M X _inst_2 _inst_1 (ts' i)) -> (ContinuousSMul.{u2, u3} M X _inst_2 _inst_1 (infᵢ.{u3, u1} (TopologicalSpace.{u3} X) (ConditionallyCompleteLattice.toInfSet.{u3} (TopologicalSpace.{u3} X) (CompleteLattice.toConditionallyCompleteLattice.{u3} (TopologicalSpace.{u3} X) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u3} X))) ι (fun (i : ι) => ts' i)))
Case conversion may be inaccurate. Consider using '#align has_continuous_smul_infi continuousSMul_infᵢₓ'. -/
@[to_additive]
theorem continuousSMul_infᵢ {ts' : ι → TopologicalSpace X}
    (h : ∀ i, @ContinuousSMul M X _ _ (ts' i)) : @ContinuousSMul M X _ _ (⨅ i, ts' i) :=
  continuousSMul_infₛ <| Set.forall_range_iff.mpr h
#align has_continuous_smul_infi continuousSMul_infᵢ
#align has_continuous_vadd_infi continuousVAdd_infᵢ

/- warning: has_continuous_smul_inf -> continuousSMul_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : SMul.{u1, u2} M X] {t₁ : TopologicalSpace.{u2} X} {t₂ : TopologicalSpace.{u2} X} [_inst_3 : ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 t₁] [_inst_4 : ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 t₂], ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 (HasInf.inf.{u2} (TopologicalSpace.{u2} X) (SemilatticeInf.toHasInf.{u2} (TopologicalSpace.{u2} X) (Lattice.toSemilatticeInf.{u2} (TopologicalSpace.{u2} X) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} X) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} X) (TopologicalSpace.completeLattice.{u2} X))))) t₁ t₂)
but is expected to have type
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : SMul.{u1, u2} M X] {t₁ : TopologicalSpace.{u2} X} {t₂ : TopologicalSpace.{u2} X} [_inst_3 : ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 t₁] [_inst_4 : ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 t₂], ContinuousSMul.{u1, u2} M X _inst_2 _inst_1 (HasInf.inf.{u2} (TopologicalSpace.{u2} X) (Lattice.toHasInf.{u2} (TopologicalSpace.{u2} X) (ConditionallyCompleteLattice.toLattice.{u2} (TopologicalSpace.{u2} X) (CompleteLattice.toConditionallyCompleteLattice.{u2} (TopologicalSpace.{u2} X) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u2} X)))) t₁ t₂)
Case conversion may be inaccurate. Consider using '#align has_continuous_smul_inf continuousSMul_infₓ'. -/
@[to_additive]
theorem continuousSMul_inf {t₁ t₂ : TopologicalSpace X} [@ContinuousSMul M X _ _ t₁]
    [@ContinuousSMul M X _ _ t₂] : @ContinuousSMul M X _ _ (t₁ ⊓ t₂) :=
  by
  rw [inf_eq_infᵢ]
  refine' continuousSMul_infᵢ fun b => _
  cases b <;> assumption
#align has_continuous_smul_inf continuousSMul_inf
#align has_continuous_vadd_inf continuousVAdd_inf

end LatticeOps

section AddTorsor

variable (G : Type _) (P : Type _) [AddGroup G] [AddTorsor G P] [TopologicalSpace G]

variable [PreconnectedSpace G] [TopologicalSpace P] [ContinuousVAdd G P]

include G

/- warning: add_torsor.connected_space -> AddTorsor.connectedSpace is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) (P : Type.{u2}) [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] [_inst_3 : TopologicalSpace.{u1} G] [_inst_4 : PreconnectedSpace.{u1} G _inst_3] [_inst_5 : TopologicalSpace.{u2} P] [_inst_6 : ContinuousVAdd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 _inst_2)) _inst_3 _inst_5], ConnectedSpace.{u2} P _inst_5
but is expected to have type
  forall (G : Type.{u2}) (P : Type.{u1}) [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1] [_inst_3 : TopologicalSpace.{u2} G] [_inst_4 : PreconnectedSpace.{u2} G _inst_3] [_inst_5 : TopologicalSpace.{u1} P] [_inst_6 : ContinuousVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 _inst_2)) _inst_3 _inst_5], ConnectedSpace.{u1} P _inst_5
Case conversion may be inaccurate. Consider using '#align add_torsor.connected_space AddTorsor.connectedSpaceₓ'. -/
/-- An `add_torsor` for a connected space is a connected space. This is not an instance because
it loops for a group as a torsor over itself. -/
protected theorem AddTorsor.connectedSpace : ConnectedSpace P :=
  { isPreconnected_univ :=
      by
      convert
        is_preconnected_univ.image (Equiv.vaddConst (Classical.arbitrary P) : G → P)
          (continuous_id.vadd continuous_const).ContinuousOn
      rw [Set.image_univ, Equiv.range_eq_univ]
    to_nonempty := inferInstance }
#align add_torsor.connected_space AddTorsor.connectedSpace

end AddTorsor

