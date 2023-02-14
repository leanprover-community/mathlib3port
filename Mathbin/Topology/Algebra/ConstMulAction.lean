/-
Copyright (c) 2021 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth

! This file was ported from Lean 3 source module topology.algebra.const_mul_action
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Constructions
import Mathbin.Topology.Homeomorph
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.Topology.Bases
import Mathbin.Topology.Support

/-!
# Monoid actions continuous in the second variable

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define class `has_continuous_const_smul`. We say `has_continuous_const_smul Γ T` if
`Γ` acts on `T` and for each `γ`, the map `x ↦ γ • x` is continuous. (This differs from
`has_continuous_smul`, which requires simultaneous continuity in both variables.)

## Main definitions

* `has_continuous_const_smul Γ T` : typeclass saying that the map `x ↦ γ • x` is continuous on `T`;
* `properly_discontinuous_smul`: says that the scalar multiplication `(•) : Γ → T → T`
  is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely
  many `γ:Γ` move `K` to have nontrivial intersection with `L`.
* `homeomorph.smul`: scalar multiplication by an element of a group `Γ` acting on `T`
  is a homeomorphism of `T`.

## Main results

* `is_open_map_quotient_mk_mul` : The quotient map by a group action is open.
* `t2_space_of_properly_discontinuous_smul_of_t2_space` : The quotient by a discontinuous group
  action of a locally compact t2 space is t2.

## Tags

Hausdorff, discrete group, properly discontinuous, quotient space

-/


open Topology Pointwise

open Filter Set TopologicalSpace

attribute [local instance] MulAction.orbitRel

#print ContinuousConstSMul /-
/-- Class `has_continuous_const_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras.

Note that both `has_continuous_const_smul α α` and `has_continuous_const_smul αᵐᵒᵖ α` are
weaker versions of `has_continuous_mul α`. -/
class ContinuousConstSMul (Γ : Type _) (T : Type _) [TopologicalSpace T] [SMul Γ T] : Prop where
  continuous_const_smul : ∀ γ : Γ, Continuous fun x : T => γ • x
#align has_continuous_const_smul ContinuousConstSMul
-/

#print ContinuousConstVAdd /-
/-- Class `has_continuous_const_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is continuous in the second argument. We use the same class for all kinds of additive actions,
including (semi)modules and algebras.

Note that both `has_continuous_const_vadd α α` and `has_continuous_const_vadd αᵐᵒᵖ α` are
weaker versions of `has_continuous_add α`. -/
class ContinuousConstVAdd (Γ : Type _) (T : Type _) [TopologicalSpace T] [VAdd Γ T] : Prop where
  continuous_const_vadd : ∀ γ : Γ, Continuous fun x : T => γ +ᵥ x
#align has_continuous_const_vadd ContinuousConstVAdd
-/

attribute [to_additive] ContinuousConstSMul

export ContinuousConstSMul (continuous_const_smul)

export ContinuousConstVAdd (continuous_const_vadd)

variable {M α β : Type _}

section SMul

variable [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α]

#print Filter.Tendsto.const_smul /-
@[to_additive]
theorem Filter.Tendsto.const_smul {f : β → α} {l : Filter β} {a : α} (hf : Tendsto f l (𝓝 a))
    (c : M) : Tendsto (fun x => c • f x) l (𝓝 (c • a)) :=
  ((continuous_const_smul _).Tendsto _).comp hf
#align filter.tendsto.const_smul Filter.Tendsto.const_smul
#align filter.tendsto.const_vadd Filter.Tendsto.const_vadd
-/

variable [TopologicalSpace β] {f : β → M} {g : β → α} {b : β} {s : Set β}

#print ContinuousWithinAt.const_smul /-
@[to_additive]
theorem ContinuousWithinAt.const_smul (hg : ContinuousWithinAt g s b) (c : M) :
    ContinuousWithinAt (fun x => c • g x) s b :=
  hg.const_smul c
#align continuous_within_at.const_smul ContinuousWithinAt.const_smul
#align continuous_within_at.const_vadd ContinuousWithinAt.const_vadd
-/

#print ContinuousAt.const_smul /-
@[to_additive]
theorem ContinuousAt.const_smul (hg : ContinuousAt g b) (c : M) :
    ContinuousAt (fun x => c • g x) b :=
  hg.const_smul c
#align continuous_at.const_smul ContinuousAt.const_smul
#align continuous_at.const_vadd ContinuousAt.const_vadd
-/

#print ContinuousOn.const_smul /-
@[to_additive]
theorem ContinuousOn.const_smul (hg : ContinuousOn g s) (c : M) :
    ContinuousOn (fun x => c • g x) s := fun x hx => (hg x hx).const_smul c
#align continuous_on.const_smul ContinuousOn.const_smul
#align continuous_on.const_vadd ContinuousOn.const_vadd
-/

#print Continuous.const_smul /-
@[continuity, to_additive]
theorem Continuous.const_smul (hg : Continuous g) (c : M) : Continuous fun x => c • g x :=
  (continuous_const_smul _).comp hg
#align continuous.const_smul Continuous.const_smul
#align continuous.const_vadd Continuous.const_vadd
-/

#print ContinuousConstSMul.op /-
/-- If a scalar is central, then its right action is continuous when its left action is. -/
@[to_additive
      "If an additive action is central, then its right action is continuous when its left\naction is."]
instance ContinuousConstSMul.op [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] : ContinuousConstSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c => by simpa only [op_smul_eq_smul] using continuous_const_smul c⟩
#align has_continuous_const_smul.op ContinuousConstSMul.op
#align has_continuous_const_vadd.op ContinuousConstVAdd.op
-/

#print MulOpposite.continuousConstSMul /-
@[to_additive]
instance MulOpposite.continuousConstSMul : ContinuousConstSMul M αᵐᵒᵖ :=
  ⟨fun c => MulOpposite.continuous_op.comp <| MulOpposite.continuous_unop.const_smul c⟩
#align mul_opposite.has_continuous_const_smul MulOpposite.continuousConstSMul
#align add_opposite.has_continuous_const_vadd AddOpposite.continuousConstVAdd
-/

@[to_additive]
instance : ContinuousConstSMul M αᵒᵈ :=
  ‹ContinuousConstSMul M α›

#print OrderDual.continuousConstSMul' /-
@[to_additive]
instance OrderDual.continuousConstSMul' : ContinuousConstSMul Mᵒᵈ α :=
  ‹ContinuousConstSMul M α›
#align order_dual.has_continuous_const_smul' OrderDual.continuousConstSMul'
#align order_dual.has_continuous_const_vadd' OrderDual.continuousConstVAdd'
-/

@[to_additive]
instance [SMul M β] [ContinuousConstSMul M β] : ContinuousConstSMul M (α × β) :=
  ⟨fun _ => (continuous_fst.const_smul _).prod_mk (continuous_snd.const_smul _)⟩

@[to_additive]
instance {ι : Type _} {γ : ι → Type _} [∀ i, TopologicalSpace (γ i)] [∀ i, SMul M (γ i)]
    [∀ i, ContinuousConstSMul M (γ i)] : ContinuousConstSMul M (∀ i, γ i) :=
  ⟨fun _ => continuous_pi fun i => (continuous_apply i).const_smul _⟩

/- warning: is_compact.smul -> IsCompact.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : SMul.{u1, u2} α β] [_inst_6 : TopologicalSpace.{u2} β] [_inst_7 : ContinuousConstSMul.{u1, u2} α β _inst_6 _inst_5] (a : α) {s : Set.{u2} β}, (IsCompact.{u2} β _inst_6 s) -> (IsCompact.{u2} β _inst_6 (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_5) a s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_5 : SMul.{u2, u1} α β] [_inst_6 : TopologicalSpace.{u1} β] [_inst_7 : ContinuousConstSMul.{u2, u1} α β _inst_6 _inst_5] (a : α) {s : Set.{u1} β}, (IsCompact.{u1} β _inst_6 s) -> (IsCompact.{u1} β _inst_6 (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β _inst_5)) a s))
Case conversion may be inaccurate. Consider using '#align is_compact.smul IsCompact.smulₓ'. -/
@[to_additive]
theorem IsCompact.smul {α β} [SMul α β] [TopologicalSpace β] [ContinuousConstSMul α β] (a : α)
    {s : Set β} (hs : IsCompact s) : IsCompact (a • s) :=
  hs.image (continuous_id'.const_smul a)
#align is_compact.smul IsCompact.smul
#align is_compact.vadd IsCompact.vadd

end SMul

section Monoid

variable [TopologicalSpace α]

variable [Monoid M] [MulAction M α] [ContinuousConstSMul M α]

#print Units.continuousConstSMul /-
@[to_additive]
instance Units.continuousConstSMul : ContinuousConstSMul Mˣ α
    where continuous_const_smul m := (continuous_const_smul (m : M) : _)
#align units.has_continuous_const_smul Units.continuousConstSMul
#align add_units.has_continuous_const_vadd AddUnits.continuousConstVAdd
-/

#print smul_closure_subset /-
@[to_additive]
theorem smul_closure_subset (c : M) (s : Set α) : c • closure s ⊆ closure (c • s) :=
  ((Set.mapsTo_image _ _).closure <| continuous_id.const_smul c).image_subset
#align smul_closure_subset smul_closure_subset
#align vadd_closure_subset vadd_closure_subset
-/

#print smul_closure_orbit_subset /-
@[to_additive]
theorem smul_closure_orbit_subset (c : M) (x : α) :
    c • closure (MulAction.orbit M x) ⊆ closure (MulAction.orbit M x) :=
  (smul_closure_subset c _).trans <| closure_mono <| MulAction.smul_orbit_subset _ _
#align smul_closure_orbit_subset smul_closure_orbit_subset
#align vadd_closure_orbit_subset vadd_closure_orbit_subset
-/

end Monoid

section Group

variable {G : Type _} [TopologicalSpace α] [Group G] [MulAction G α] [ContinuousConstSMul G α]

/- warning: tendsto_const_smul_iff -> tendsto_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u3} G] [_inst_3 : MulAction.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G α _inst_1 (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3)] {f : β -> α} {l : Filter.{u2} β} {a : α} (c : G), Iff (Filter.Tendsto.{u2, u1} β α (fun (x : β) => SMul.smul.{u3, u1} G α (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3) c (f x)) l (nhds.{u1} α _inst_1 (SMul.smul.{u3, u1} G α (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3) c a))) (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] {f : β -> α} {l : Filter.{u3} β} {a : α} (c : G), Iff (Filter.Tendsto.{u3, u2} β α (fun (x : β) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c (f x)) l (nhds.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c a))) (Filter.Tendsto.{u3, u2} β α f l (nhds.{u2} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align tendsto_const_smul_iff tendsto_const_smul_iffₓ'. -/
@[to_additive]
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} (c : G) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul c⁻¹, fun h => h.const_smul _⟩
#align tendsto_const_smul_iff tendsto_const_smul_iff
#align tendsto_const_vadd_iff tendsto_const_vadd_iff

variable [TopologicalSpace β] {f : β → α} {b : β} {s : Set β}

/- warning: continuous_within_at_const_smul_iff -> continuousWithinAt_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u3} G] [_inst_3 : MulAction.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G α _inst_1 (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {s : Set.{u2} β} (c : G), Iff (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G α (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3) c (f x)) s b) (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_1 f s b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {b : β} {s : Set.{u3} β} (c : G), Iff (ContinuousWithinAt.{u3, u2} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c (f x)) s b) (ContinuousWithinAt.{u3, u2} β α _inst_5 _inst_1 f s b)
Case conversion may be inaccurate. Consider using '#align continuous_within_at_const_smul_iff continuousWithinAt_const_smul_iffₓ'. -/
@[to_additive]
theorem continuousWithinAt_const_smul_iff (c : G) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff c
#align continuous_within_at_const_smul_iff continuousWithinAt_const_smul_iff
#align continuous_within_at_const_vadd_iff continuousWithinAt_const_vadd_iff

/- warning: continuous_on_const_smul_iff -> continuousOn_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u3} G] [_inst_3 : MulAction.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G α _inst_1 (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {s : Set.{u2} β} (c : G), Iff (ContinuousOn.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G α (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3) c (f x)) s) (ContinuousOn.{u2, u1} β α _inst_5 _inst_1 f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {s : Set.{u3} β} (c : G), Iff (ContinuousOn.{u3, u2} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c (f x)) s) (ContinuousOn.{u3, u2} β α _inst_5 _inst_1 f s)
Case conversion may be inaccurate. Consider using '#align continuous_on_const_smul_iff continuousOn_const_smul_iffₓ'. -/
@[to_additive]
theorem continuousOn_const_smul_iff (c : G) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  forall₂_congr fun b hb => continuousWithinAt_const_smul_iff c
#align continuous_on_const_smul_iff continuousOn_const_smul_iff
#align continuous_on_const_vadd_iff continuousOn_const_vadd_iff

/- warning: continuous_at_const_smul_iff -> continuousAt_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u3} G] [_inst_3 : MulAction.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G α _inst_1 (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} (c : G), Iff (ContinuousAt.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G α (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3) c (f x)) b) (ContinuousAt.{u2, u1} β α _inst_5 _inst_1 f b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {b : β} (c : G), Iff (ContinuousAt.{u3, u2} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c (f x)) b) (ContinuousAt.{u3, u2} β α _inst_5 _inst_1 f b)
Case conversion may be inaccurate. Consider using '#align continuous_at_const_smul_iff continuousAt_const_smul_iffₓ'. -/
@[to_additive]
theorem continuousAt_const_smul_iff (c : G) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  tendsto_const_smul_iff c
#align continuous_at_const_smul_iff continuousAt_const_smul_iff
#align continuous_at_const_vadd_iff continuousAt_const_vadd_iff

/- warning: continuous_const_smul_iff -> continuous_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u3} G] [_inst_3 : MulAction.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G α _inst_1 (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} (c : G), Iff (Continuous.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G α (MulAction.toHasSmul.{u3, u1} G α (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_2)) _inst_3) c (f x))) (Continuous.{u2, u1} β α _inst_5 _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} (c : G), Iff (Continuous.{u3, u2} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c (f x))) (Continuous.{u3, u2} β α _inst_5 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align continuous_const_smul_iff continuous_const_smul_iffₓ'. -/
@[to_additive]
theorem continuous_const_smul_iff (c : G) : (Continuous fun x => c • f x) ↔ Continuous f := by
  simp only [continuous_iff_continuousAt, continuousAt_const_smul_iff]
#align continuous_const_smul_iff continuous_const_smul_iff
#align continuous_const_vadd_iff continuous_const_vadd_iff

#print Homeomorph.smul /-
/-- The homeomorphism given by scalar multiplication by a given element of a group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
@[to_additive]
def Homeomorph.smul (γ : G) : α ≃ₜ α
    where
  toEquiv := MulAction.toPerm γ
  continuous_toFun := continuous_const_smul γ
  continuous_invFun := continuous_const_smul γ⁻¹
#align homeomorph.smul Homeomorph.smul
#align homeomorph.vadd Homeomorph.vadd
-/

/-- The homeomorphism given by affine-addition by an element of an additive group `Γ` acting on
  `T` is a homeomorphism from `T` to itself. -/
add_decl_doc Homeomorph.vadd

/- warning: is_open_map_smul -> isOpenMap_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (c : G), IsOpenMap.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => SMul.smul.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) c x)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G), IsOpenMap.{u2, u2} α α _inst_1 _inst_1 (fun (x : α) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c x)
Case conversion may be inaccurate. Consider using '#align is_open_map_smul isOpenMap_smulₓ'. -/
@[to_additive]
theorem isOpenMap_smul (c : G) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smul c).IsOpenMap
#align is_open_map_smul isOpenMap_smul
#align is_open_map_vadd isOpenMap_vadd

/- warning: is_open.smul -> IsOpen.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (forall (c : G), IsOpen.{u1} α _inst_1 (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c s))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (forall (c : G), IsOpen.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c s))
Case conversion may be inaccurate. Consider using '#align is_open.smul IsOpen.smulₓ'. -/
@[to_additive]
theorem IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c • s) :=
  isOpenMap_smul c s hs
#align is_open.smul IsOpen.smul
#align is_open.vadd IsOpen.vadd

/- warning: is_closed_map_smul -> isClosedMap_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (c : G), IsClosedMap.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => SMul.smul.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3) c x)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G), IsClosedMap.{u2, u2} α α _inst_1 _inst_1 (fun (x : α) => HSMul.hSMul.{u1, u2, u2} G α α (instHSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)) c x)
Case conversion may be inaccurate. Consider using '#align is_closed_map_smul isClosedMap_smulₓ'. -/
@[to_additive]
theorem isClosedMap_smul (c : G) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smul c).IsClosedMap
#align is_closed_map_smul isClosedMap_smul
#align is_closed_map_vadd isClosedMap_vadd

/- warning: is_closed.smul -> IsClosed.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] {s : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (forall (c : G), IsClosed.{u1} α _inst_1 (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c s))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] {s : Set.{u2} α}, (IsClosed.{u2} α _inst_1 s) -> (forall (c : G), IsClosed.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c s))
Case conversion may be inaccurate. Consider using '#align is_closed.smul IsClosed.smulₓ'. -/
@[to_additive]
theorem IsClosed.smul {s : Set α} (hs : IsClosed s) (c : G) : IsClosed (c • s) :=
  isClosedMap_smul c s hs
#align is_closed.smul IsClosed.smul
#align is_closed.vadd IsClosed.vadd

/- warning: closure_smul -> closure_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (c : G) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (closure.{u1} α _inst_1 (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c s)) (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c (closure.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (closure.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c s)) (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c (closure.{u2} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align closure_smul closure_smulₓ'. -/
@[to_additive]
theorem closure_smul (c : G) (s : Set α) : closure (c • s) = c • closure s :=
  ((Homeomorph.smul c).image_closure s).symm
#align closure_smul closure_smul
#align closure_vadd closure_vadd

/- warning: dense.smul -> Dense.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (c : G) {s : Set.{u1} α}, (Dense.{u1} α _inst_1 s) -> (Dense.{u1} α _inst_1 (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c s))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) {s : Set.{u2} α}, (Dense.{u2} α _inst_1 s) -> (Dense.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c s))
Case conversion may be inaccurate. Consider using '#align dense.smul Dense.smulₓ'. -/
@[to_additive]
theorem Dense.smul (c : G) {s : Set α} (hs : Dense s) : Dense (c • s) := by
  rw [dense_iff_closure_eq] at hs⊢ <;> rw [closure_smul, hs, smul_set_univ]
#align dense.smul Dense.smul
#align dense.vadd Dense.vadd

/- warning: interior_smul -> interior_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : Group.{u2} G] [_inst_3 : MulAction.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G α _inst_1 (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)] (c : G) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c s)) (SMul.smul.{u2, u1} G (Set.{u1} α) (Set.smulSet.{u2, u1} G α (MulAction.toHasSmul.{u2, u1} G α (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_2)) _inst_3)) c (interior.{u1} α _inst_1 s))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : Group.{u1} G] [_inst_3 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G α _inst_1 (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3)] (c : G) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (interior.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c s)) (HSMul.hSMul.{u1, u2, u2} G (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G (Set.{u2} α) (Set.smulSet.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_2)) _inst_3))) c (interior.{u2} α _inst_1 s))
Case conversion may be inaccurate. Consider using '#align interior_smul interior_smulₓ'. -/
@[to_additive]
theorem interior_smul (c : G) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smul c).image_interior s).symm
#align interior_smul interior_smul
#align interior_vadd interior_vadd

end Group

section GroupWithZero

variable {G₀ : Type _} [TopologicalSpace α] [GroupWithZero G₀] [MulAction G₀ α]
  [ContinuousConstSMul G₀ α]

/- warning: tendsto_const_smul_iff₀ -> tendsto_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] {f : β -> α} {l : Filter.{u2} β} {a : α} {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)))))))) -> (Iff (Filter.Tendsto.{u2, u1} β α (fun (x : β) => SMul.smul.{u3, u1} G₀ α (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3) c (f x)) l (nhds.{u1} α _inst_1 (SMul.smul.{u3, u1} G₀ α (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3) c a))) (Filter.Tendsto.{u2, u1} β α f l (nhds.{u1} α _inst_1 a)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {f : β -> α} {l : Filter.{u3} β} {a : α} {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))))) -> (Iff (Filter.Tendsto.{u3, u1} β α (fun (x : β) => HSMul.hSMul.{u2, u1, u1} G₀ α α (instHSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c (f x)) l (nhds.{u1} α _inst_1 (HSMul.hSMul.{u2, u1, u1} G₀ α α (instHSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c a))) (Filter.Tendsto.{u3, u1} β α f l (nhds.{u1} α _inst_1 a)))
Case conversion may be inaccurate. Consider using '#align tendsto_const_smul_iff₀ tendsto_const_smul_iff₀ₓ'. -/
theorem tendsto_const_smul_iff₀ {f : β → α} {l : Filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  tendsto_const_smul_iff (Units.mk0 c hc)
#align tendsto_const_smul_iff₀ tendsto_const_smul_iff₀

variable [TopologicalSpace β] {f : β → α} {b : β} {c : G₀} {s : Set β}

/- warning: continuous_within_at_const_smul_iff₀ -> continuousWithinAt_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {c : G₀} {s : Set.{u2} β}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)))))))) -> (Iff (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G₀ α (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3) c (f x)) s b) (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_1 f s b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {c : G₀} {s : Set.{u2} β}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))))) -> (Iff (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} G₀ α α (instHSMul.{u3, u1} G₀ α (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)) c (f x)) s b) (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_1 f s b))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_const_smul_iff₀ continuousWithinAt_const_smul_iff₀ₓ'. -/
theorem continuousWithinAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  tendsto_const_smul_iff (Units.mk0 c hc)
#align continuous_within_at_const_smul_iff₀ continuousWithinAt_const_smul_iff₀

/- warning: continuous_on_const_smul_iff₀ -> continuousOn_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {c : G₀} {s : Set.{u2} β}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)))))))) -> (Iff (ContinuousOn.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G₀ α (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3) c (f x)) s) (ContinuousOn.{u2, u1} β α _inst_5 _inst_1 f s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {c : G₀} {s : Set.{u2} β}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))))) -> (Iff (ContinuousOn.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} G₀ α α (instHSMul.{u3, u1} G₀ α (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)) c (f x)) s) (ContinuousOn.{u2, u1} β α _inst_5 _inst_1 f s))
Case conversion may be inaccurate. Consider using '#align continuous_on_const_smul_iff₀ continuousOn_const_smul_iff₀ₓ'. -/
theorem continuousOn_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  continuousOn_const_smul_iff (Units.mk0 c hc)
#align continuous_on_const_smul_iff₀ continuousOn_const_smul_iff₀

/- warning: continuous_at_const_smul_iff₀ -> continuousAt_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)))))))) -> (Iff (ContinuousAt.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G₀ α (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3) c (f x)) b) (ContinuousAt.{u2, u1} β α _inst_5 _inst_1 f b))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))))) -> (Iff (ContinuousAt.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} G₀ α α (instHSMul.{u3, u1} G₀ α (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)) c (f x)) b) (ContinuousAt.{u2, u1} β α _inst_5 _inst_1 f b))
Case conversion may be inaccurate. Consider using '#align continuous_at_const_smul_iff₀ continuousAt_const_smul_iff₀ₓ'. -/
theorem continuousAt_const_smul_iff₀ (hc : c ≠ 0) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  continuousAt_const_smul_iff (Units.mk0 c hc)
#align continuous_at_const_smul_iff₀ continuousAt_const_smul_iff₀

/- warning: continuous_const_smul_iff₀ -> continuous_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)))))))) -> (Iff (Continuous.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => SMul.smul.{u3, u1} G₀ α (MulAction.toHasSmul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3) c (f x))) (Continuous.{u2, u1} β α _inst_5 _inst_1 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {G₀ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u3} G₀] [_inst_3 : MulAction.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u3, u1} G₀ α _inst_1 (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2))))) -> (Iff (Continuous.{u2, u1} β α _inst_5 _inst_1 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} G₀ α α (instHSMul.{u3, u1} G₀ α (MulAction.toSMul.{u3, u1} G₀ α (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_2)) _inst_3)) c (f x))) (Continuous.{u2, u1} β α _inst_5 _inst_1 f))
Case conversion may be inaccurate. Consider using '#align continuous_const_smul_iff₀ continuous_const_smul_iff₀ₓ'. -/
theorem continuous_const_smul_iff₀ (hc : c ≠ 0) : (Continuous fun x => c • f x) ↔ Continuous f :=
  continuous_const_smul_iff (Units.mk0 c hc)
#align continuous_const_smul_iff₀ continuous_const_smul_iff₀

/- warning: homeomorph.smul_of_ne_zero -> Homeomorph.smulOfNeZero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] (c : G₀), (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (Homeomorph.{u1, u1} α α _inst_1 _inst_1)
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] (c : G₀), (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))))) -> (Homeomorph.{u1, u1} α α _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.smul_of_ne_zero Homeomorph.smulOfNeZeroₓ'. -/
/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
protected def Homeomorph.smulOfNeZero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
  Homeomorph.smul (Units.mk0 c hc)
#align homeomorph.smul_of_ne_zero Homeomorph.smulOfNeZero

/- warning: is_open_map_smul₀ -> isOpenMap_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (IsOpenMap.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => SMul.smul.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3) c x))
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))))) -> (IsOpenMap.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => HSMul.hSMul.{u2, u1, u1} G₀ α α (instHSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c x))
Case conversion may be inaccurate. Consider using '#align is_open_map_smul₀ isOpenMap_smul₀ₓ'. -/
theorem isOpenMap_smul₀ {c : G₀} (hc : c ≠ 0) : IsOpenMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).IsOpenMap
#align is_open_map_smul₀ isOpenMap_smul₀

/- warning: is_open.smul₀ -> IsOpen.smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀} {s : Set.{u1} α}, (IsOpen.{u1} α _inst_1 s) -> (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (IsOpen.{u1} α _inst_1 (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c s))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : GroupWithZero.{u1} G₀] [_inst_3 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G₀ α _inst_1 (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3)] {c : G₀} {s : Set.{u2} α}, (IsOpen.{u2} α _inst_1 s) -> (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (IsOpen.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G₀ (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3))) c s))
Case conversion may be inaccurate. Consider using '#align is_open.smul₀ IsOpen.smul₀ₓ'. -/
theorem IsOpen.smul₀ {c : G₀} {s : Set α} (hs : IsOpen s) (hc : c ≠ 0) : IsOpen (c • s) :=
  isOpenMap_smul₀ hc s hs
#align is_open.smul₀ IsOpen.smul₀

/- warning: interior_smul₀ -> interior_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c s)) (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c (interior.{u1} α _inst_1 s)))
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))))) -> (forall (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (interior.{u1} α _inst_1 (HSMul.hSMul.{u2, u1, u1} G₀ (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3))) c s)) (HSMul.hSMul.{u2, u1, u1} G₀ (Set.{u1} α) (Set.{u1} α) (instHSMul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3))) c (interior.{u1} α _inst_1 s)))
Case conversion may be inaccurate. Consider using '#align interior_smul₀ interior_smul₀ₓ'. -/
theorem interior_smul₀ {c : G₀} (hc : c ≠ 0) (s : Set α) : interior (c • s) = c • interior s :=
  ((Homeomorph.smulOfNeZero c hc).image_interior s).symm
#align interior_smul₀ interior_smul₀

#print closure_smul₀ /-
theorem closure_smul₀ {E} [Zero E] [MulActionWithZero G₀ E] [TopologicalSpace E] [T1Space E]
    [ContinuousConstSMul G₀ E] (c : G₀) (s : Set E) : closure (c • s) = c • closure s :=
  by
  rcases eq_or_ne c 0 with (rfl | hc)
  · rcases eq_empty_or_nonempty s with (rfl | hs)
    · simp
    · rw [zero_smul_set hs, zero_smul_set hs.closure]
      exact closure_singleton
  · exact ((Homeomorph.smulOfNeZero c hc).image_closure s).symm
#align closure_smul₀ closure_smul₀
-/

/- warning: is_closed_map_smul_of_ne_zero -> isClosedMap_smul_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (IsClosedMap.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => SMul.smul.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3) c x))
but is expected to have type
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (Zero.toOfNat0.{u2} G₀ (MonoidWithZero.toZero.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))))) -> (IsClosedMap.{u1, u1} α α _inst_1 _inst_1 (fun (x : α) => HSMul.hSMul.{u2, u1, u1} G₀ α α (instHSMul.{u2, u1} G₀ α (MulAction.toSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c x))
Case conversion may be inaccurate. Consider using '#align is_closed_map_smul_of_ne_zero isClosedMap_smul_of_ne_zeroₓ'. -/
/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem isClosedMap_smul_of_ne_zero {c : G₀} (hc : c ≠ 0) : IsClosedMap fun x : α => c • x :=
  (Homeomorph.smulOfNeZero c hc).IsClosedMap
#align is_closed_map_smul_of_ne_zero isClosedMap_smul_of_ne_zero

/- warning: is_closed.smul_of_ne_zero -> IsClosed.smul_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {c : G₀} {s : Set.{u1} α}, (IsClosed.{u1} α _inst_1 s) -> (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (IsClosed.{u1} α _inst_1 (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)) c s))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : GroupWithZero.{u1} G₀] [_inst_3 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G₀ α _inst_1 (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3)] {c : G₀} {s : Set.{u2} α}, (IsClosed.{u2} α _inst_1 s) -> (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (IsClosed.{u2} α _inst_1 (HSMul.hSMul.{u1, u2, u2} G₀ (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3))) c s))
Case conversion may be inaccurate. Consider using '#align is_closed.smul_of_ne_zero IsClosed.smul_of_ne_zeroₓ'. -/
theorem IsClosed.smul_of_ne_zero {c : G₀} {s : Set α} (hs : IsClosed s) (hc : c ≠ 0) :
    IsClosed (c • s) :=
  isClosedMap_smul_of_ne_zero hc s hs
#align is_closed.smul_of_ne_zero IsClosed.smul_of_ne_zero

/- warning: is_closed_map_smul₀ -> isClosedMap_smul₀ is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {M : Type.{u2}} [_inst_6 : DivisionRing.{u1} 𝕜] [_inst_7 : AddCommMonoid.{u2} M] [_inst_8 : TopologicalSpace.{u2} M] [_inst_9 : T1Space.{u2} M _inst_8] [_inst_10 : Module.{u1, u2} 𝕜 M (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)) _inst_7] [_inst_11 : ContinuousConstSMul.{u1, u2} 𝕜 M _inst_8 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 M (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 M (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (Module.toMulActionWithZero.{u1, u2} 𝕜 M (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)) _inst_7 _inst_10))))] (c : 𝕜), IsClosedMap.{u2, u2} M M _inst_8 _inst_8 (fun (x : M) => SMul.smul.{u1, u2} 𝕜 M (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 M (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 M (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (Module.toMulActionWithZero.{u1, u2} 𝕜 M (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)) _inst_7 _inst_10)))) c x)
but is expected to have type
  forall {𝕜 : Type.{u2}} {M : Type.{u1}} [_inst_6 : DivisionRing.{u2} 𝕜] [_inst_7 : AddCommMonoid.{u1} M] [_inst_8 : TopologicalSpace.{u1} M] [_inst_9 : T1Space.{u1} M _inst_8] [_inst_10 : Module.{u2, u1} 𝕜 M (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)) _inst_7] [_inst_11 : ContinuousConstSMul.{u2, u1} 𝕜 M _inst_8 (SMulZeroClass.toSMul.{u2, u1} 𝕜 M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 M (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 M (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (Module.toMulActionWithZero.{u2, u1} 𝕜 M (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)) _inst_7 _inst_10))))] (c : 𝕜), IsClosedMap.{u1, u1} M M _inst_8 _inst_8 (fun (x : M) => HSMul.hSMul.{u2, u1, u1} 𝕜 M M (instHSMul.{u2, u1} 𝕜 M (SMulZeroClass.toSMul.{u2, u1} 𝕜 M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 M (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 M (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (Module.toMulActionWithZero.{u2, u1} 𝕜 M (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)) _inst_7 _inst_10))))) c x)
Case conversion may be inaccurate. Consider using '#align is_closed_map_smul₀ isClosedMap_smul₀ₓ'. -/
/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
theorem isClosedMap_smul₀ {𝕜 M : Type _} [DivisionRing 𝕜] [AddCommMonoid M] [TopologicalSpace M]
    [T1Space M] [Module 𝕜 M] [ContinuousConstSMul 𝕜 M] (c : 𝕜) : IsClosedMap fun x : M => c • x :=
  by
  rcases eq_or_ne c 0 with (rfl | hne)
  · simp only [zero_smul]
    exact isClosedMap_const
  · exact (Homeomorph.smulOfNeZero c hne).IsClosedMap
#align is_closed_map_smul₀ isClosedMap_smul₀

/- warning: is_closed.smul₀ -> IsClosed.smul₀ is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {M : Type.{u2}} [_inst_6 : DivisionRing.{u1} 𝕜] [_inst_7 : AddCommMonoid.{u2} M] [_inst_8 : TopologicalSpace.{u2} M] [_inst_9 : T1Space.{u2} M _inst_8] [_inst_10 : Module.{u1, u2} 𝕜 M (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)) _inst_7] [_inst_11 : ContinuousConstSMul.{u1, u2} 𝕜 M _inst_8 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 M (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 M (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (Module.toMulActionWithZero.{u1, u2} 𝕜 M (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)) _inst_7 _inst_10))))] (c : 𝕜) {s : Set.{u2} M}, (IsClosed.{u2} M _inst_8 s) -> (IsClosed.{u2} M _inst_8 (SMul.smul.{u1, u2} 𝕜 (Set.{u2} M) (Set.smulSet.{u1, u2} 𝕜 M (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 M (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 M (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_7))) (Module.toMulActionWithZero.{u1, u2} 𝕜 M (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 _inst_6)) _inst_7 _inst_10))))) c s))
but is expected to have type
  forall {𝕜 : Type.{u2}} {M : Type.{u1}} [_inst_6 : DivisionRing.{u2} 𝕜] [_inst_7 : AddCommMonoid.{u1} M] [_inst_8 : TopologicalSpace.{u1} M] [_inst_9 : T1Space.{u1} M _inst_8] [_inst_10 : Module.{u2, u1} 𝕜 M (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)) _inst_7] [_inst_11 : ContinuousConstSMul.{u2, u1} 𝕜 M _inst_8 (SMulZeroClass.toSMul.{u2, u1} 𝕜 M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 M (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 M (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (Module.toMulActionWithZero.{u2, u1} 𝕜 M (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)) _inst_7 _inst_10))))] (c : 𝕜) {s : Set.{u1} M}, (IsClosed.{u1} M _inst_8 s) -> (IsClosed.{u1} M _inst_8 (HSMul.hSMul.{u2, u1, u1} 𝕜 (Set.{u1} M) (Set.{u1} M) (instHSMul.{u2, u1} 𝕜 (Set.{u1} M) (Set.smulSet.{u2, u1} 𝕜 M (SMulZeroClass.toSMul.{u2, u1} 𝕜 M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 M (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 M (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_7)) (Module.toMulActionWithZero.{u2, u1} 𝕜 M (DivisionSemiring.toSemiring.{u2} 𝕜 (DivisionRing.toDivisionSemiring.{u2} 𝕜 _inst_6)) _inst_7 _inst_10)))))) c s))
Case conversion may be inaccurate. Consider using '#align is_closed.smul₀ IsClosed.smul₀ₓ'. -/
theorem IsClosed.smul₀ {𝕜 M : Type _} [DivisionRing 𝕜] [AddCommMonoid M] [TopologicalSpace M]
    [T1Space M] [Module 𝕜 M] [ContinuousConstSMul 𝕜 M] (c : 𝕜) {s : Set M} (hs : IsClosed s) :
    IsClosed (c • s) :=
  isClosedMap_smul₀ c s hs
#align is_closed.smul₀ IsClosed.smul₀

/- warning: has_compact_mul_support.comp_smul -> HasCompactMulSupport.comp_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {β : Type.{u3}} [_inst_6 : One.{u3} β] {f : α -> β}, (HasCompactMulSupport.{u1, u3} α β _inst_1 _inst_6 f) -> (forall {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (HasCompactMulSupport.{u1, u3} α β _inst_1 _inst_6 (fun (x : α) => f (SMul.smul.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3) c x))))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : GroupWithZero.{u1} G₀] [_inst_3 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G₀ α _inst_1 (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3)] {β : Type.{u3}} [_inst_6 : One.{u3} β] {f : α -> β}, (HasCompactMulSupport.{u2, u3} α β _inst_1 _inst_6 f) -> (forall {c : G₀}, (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (HasCompactMulSupport.{u2, u3} α β _inst_1 _inst_6 (fun (x : α) => f (HSMul.hSMul.{u1, u2, u2} G₀ α α (instHSMul.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3)) c x))))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.comp_smul HasCompactMulSupport.comp_smulₓ'. -/
theorem HasCompactMulSupport.comp_smul {β : Type _} [One β] {f : α → β} (h : HasCompactMulSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactMulSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)
#align has_compact_mul_support.comp_smul HasCompactMulSupport.comp_smul

/- warning: has_compact_support.comp_smul -> HasCompactSupport.comp_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : GroupWithZero.{u2} G₀] [_inst_3 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u2, u1} G₀ α _inst_1 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3)] {β : Type.{u3}} [_inst_6 : Zero.{u3} β] {f : α -> β}, (HasCompactSupport.{u1, u3} α β _inst_1 _inst_6 f) -> (forall {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)))))))) -> (HasCompactSupport.{u1, u3} α β _inst_1 _inst_6 (fun (x : α) => f (SMul.smul.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_2)) _inst_3) c x))))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : GroupWithZero.{u1} G₀] [_inst_3 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))] [_inst_4 : ContinuousConstSMul.{u1, u2} G₀ α _inst_1 (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3)] {β : Type.{u3}} [_inst_6 : Zero.{u3} β] {f : α -> β}, (HasCompactSupport.{u2, u3} α β _inst_1 _inst_6 f) -> (forall {c : G₀}, (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (HasCompactSupport.{u2, u3} α β _inst_1 _inst_6 (fun (x : α) => f (HSMul.hSMul.{u1, u2, u2} G₀ α α (instHSMul.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) _inst_3)) c x))))
Case conversion may be inaccurate. Consider using '#align has_compact_support.comp_smul HasCompactSupport.comp_smulₓ'. -/
theorem HasCompactSupport.comp_smul {β : Type _} [Zero β] {f : α → β} (h : HasCompactSupport f)
    {c : G₀} (hc : c ≠ 0) : HasCompactSupport fun x => f (c • x) :=
  h.comp_homeomorph (Homeomorph.smulOfNeZero c hc)
#align has_compact_support.comp_smul HasCompactSupport.comp_smul

attribute [to_additive HasCompactSupport.comp_smul] HasCompactMulSupport.comp_smul

end GroupWithZero

namespace IsUnit

variable [Monoid M] [TopologicalSpace α] [MulAction M α] [ContinuousConstSMul M α]

/- warning: is_unit.tendsto_const_smul_iff -> IsUnit.tendsto_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] {f : β -> α} {l : Filter.{u3} β} {a : α} {c : M}, (IsUnit.{u1} M _inst_1 c) -> (Iff (Filter.Tendsto.{u3, u2} β α (fun (x : β) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c (f x)) l (nhds.{u2} α _inst_2 (SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c a))) (Filter.Tendsto.{u3, u2} β α f l (nhds.{u2} α _inst_2 a)))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : Monoid.{u2} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u2, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u2, u1} M α _inst_2 (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)] {f : β -> α} {l : Filter.{u3} β} {a : α} {c : M}, (IsUnit.{u2} M _inst_1 c) -> (Iff (Filter.Tendsto.{u3, u1} β α (fun (x : β) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)) c (f x)) l (nhds.{u1} α _inst_2 (HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)) c a))) (Filter.Tendsto.{u3, u1} β α f l (nhds.{u1} α _inst_2 a)))
Case conversion may be inaccurate. Consider using '#align is_unit.tendsto_const_smul_iff IsUnit.tendsto_const_smul_iffₓ'. -/
theorem tendsto_const_smul_iff {f : β → α} {l : Filter β} {a : α} {c : M} (hc : IsUnit c) :
    Tendsto (fun x => c • f x) l (𝓝 <| c • a) ↔ Tendsto f l (𝓝 a) :=
  let ⟨u, hu⟩ := hc
  hu ▸ tendsto_const_smul_iff u
#align is_unit.tendsto_const_smul_iff IsUnit.tendsto_const_smul_iff

variable [TopologicalSpace β] {f : β → α} {b : β} {c : M} {s : Set β}

/- warning: is_unit.continuous_within_at_const_smul_iff -> IsUnit.continuousWithinAt_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {b : β} {c : M} {s : Set.{u3} β}, (IsUnit.{u1} M _inst_1 c) -> (Iff (ContinuousWithinAt.{u3, u2} β α _inst_5 _inst_2 (fun (x : β) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c (f x)) s b) (ContinuousWithinAt.{u3, u2} β α _inst_5 _inst_2 f s b))
but is expected to have type
  forall {M : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u3} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u3, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u3, u1} M α _inst_2 (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {c : M} {s : Set.{u2} β}, (IsUnit.{u3} M _inst_1 c) -> (Iff (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} M α α (instHSMul.{u3, u1} M α (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)) c (f x)) s b) (ContinuousWithinAt.{u2, u1} β α _inst_5 _inst_2 f s b))
Case conversion may be inaccurate. Consider using '#align is_unit.continuous_within_at_const_smul_iff IsUnit.continuousWithinAt_const_smul_iffₓ'. -/
theorem continuousWithinAt_const_smul_iff (hc : IsUnit c) :
    ContinuousWithinAt (fun x => c • f x) s b ↔ ContinuousWithinAt f s b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuousWithinAt_const_smul_iff u
#align is_unit.continuous_within_at_const_smul_iff IsUnit.continuousWithinAt_const_smul_iff

/- warning: is_unit.continuous_on_const_smul_iff -> IsUnit.continuousOn_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {c : M} {s : Set.{u3} β}, (IsUnit.{u1} M _inst_1 c) -> (Iff (ContinuousOn.{u3, u2} β α _inst_5 _inst_2 (fun (x : β) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c (f x)) s) (ContinuousOn.{u3, u2} β α _inst_5 _inst_2 f s))
but is expected to have type
  forall {M : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u3} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u3, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u3, u1} M α _inst_2 (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {c : M} {s : Set.{u2} β}, (IsUnit.{u3} M _inst_1 c) -> (Iff (ContinuousOn.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} M α α (instHSMul.{u3, u1} M α (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)) c (f x)) s) (ContinuousOn.{u2, u1} β α _inst_5 _inst_2 f s))
Case conversion may be inaccurate. Consider using '#align is_unit.continuous_on_const_smul_iff IsUnit.continuousOn_const_smul_iffₓ'. -/
theorem continuousOn_const_smul_iff (hc : IsUnit c) :
    ContinuousOn (fun x => c • f x) s ↔ ContinuousOn f s :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuousOn_const_smul_iff u
#align is_unit.continuous_on_const_smul_iff IsUnit.continuousOn_const_smul_iff

/- warning: is_unit.continuous_at_const_smul_iff -> IsUnit.continuousAt_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {b : β} {c : M}, (IsUnit.{u1} M _inst_1 c) -> (Iff (ContinuousAt.{u3, u2} β α _inst_5 _inst_2 (fun (x : β) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c (f x)) b) (ContinuousAt.{u3, u2} β α _inst_5 _inst_2 f b))
but is expected to have type
  forall {M : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u3} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u3, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u3, u1} M α _inst_2 (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {b : β} {c : M}, (IsUnit.{u3} M _inst_1 c) -> (Iff (ContinuousAt.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} M α α (instHSMul.{u3, u1} M α (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)) c (f x)) b) (ContinuousAt.{u2, u1} β α _inst_5 _inst_2 f b))
Case conversion may be inaccurate. Consider using '#align is_unit.continuous_at_const_smul_iff IsUnit.continuousAt_const_smul_iffₓ'. -/
theorem continuousAt_const_smul_iff (hc : IsUnit c) :
    ContinuousAt (fun x => c • f x) b ↔ ContinuousAt f b :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuousAt_const_smul_iff u
#align is_unit.continuous_at_const_smul_iff IsUnit.continuousAt_const_smul_iff

/- warning: is_unit.continuous_const_smul_iff -> IsUnit.continuous_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u3} β] {f : β -> α} {c : M}, (IsUnit.{u1} M _inst_1 c) -> (Iff (Continuous.{u3, u2} β α _inst_5 _inst_2 (fun (x : β) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c (f x))) (Continuous.{u3, u2} β α _inst_5 _inst_2 f))
but is expected to have type
  forall {M : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u3} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u3, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u3, u1} M α _inst_2 (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)] [_inst_5 : TopologicalSpace.{u2} β] {f : β -> α} {c : M}, (IsUnit.{u3} M _inst_1 c) -> (Iff (Continuous.{u2, u1} β α _inst_5 _inst_2 (fun (x : β) => HSMul.hSMul.{u3, u1, u1} M α α (instHSMul.{u3, u1} M α (MulAction.toSMul.{u3, u1} M α _inst_1 _inst_3)) c (f x))) (Continuous.{u2, u1} β α _inst_5 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align is_unit.continuous_const_smul_iff IsUnit.continuous_const_smul_iffₓ'. -/
theorem continuous_const_smul_iff (hc : IsUnit c) : (Continuous fun x => c • f x) ↔ Continuous f :=
  let ⟨u, hu⟩ := hc
  hu ▸ continuous_const_smul_iff u
#align is_unit.continuous_const_smul_iff IsUnit.continuous_const_smul_iff

/- warning: is_unit.is_open_map_smul -> IsUnit.isOpenMap_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] {c : M}, (IsUnit.{u1} M _inst_1 c) -> (IsOpenMap.{u2, u2} α α _inst_2 _inst_2 (fun (x : α) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c x))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u2, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u2, u1} M α _inst_2 (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)] {c : M}, (IsUnit.{u2} M _inst_1 c) -> (IsOpenMap.{u1, u1} α α _inst_2 _inst_2 (fun (x : α) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)) c x))
Case conversion may be inaccurate. Consider using '#align is_unit.is_open_map_smul IsUnit.isOpenMap_smulₓ'. -/
theorem isOpenMap_smul (hc : IsUnit c) : IsOpenMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ isOpenMap_smul u
#align is_unit.is_open_map_smul IsUnit.isOpenMap_smul

/- warning: is_unit.is_closed_map_smul -> IsUnit.isClosedMap_smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u1, u2} M α _inst_2 (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3)] {c : M}, (IsUnit.{u1} M _inst_1 c) -> (IsClosedMap.{u2, u2} α α _inst_2 _inst_2 (fun (x : α) => SMul.smul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_1 _inst_3) c x))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : MulAction.{u2, u1} M α _inst_1] [_inst_4 : ContinuousConstSMul.{u2, u1} M α _inst_2 (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)] {c : M}, (IsUnit.{u2} M _inst_1 c) -> (IsClosedMap.{u1, u1} α α _inst_2 _inst_2 (fun (x : α) => HSMul.hSMul.{u2, u1, u1} M α α (instHSMul.{u2, u1} M α (MulAction.toSMul.{u2, u1} M α _inst_1 _inst_3)) c x))
Case conversion may be inaccurate. Consider using '#align is_unit.is_closed_map_smul IsUnit.isClosedMap_smulₓ'. -/
theorem isClosedMap_smul (hc : IsUnit c) : IsClosedMap fun x : α => c • x :=
  let ⟨u, hu⟩ := hc
  hu ▸ isClosedMap_smul u
#align is_unit.is_closed_map_smul IsUnit.isClosedMap_smul

end IsUnit

#print ProperlyDiscontinuousSMul /-
/-- Class `properly_discontinuous_smul Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousSMul (Γ : Type _) (T : Type _) [TopologicalSpace T] [SMul Γ T] :
  Prop where
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (· • ·) γ '' K ∩ L ≠ ∅ }
#align properly_discontinuous_smul ProperlyDiscontinuousSMul
-/

#print ProperlyDiscontinuousVAdd /-
/-- Class `properly_discontinuous_vadd Γ T` says that the additive action `(+ᵥ) : Γ → T → T`
is properly discontinuous, that is, for any pair of compact sets `K, L` in `T`, only finitely many
`γ:Γ` move `K` to have nontrivial intersection with `L`.
-/
class ProperlyDiscontinuousVAdd (Γ : Type _) (T : Type _) [TopologicalSpace T] [VAdd Γ T] :
  Prop where
  finite_disjoint_inter_image :
    ∀ {K L : Set T}, IsCompact K → IsCompact L → Set.Finite { γ : Γ | (· +ᵥ ·) γ '' K ∩ L ≠ ∅ }
#align properly_discontinuous_vadd ProperlyDiscontinuousVAdd
-/

attribute [to_additive] ProperlyDiscontinuousSMul

variable {Γ : Type _} [Group Γ] {T : Type _} [TopologicalSpace T] [MulAction Γ T]

#print Finite.to_properlyDiscontinuousSMul /-
/-- A finite group action is always properly discontinuous. -/
@[to_additive "A finite group action is always properly discontinuous."]
instance (priority := 100) Finite.to_properlyDiscontinuousSMul [Finite Γ] :
    ProperlyDiscontinuousSMul Γ T where finite_disjoint_inter_image _ _ _ _ := Set.toFinite _
#align finite.to_properly_discontinuous_smul Finite.to_properlyDiscontinuousSMul
#align finite.to_properly_discontinuous_vadd Finite.to_properlyDiscontinuousVAdd
-/

export ProperlyDiscontinuousSMul (finite_disjoint_inter_image)

export ProperlyDiscontinuousVAdd (finite_disjoint_inter_image)

/- warning: is_open_map_quotient_mk_mul -> isOpenMap_quotient_mk'_mul is a dubious translation:
lean 3 declaration is
  forall {Γ : Type.{u1}} [_inst_1 : Group.{u1} Γ] {T : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} T] [_inst_3 : MulAction.{u1, u2} Γ T (DivInvMonoid.toMonoid.{u1} Γ (Group.toDivInvMonoid.{u1} Γ _inst_1))] [_inst_4 : ContinuousConstSMul.{u1, u2} Γ T _inst_2 (MulAction.toHasSmul.{u1, u2} Γ T (DivInvMonoid.toMonoid.{u1} Γ (Group.toDivInvMonoid.{u1} Γ _inst_1)) _inst_3)], IsOpenMap.{u2, u2} T (Quotient.{succ u2} T (MulAction.orbitRel.{u1, u2} Γ T _inst_1 _inst_3)) _inst_2 (Quotient.topologicalSpace.{u2} T (MulAction.orbitRel.{u1, u2} Γ T _inst_1 _inst_3) _inst_2) (Quotient.mk'.{succ u2} T (MulAction.orbitRel.{u1, u2} Γ T _inst_1 _inst_3))
but is expected to have type
  forall {Γ : Type.{u2}} [_inst_1 : Group.{u2} Γ] {T : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} T] [_inst_3 : MulAction.{u2, u1} Γ T (DivInvMonoid.toMonoid.{u2} Γ (Group.toDivInvMonoid.{u2} Γ _inst_1))] [_inst_4 : ContinuousConstSMul.{u2, u1} Γ T _inst_2 (MulAction.toSMul.{u2, u1} Γ T (DivInvMonoid.toMonoid.{u2} Γ (Group.toDivInvMonoid.{u2} Γ _inst_1)) _inst_3)], IsOpenMap.{u1, u1} T (Quotient.{succ u1} T (MulAction.orbitRel.{u2, u1} Γ T _inst_1 _inst_3)) _inst_2 (instTopologicalSpaceQuotient.{u1} T (MulAction.orbitRel.{u2, u1} Γ T _inst_1 _inst_3) _inst_2) (Quotient.mk'.{succ u1} T (MulAction.orbitRel.{u2, u1} Γ T _inst_1 _inst_3))
Case conversion may be inaccurate. Consider using '#align is_open_map_quotient_mk_mul isOpenMap_quotient_mk'_mulₓ'. -/
/-- The quotient map by a group action is open, i.e. the quotient by a group action is an open
  quotient. -/
@[to_additive
      "The quotient map by a group action is open, i.e. the quotient by a group\naction is an open quotient. "]
theorem isOpenMap_quotient_mk'_mul [ContinuousConstSMul Γ T] :
    IsOpenMap (Quotient.mk' : T → Quotient (MulAction.orbitRel Γ T)) :=
  by
  intro U hU
  rw [isOpen_coinduced, MulAction.quotient_preimage_image_eq_union_mul U]
  exact isOpen_unionᵢ fun γ => (Homeomorph.smul γ).IsOpenMap U hU
#align is_open_map_quotient_mk_mul isOpenMap_quotient_mk'_mul
#align is_open_map_quotient_mk_add isOpenMap_quotient_mk'_add

#print t2Space_of_properlyDiscontinuousSMul_of_t2Space /-
/-- The quotient by a discontinuous group action of a locally compact t2 space is t2. -/
@[to_additive "The quotient by a discontinuous group action of a locally compact t2\nspace is t2."]
instance (priority := 100) t2Space_of_properlyDiscontinuousSMul_of_t2Space [T2Space T]
    [LocallyCompactSpace T] [ContinuousConstSMul Γ T] [ProperlyDiscontinuousSMul Γ T] :
    T2Space (Quotient (MulAction.orbitRel Γ T)) :=
  by
  set Q := Quotient (MulAction.orbitRel Γ T)
  rw [t2Space_iff_nhds]
  let f : T → Q := Quotient.mk'
  have f_op : IsOpenMap f := isOpenMap_quotient_mk'_mul
  rintro ⟨x₀⟩ ⟨y₀⟩ (hxy : f x₀ ≠ f y₀)
  show ∃ U ∈ 𝓝 (f x₀), ∃ V ∈ 𝓝 (f y₀), _
  have hx₀y₀ : x₀ ≠ y₀ := ne_of_apply_ne _ hxy
  have hγx₀y₀ : ∀ γ : Γ, γ • x₀ ≠ y₀ := not_exists.mp (mt Quotient.sound hxy.symm : _)
  obtain ⟨K₀, L₀, K₀_in, L₀_in, hK₀, hL₀, hK₀L₀⟩ := t2_separation_compact_nhds hx₀y₀
  let bad_Γ_set := { γ : Γ | (· • ·) γ '' K₀ ∩ L₀ ≠ ∅ }
  have bad_Γ_finite : bad_Γ_set.finite := finite_disjoint_inter_image hK₀ hL₀
  choose u v hu hv u_v_disjoint using fun γ => t2_separation_nhds (hγx₀y₀ γ)
  let U₀₀ := ⋂ γ ∈ bad_Γ_set, (· • ·) γ ⁻¹' u γ
  let U₀ := U₀₀ ∩ K₀
  let V₀₀ := ⋂ γ ∈ bad_Γ_set, v γ
  let V₀ := V₀₀ ∩ L₀
  have U_nhds : f '' U₀ ∈ 𝓝 (f x₀) :=
    by
    apply f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr fun γ hγ => _) K₀_in)
    exact (continuous_const_smul _).ContinuousAt (hu γ)
  have V_nhds : f '' V₀ ∈ 𝓝 (f y₀) :=
    f_op.image_mem_nhds (inter_mem ((bInter_mem bad_Γ_finite).mpr fun γ hγ => hv γ) L₀_in)
  refine' ⟨f '' U₀, U_nhds, f '' V₀, V_nhds, MulAction.disjoint_image_image_iff.2 _⟩
  rintro x ⟨x_in_U₀₀, x_in_K₀⟩ γ
  by_cases H : γ ∈ bad_Γ_set
  · exact fun h => (u_v_disjoint γ).le_bot ⟨mem_Inter₂.mp x_in_U₀₀ γ H, mem_Inter₂.mp h.1 γ H⟩
  · rintro ⟨-, h'⟩
    simp only [image_smul, Classical.not_not, mem_set_of_eq, Ne.def] at H
    exact eq_empty_iff_forall_not_mem.mp H (γ • x) ⟨mem_image_of_mem _ x_in_K₀, h'⟩
#align t2_space_of_properly_discontinuous_smul_of_t2_space t2Space_of_properlyDiscontinuousSMul_of_t2Space
#align t2_space_of_properly_discontinuous_vadd_of_t2_space t2Space_of_properlyDiscontinuousVAdd_of_t2Space
-/

#print ContinuousConstSMul.secondCountableTopology /-
/-- The quotient of a second countable space by a group action is second countable. -/
@[to_additive
      "The quotient of a second countable space by an additive group action is second\ncountable."]
theorem ContinuousConstSMul.secondCountableTopology [SecondCountableTopology T]
    [ContinuousConstSMul Γ T] : SecondCountableTopology (Quotient (MulAction.orbitRel Γ T)) :=
  TopologicalSpace.Quotient.secondCountableTopology isOpenMap_quotient_mk'_mul
#align has_continuous_const_smul.second_countable_topology ContinuousConstSMul.secondCountableTopology
#align has_continuous_const_vadd.second_countable_topology ContinuousConstVAdd.secondCountableTopology
-/

section nhds

section MulAction

variable {G₀ : Type _} [GroupWithZero G₀] [MulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/- warning: set_smul_mem_nhds_smul -> set_smul_mem_nhds_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4))] [_inst_6 : TopologicalSpace.{u1} α] [_inst_7 : ContinuousConstSMul.{u2, u1} G₀ α _inst_6 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5)] {c : G₀} {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_6 x)) -> (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)))))))) -> (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5)) c s) (nhds.{u1} α _inst_6 (SMul.smul.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5) c x)))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_4 : GroupWithZero.{u1} G₀] [_inst_5 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4))] [_inst_6 : TopologicalSpace.{u2} α] [_inst_7 : ContinuousConstSMul.{u1, u2} G₀ α _inst_6 (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5)] {c : G₀} {s : Set.{u2} α} {x : α}, (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_6 x)) -> (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4))))) -> (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (HSMul.hSMul.{u1, u2, u2} G₀ (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5))) c s) (nhds.{u2} α _inst_6 (HSMul.hSMul.{u1, u2, u2} G₀ α α (instHSMul.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5)) c x)))
Case conversion may be inaccurate. Consider using '#align set_smul_mem_nhds_smul set_smul_mem_nhds_smulₓ'. -/
/-- Scalar multiplication preserves neighborhoods. -/
theorem set_smul_mem_nhds_smul {c : G₀} {s : Set α} {x : α} (hs : s ∈ 𝓝 x) (hc : c ≠ 0) :
    c • s ∈ 𝓝 (c • x : α) := by
  rw [mem_nhds_iff] at hs⊢
  obtain ⟨U, hs', hU, hU'⟩ := hs
  exact ⟨c • U, Set.smul_set_mono hs', hU.smul₀ hc, Set.smul_mem_smul_set hU'⟩
#align set_smul_mem_nhds_smul set_smul_mem_nhds_smul

/- warning: set_smul_mem_nhds_smul_iff -> set_smul_mem_nhds_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : MulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4))] [_inst_6 : TopologicalSpace.{u1} α] [_inst_7 : ContinuousConstSMul.{u2, u1} G₀ α _inst_6 (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5)] {c : G₀} {s : Set.{u1} α} {x : α}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)))))))) -> (Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5)) c s) (nhds.{u1} α _inst_6 (SMul.smul.{u2, u1} G₀ α (MulAction.toHasSmul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5) c x))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_6 x)))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_4 : GroupWithZero.{u1} G₀] [_inst_5 : MulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4))] [_inst_6 : TopologicalSpace.{u2} α] [_inst_7 : ContinuousConstSMul.{u1, u2} G₀ α _inst_6 (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5)] {c : G₀} {s : Set.{u2} α} {x : α}, (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4))))) -> (Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (HSMul.hSMul.{u1, u2, u2} G₀ (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5))) c s) (nhds.{u2} α _inst_6 (HSMul.hSMul.{u1, u2, u2} G₀ α α (instHSMul.{u1, u2} G₀ α (MulAction.toSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5)) c x))) (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_6 x)))
Case conversion may be inaccurate. Consider using '#align set_smul_mem_nhds_smul_iff set_smul_mem_nhds_smul_iffₓ'. -/
theorem set_smul_mem_nhds_smul_iff {c : G₀} {s : Set α} {x : α} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (c • x : α) ↔ s ∈ 𝓝 x :=
  by
  refine' ⟨fun h => _, fun h => set_smul_mem_nhds_smul h hc⟩
  rw [← inv_smul_smul₀ hc x, ← inv_smul_smul₀ hc s]
  exact set_smul_mem_nhds_smul h (inv_ne_zero hc)
#align set_smul_mem_nhds_smul_iff set_smul_mem_nhds_smul_iff

end MulAction

section DistribMulAction

variable {G₀ : Type _} [GroupWithZero G₀] [AddMonoid α] [DistribMulAction G₀ α] [TopologicalSpace α]
  [ContinuousConstSMul G₀ α]

/- warning: set_smul_mem_nhds_zero_iff -> set_smul_mem_nhds_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : AddMonoid.{u1} α] [_inst_6 : DistribMulAction.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5] [_inst_7 : TopologicalSpace.{u1} α] [_inst_8 : ContinuousConstSMul.{u2, u1} G₀ α _inst_7 (SMulZeroClass.toHasSmul.{u2, u1} G₀ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_5)) (DistribSMul.toSmulZeroClass.{u2, u1} G₀ α (AddMonoid.toAddZeroClass.{u1} α _inst_5) (DistribMulAction.toDistribSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5 _inst_6)))] {s : Set.{u1} α} {c : G₀}, (Ne.{succ u2} G₀ c (OfNat.ofNat.{u2} G₀ 0 (OfNat.mk.{u2} G₀ 0 (Zero.zero.{u2} G₀ (MulZeroClass.toHasZero.{u2} G₀ (MulZeroOneClass.toMulZeroClass.{u2} G₀ (MonoidWithZero.toMulZeroOneClass.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)))))))) -> (Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) (SMul.smul.{u2, u1} G₀ (Set.{u1} α) (Set.smulSet.{u2, u1} G₀ α (SMulZeroClass.toHasSmul.{u2, u1} G₀ α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_5)) (DistribSMul.toSmulZeroClass.{u2, u1} G₀ α (AddMonoid.toAddZeroClass.{u1} α _inst_5) (DistribMulAction.toDistribSMul.{u2, u1} G₀ α (MonoidWithZero.toMonoid.{u2} G₀ (GroupWithZero.toMonoidWithZero.{u2} G₀ _inst_4)) _inst_5 _inst_6)))) c s) (nhds.{u1} α _inst_7 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_5))))))) (Membership.Mem.{u1, u1} (Set.{u1} α) (Filter.{u1} α) (Filter.hasMem.{u1} α) s (nhds.{u1} α _inst_7 (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α _inst_5))))))))
but is expected to have type
  forall {α : Type.{u2}} {G₀ : Type.{u1}} [_inst_4 : GroupWithZero.{u1} G₀] [_inst_5 : AddMonoid.{u2} α] [_inst_6 : DistribMulAction.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5] [_inst_7 : TopologicalSpace.{u2} α] [_inst_8 : ContinuousConstSMul.{u1, u2} G₀ α _inst_7 (SMulZeroClass.toSMul.{u1, u2} G₀ α (AddMonoid.toZero.{u2} α _inst_5) (DistribSMul.toSMulZeroClass.{u1, u2} G₀ α (AddMonoid.toAddZeroClass.{u2} α _inst_5) (DistribMulAction.toDistribSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5 _inst_6)))] {s : Set.{u2} α} {c : G₀}, (Ne.{succ u1} G₀ c (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4))))) -> (Iff (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) (HSMul.hSMul.{u1, u2, u2} G₀ (Set.{u2} α) (Set.{u2} α) (instHSMul.{u1, u2} G₀ (Set.{u2} α) (Set.smulSet.{u1, u2} G₀ α (SMulZeroClass.toSMul.{u1, u2} G₀ α (AddMonoid.toZero.{u2} α _inst_5) (DistribSMul.toSMulZeroClass.{u1, u2} G₀ α (AddMonoid.toAddZeroClass.{u2} α _inst_5) (DistribMulAction.toDistribSMul.{u1, u2} G₀ α (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_4)) _inst_5 _inst_6))))) c s) (nhds.{u2} α _inst_7 (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α _inst_5))))) (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s (nhds.{u2} α _inst_7 (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (AddMonoid.toZero.{u2} α _inst_5))))))
Case conversion may be inaccurate. Consider using '#align set_smul_mem_nhds_zero_iff set_smul_mem_nhds_zero_iffₓ'. -/
theorem set_smul_mem_nhds_zero_iff {s : Set α} {c : G₀} (hc : c ≠ 0) :
    c • s ∈ 𝓝 (0 : α) ↔ s ∈ 𝓝 (0 : α) :=
  by
  refine' Iff.trans _ (set_smul_mem_nhds_smul_iff hc)
  rw [smul_zero]
#align set_smul_mem_nhds_zero_iff set_smul_mem_nhds_zero_iff

end DistribMulAction

end nhds

