/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa

! This file was ported from Lean 3 source module topology.continuous_function.t0_sierpinski
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Order
import Mathbin.Topology.Sets.Opens
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Any T0 space embeds in a product of copies of the Sierpinski space.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We consider `Prop` with the Sierpinski topology. If `X` is a topological space, there is a
continuous map `product_of_mem_opens` from `X` to `opens X → Prop` which is the product of the maps
`X → Prop` given by `x ↦ x ∈ u`.

The map `product_of_mem_opens` is always inducing. Whenever `X` is T0, `product_of_mem_opens` is
also injective and therefore an embedding.
-/


noncomputable section

namespace TopologicalSpace

/- warning: topological_space.eq_induced_by_maps_to_sierpinski -> TopologicalSpace.eq_induced_by_maps_to_sierpinski is a dubious translation:
lean 3 declaration is
  forall (X : Type.{u1}) [t : TopologicalSpace.{u1} X], Eq.{succ u1} (TopologicalSpace.{u1} X) t (infᵢ.{u1, succ u1} (TopologicalSpace.{u1} X) (ConditionallyCompleteLattice.toHasInf.{u1} (TopologicalSpace.{u1} X) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} X) (TopologicalSpace.completeLattice.{u1} X))) (TopologicalSpace.Opens.{u1} X t) (fun (u : TopologicalSpace.Opens.{u1} X t) => TopologicalSpace.induced.{u1, 0} X Prop (fun (_x : X) => Membership.Mem.{u1, u1} X (TopologicalSpace.Opens.{u1} X t) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} X t) X (TopologicalSpace.Opens.setLike.{u1} X t)) _x u) sierpinskiSpace))
but is expected to have type
  forall (X : Type.{u1}) [t : TopologicalSpace.{u1} X], Eq.{succ u1} (TopologicalSpace.{u1} X) t (infᵢ.{u1, succ u1} (TopologicalSpace.{u1} X) (ConditionallyCompleteLattice.toInfSet.{u1} (TopologicalSpace.{u1} X) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.{u1} X) (TopologicalSpace.instCompleteLatticeTopologicalSpace.{u1} X))) (TopologicalSpace.Opens.{u1} X t) (fun (u : TopologicalSpace.Opens.{u1} X t) => TopologicalSpace.induced.{u1, 0} X Prop (fun (_x : X) => Membership.mem.{u1, u1} X (TopologicalSpace.Opens.{u1} X t) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} X t) X (TopologicalSpace.Opens.instSetLikeOpens.{u1} X t)) _x u) sierpinskiSpace))
Case conversion may be inaccurate. Consider using '#align topological_space.eq_induced_by_maps_to_sierpinski TopologicalSpace.eq_induced_by_maps_to_sierpinskiₓ'. -/
theorem eq_induced_by_maps_to_sierpinski (X : Type _) [t : TopologicalSpace X] :
    t = ⨅ u : Opens X, sierpinskiSpace.induced (· ∈ u) :=
  by
  apply le_antisymm
  · rw [le_infᵢ_iff]
    exact fun u => Continuous.le_induced (is_open_iff_continuous_mem.mp u.2)
  · intro u h
    rw [← generateFrom_unionᵢ_isOpen]
    apply is_open_generate_from_of_mem
    simp only [Set.mem_unionᵢ, Set.mem_setOf_eq, isOpen_induced_iff]
    exact ⟨⟨u, h⟩, {True}, isOpen_singleton_true, by simp [Set.preimage]⟩
#align topological_space.eq_induced_by_maps_to_sierpinski TopologicalSpace.eq_induced_by_maps_to_sierpinski

variable (X : Type _) [TopologicalSpace X]

#print TopologicalSpace.productOfMemOpens /-
/-- The continuous map from `X` to the product of copies of the Sierpinski space, (one copy for each
open subset `u` of `X`). The `u` coordinate of `product_of_mem_opens x` is given by `x ∈ u`.
-/
def productOfMemOpens : C(X, Opens X → Prop)
    where
  toFun x u := x ∈ u
  continuous_toFun := continuous_pi_iff.2 fun u => continuous_Prop.2 u.IsOpen
#align topological_space.product_of_mem_opens TopologicalSpace.productOfMemOpens
-/

/- warning: topological_space.product_of_mem_opens_inducing -> TopologicalSpace.productOfMemOpens_inducing is a dubious translation:
lean 3 declaration is
  forall (X : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} X], Inducing.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (coeFn.{succ u1, succ u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) (fun (_x : ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) => X -> (TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) (ContinuousMap.hasCoeToFun.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) (TopologicalSpace.productOfMemOpens.{u1} X _inst_1))
but is expected to have type
  forall (X : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} X], Inducing.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => (TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)))) (TopologicalSpace.productOfMemOpens.{u1} X _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.product_of_mem_opens_inducing TopologicalSpace.productOfMemOpens_inducingₓ'. -/
theorem productOfMemOpens_inducing : Inducing (productOfMemOpens X) :=
  by
  convert inducing_infᵢ_to_pi fun (u : opens X) (x : X) => x ∈ u
  apply eq_induced_by_maps_to_sierpinski
#align topological_space.product_of_mem_opens_inducing TopologicalSpace.productOfMemOpens_inducing

/- warning: topological_space.product_of_mem_opens_injective -> TopologicalSpace.productOfMemOpens_injective is a dubious translation:
lean 3 declaration is
  forall (X : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : T0Space.{u1} X _inst_1], Function.Injective.{succ u1, succ u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) (coeFn.{succ u1, succ u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) (fun (_x : ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) => X -> (TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) (ContinuousMap.hasCoeToFun.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) (TopologicalSpace.productOfMemOpens.{u1} X _inst_1))
but is expected to have type
  forall (X : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : T0Space.{u1} X _inst_1], Function.Injective.{succ u1, succ u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => (TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)))) (TopologicalSpace.productOfMemOpens.{u1} X _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.product_of_mem_opens_injective TopologicalSpace.productOfMemOpens_injectiveₓ'. -/
theorem productOfMemOpens_injective [T0Space X] : Function.Injective (productOfMemOpens X) :=
  by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← Inducing.inseparable_iff (product_of_mem_opens_inducing X), h]
#align topological_space.product_of_mem_opens_injective TopologicalSpace.productOfMemOpens_injective

/- warning: topological_space.product_of_mem_opens_embedding -> TopologicalSpace.productOfMemOpens_embedding is a dubious translation:
lean 3 declaration is
  forall (X : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : T0Space.{u1} X _inst_1], Embedding.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (coeFn.{succ u1, succ u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) (fun (_x : ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) => X -> (TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) (ContinuousMap.hasCoeToFun.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) (TopologicalSpace.productOfMemOpens.{u1} X _inst_1))
but is expected to have type
  forall (X : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : T0Space.{u1} X _inst_1], Embedding.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (ᾰ : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (FunLike.coe.{succ u1, succ u1, succ u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : X) => (TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _x) (ContinuousMapClass.toFunLike.{u1, u1, u1} (ContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace))) X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)) (ContinuousMap.instContinuousMapClassContinuousMap.{u1, u1} X ((TopologicalSpace.Opens.{u1} X _inst_1) -> Prop) _inst_1 (Pi.topologicalSpace.{u1, 0} (TopologicalSpace.Opens.{u1} X _inst_1) (fun (a._@.Mathlib.Topology.ContinuousFunction.T0Sierpinski._hyg.166 : TopologicalSpace.Opens.{u1} X _inst_1) => Prop) (fun (a : TopologicalSpace.Opens.{u1} X _inst_1) => sierpinskiSpace)))) (TopologicalSpace.productOfMemOpens.{u1} X _inst_1))
Case conversion may be inaccurate. Consider using '#align topological_space.product_of_mem_opens_embedding TopologicalSpace.productOfMemOpens_embeddingₓ'. -/
theorem productOfMemOpens_embedding [T0Space X] : Embedding (productOfMemOpens X) :=
  Embedding.mk (productOfMemOpens_inducing X) (productOfMemOpens_injective X)
#align topological_space.product_of_mem_opens_embedding TopologicalSpace.productOfMemOpens_embedding

end TopologicalSpace

