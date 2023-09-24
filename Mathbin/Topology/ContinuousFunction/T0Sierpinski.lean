/-
Copyright (c) 2022 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import Topology.Order
import Topology.Sets.Opens
import Topology.ContinuousFunction.Basic

#align_import topology.continuous_function.t0_sierpinski from "leanprover-community/mathlib"@"34ee86e6a59d911a8e4f89b68793ee7577ae79c7"

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

#print TopologicalSpace.eq_induced_by_maps_to_sierpinski /-
theorem eq_induced_by_maps_to_sierpinski (X : Type _) [t : TopologicalSpace X] :
    t = ⨅ u : Opens X, sierpinskiSpace.induced (· ∈ u) :=
  by
  apply le_antisymm
  · rw [le_iInf_iff]
    exact fun u => Continuous.le_induced (is_open_iff_continuous_mem.mp u.2)
  · intro u h
    rw [← generateFrom_iUnion_isOpen]
    apply is_open_generate_from_of_mem
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, isOpen_induced_iff]
    exact ⟨⟨u, h⟩, {True}, isOpen_singleton_true, by simp [Set.preimage]⟩
#align topological_space.eq_induced_by_maps_to_sierpinski TopologicalSpace.eq_induced_by_maps_to_sierpinski
-/

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

#print TopologicalSpace.productOfMemOpens_inducing /-
theorem productOfMemOpens_inducing : Inducing (productOfMemOpens X) :=
  by
  convert inducing_iInf_to_pi fun (u : opens X) (x : X) => x ∈ u
  apply eq_induced_by_maps_to_sierpinski
#align topological_space.product_of_mem_opens_inducing TopologicalSpace.productOfMemOpens_inducing
-/

#print TopologicalSpace.productOfMemOpens_injective /-
theorem productOfMemOpens_injective [T0Space X] : Function.Injective (productOfMemOpens X) :=
  by
  intro x1 x2 h
  apply Inseparable.eq
  rw [← Inducing.inseparable_iff (product_of_mem_opens_inducing X), h]
#align topological_space.product_of_mem_opens_injective TopologicalSpace.productOfMemOpens_injective
-/

#print TopologicalSpace.productOfMemOpens_embedding /-
theorem productOfMemOpens_embedding [T0Space X] : Embedding (productOfMemOpens X) :=
  Embedding.mk (productOfMemOpens_inducing X) (productOfMemOpens_injective X)
#align topological_space.product_of_mem_opens_embedding TopologicalSpace.productOfMemOpens_embedding
-/

end TopologicalSpace

