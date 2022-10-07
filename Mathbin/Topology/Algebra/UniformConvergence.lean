/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Topology.UniformSpace.UniformConvergenceTopology
import Mathbin.Topology.Algebra.UniformGroup

/-!
# Algebraic facts about the topology of uniform convergence

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `uniform_convergence.uniform_group` : if `G` is a uniform group, then the uniform structure of
  uniform convergence makes `α → G` a uniform group
* `uniform_convergence_on.uniform_group` : if `G` is a uniform group, then the uniform structure of
  `𝔖`-convergence, for any `𝔖 : set (set α)`, makes `α → G` a uniform group

## TODO

* Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α → E`. If the image of any `S ∈ 𝔖`
  by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`, equipped with
  the topology of `𝔖`-convergence, is a TVS.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

uniform convergence, strong dual

-/


section Groupₓ

variable {α G : Type _} [Groupₓ G] [UniformSpace G] [UniformGroup G] {𝔖 : Set <| Set α}

attribute [-instance] Pi.uniformSpace

/-- If `G` is a uniform group, then the uniform structure of uniform convergence makes `α → G`
a uniform group as well. -/
@[to_additive
      "If `G` is a uniform additive group, then the uniform structure of uniform\nconvergence makes `α → G` a uniform additive group as well."]
protected theorem UniformConvergence.uniform_group : @UniformGroup (α → G) (UniformConvergence.uniformSpace α G) _ := by
  -- Since `(/) : G × G → G` is uniformly continuous,
  -- `uniform_convergence.postcomp_uniform_continuous` tells us that
  -- `((/) ∘ —) : (α → G × G) → (α → G)` is uniformly continuous too. By precomposing with
  -- `uniform_convergence.uniform_equiv_prod_arrow`, this gives that
  -- `(/) : (α → G) × (α → G) → (α → G)` is also uniformly continuous
  letI : UniformSpace (α → G) := UniformConvergence.uniformSpace α G
  letI : UniformSpace (α → G × G) := UniformConvergence.uniformSpace α (G × G)
  exact
    ⟨(UniformConvergence.postcomp_uniform_continuous uniform_continuous_div).comp
        uniform_convergence.uniform_equiv_prod_arrow.symm.uniform_continuous⟩

/-- Let `𝔖 : set (set α)`. If `G` is a uniform group, then the uniform structure of
`𝔖`-convergence makes `α → G` a uniform group as well. -/
@[to_additive
      "Let `𝔖 : set (set α)`. If `G` is a uniform additive group, then the uniform\nstructure of  `𝔖`-convergence makes `α → G` a uniform additive group as well. "]
protected theorem UniformConvergenceOn.uniform_group :
    @UniformGroup (α → G) (UniformConvergenceOn.uniformSpace α G 𝔖) _ := by
  -- Since `(/) : G × G → G` is uniformly continuous,
  -- `uniform_convergence_on.postcomp_uniform_continuous` tells us that
  -- `((/) ∘ —) : (α → G × G) → (α → G)` is uniformly continuous too. By precomposing with
  -- `uniform_convergence_on.uniform_equiv_prod_arrow`, this gives that
  -- `(/) : (α → G) × (α → G) → (α → G)` is also uniformly continuous
  letI : UniformSpace (α → G) := UniformConvergenceOn.uniformSpace α G 𝔖
  letI : UniformSpace (α → G × G) := UniformConvergenceOn.uniformSpace α (G × G) 𝔖
  exact
    ⟨(UniformConvergenceOn.postcomp_uniform_continuous uniform_continuous_div).comp
        uniform_convergence_on.uniform_equiv_prod_arrow.symm.uniform_continuous⟩

end Groupₓ

