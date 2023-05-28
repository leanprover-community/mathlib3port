/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.uniform_convergence
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformConvergenceTopology
import Mathbin.Analysis.LocallyConvex.Bounded
import Mathbin.Topology.Algebra.FilterBasis

/-!
# Algebraic facts about the topology of uniform convergence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains algebraic compatibility results about the uniform structure of uniform
convergence / `𝔖`-convergence. They will mostly be useful for defining strong topologies on the
space of continuous linear maps between two topological vector spaces.

## Main statements

* `uniform_fun.uniform_group` : if `G` is a uniform group, then `α →ᵤ G` a uniform group
* `uniform_on_fun.uniform_group` : if `G` is a uniform group, then for any `𝔖 : set (set α)`,
  `α →ᵤ[𝔖] G` a uniform group.
* `uniform_on_fun.has_continuous_smul_of_image_bounded` : let `E` be a TVS, `𝔖 : set (set α)` and
  `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any `S ∈ 𝔖` by any `u ∈ H` is bounded (in the
  sense of `bornology.is_vonN_bounded`), then `H`, equipped with the topology induced from
  `α →ᵤ[𝔖] E`, is a TVS.

## Implementation notes

Like in `topology/uniform_space/uniform_convergence_topology`, we use the type aliases
`uniform_fun` (denoted `α →ᵤ β`) and `uniform_on_fun` (denoted `α →ᵤ[𝔖] β`) for functions from `α`
to `β` endowed with the structures of uniform convergence and `𝔖`-convergence.

## TODO

* `uniform_on_fun.has_continuous_smul_of_image_bounded` unnecessarily asks for `𝔖` to be
  nonempty and directed. This will be easy to solve once we know that replacing `𝔖` by its
  ***noncovering*** bornology (i.e ***not*** what `bornology` currently refers to in mathlib)
  doesn't change the topology.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]
* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, strong dual

-/


open Filter

open Topology Pointwise UniformConvergence

section AlgebraicInstances

variable {α β ι R : Type _} {𝔖 : Set <| Set α}

@[to_additive]
instance [Monoid β] : Monoid (α →ᵤ β) :=
  Pi.monoid

@[to_additive]
instance [Monoid β] : Monoid (α →ᵤ[𝔖] β) :=
  Pi.monoid

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ᵤ β) :=
  Pi.commMonoid

@[to_additive]
instance [CommMonoid β] : CommMonoid (α →ᵤ[𝔖] β) :=
  Pi.commMonoid

@[to_additive]
instance [Group β] : Group (α →ᵤ β) :=
  Pi.group

@[to_additive]
instance [Group β] : Group (α →ᵤ[𝔖] β) :=
  Pi.group

@[to_additive]
instance [CommGroup β] : CommGroup (α →ᵤ β) :=
  Pi.commGroup

@[to_additive]
instance [CommGroup β] : CommGroup (α →ᵤ[𝔖] β) :=
  Pi.commGroup

instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ β) :=
  Pi.module _ _ _

instance [Semiring R] [AddCommMonoid β] [Module R β] : Module R (α →ᵤ[𝔖] β) :=
  Pi.module _ _ _

end AlgebraicInstances

section Group

variable {α G ι : Type _} [Group G] {𝔖 : Set <| Set α} [UniformSpace G] [UniformGroup G]

/-- If `G` is a uniform group, then `α →ᵤ G` is a uniform group as well. -/
@[to_additive
      "If `G` is a uniform additive group, then `α →ᵤ G` is a uniform additive group\nas well."]
instance : UniformGroup (α →ᵤ G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
          -- `uniform_fun.postcomp_uniform_continuous` tells us that
          -- `((/) ∘ —) : (α →ᵤ G × G) → (α →ᵤ G)` is uniformly continuous too. By precomposing with
          -- `uniform_fun.uniform_equiv_prod_arrow`, this gives that
          -- `(/) : (α →ᵤ G) × (α →ᵤ G) → (α →ᵤ G)` is also uniformly continuous
          UniformFun.postcomp_uniformContinuous
          uniformContinuous_div).comp
      UniformFun.uniformEquivProdArrow.symm.UniformContinuous⟩

/- warning: uniform_fun.has_basis_nhds_one_of_basis -> UniformFun.hasBasis_nhds_one_of_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Group.{u2} G] [_inst_2 : UniformSpace.{u2} G] [_inst_3 : UniformGroup.{u2} G _inst_2 _inst_1] {p : ι -> Prop} {b : ι -> (Set.{u2} G)}, (Filter.HasBasis.{u2, succ u3} G ι (nhds.{u2} G (UniformSpace.toTopologicalSpace.{u2} G _inst_2) (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))))) p b) -> (Filter.HasBasis.{max u1 u2, succ u3} (UniformFun.{u1, u2} α G) ι (nhds.{max u1 u2} (UniformFun.{u1, u2} α G) (UniformFun.topologicalSpace.{u1, u2} α G _inst_2) (OfNat.ofNat.{max u1 u2} (UniformFun.{u1, u2} α G) 1 (OfNat.mk.{max u1 u2} (UniformFun.{u1, u2} α G) 1 (One.one.{max u1 u2} (UniformFun.{u1, u2} α G) (MulOneClass.toHasOne.{max u1 u2} (UniformFun.{u1, u2} α G) (Monoid.toMulOneClass.{max u1 u2} (UniformFun.{u1, u2} α G) (UniformFun.monoid.{u1, u2} α G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))))) p (fun (i : ι) => setOf.{max u1 u2} (UniformFun.{u1, u2} α G) (fun (f : UniformFun.{u1, u2} α G) => forall (x : α), Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) (f x) (b i))))
but is expected to have type
  forall {α : Type.{u1}} {G : Type.{u3}} {ι : Type.{u2}} [_inst_1 : Group.{u3} G] [_inst_2 : UniformSpace.{u3} G] [_inst_3 : UniformGroup.{u3} G _inst_2 _inst_1] {p : ι -> Prop} {b : ι -> (Set.{u3} G)}, (Filter.HasBasis.{u3, succ u2} G ι (nhds.{u3} G (UniformSpace.toTopologicalSpace.{u3} G _inst_2) (OfNat.ofNat.{u3} G 1 (One.toOfNat1.{u3} G (InvOneClass.toOne.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_1))))))) p b) -> (Filter.HasBasis.{max u1 u3, succ u2} (UniformFun.{u1, u3} α G) ι (nhds.{max u1 u3} (UniformFun.{u1, u3} α G) (UniformFun.topologicalSpace.{u1, u3} α G _inst_2) (OfNat.ofNat.{max u1 u3} (UniformFun.{u1, u3} α G) 1 (One.toOfNat1.{max u1 u3} (UniformFun.{u1, u3} α G) (InvOneClass.toOne.{max u1 u3} (UniformFun.{u1, u3} α G) (DivInvOneMonoid.toInvOneClass.{max u1 u3} (UniformFun.{u1, u3} α G) (DivisionMonoid.toDivInvOneMonoid.{max u1 u3} (UniformFun.{u1, u3} α G) (Group.toDivisionMonoid.{max u1 u3} (UniformFun.{u1, u3} α G) (instGroupUniformFun.{u1, u3} α G _inst_1)))))))) p (fun (i : ι) => setOf.{max u1 u3} (UniformFun.{u1, u3} α G) (fun (f : UniformFun.{u1, u3} α G) => forall (x : α), Membership.mem.{u3, u3} G (Set.{u3} G) (Set.instMembershipSet.{u3} G) (f x) (b i))))
Case conversion may be inaccurate. Consider using '#align uniform_fun.has_basis_nhds_one_of_basis UniformFun.hasBasis_nhds_one_of_basisₓ'. -/
@[to_additive]
protected theorem UniformFun.hasBasis_nhds_one_of_basis {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis p fun i => { f : α →ᵤ G | ∀ x, f x ∈ b i } :=
  by
  have := h.comap fun p : G × G => p.2 / p.1
  rw [← uniformity_eq_comap_nhds_one] at this
  convert UniformFun.hasBasis_nhds_of_basis α _ 1 this
  ext (i f)
  simp [UniformFun.gen]
#align uniform_fun.has_basis_nhds_one_of_basis UniformFun.hasBasis_nhds_one_of_basis
#align uniform_fun.has_basis_nhds_zero_of_basis UniformFun.hasBasis_nhds_zero_of_basis

/- warning: uniform_fun.has_basis_nhds_one -> UniformFun.hasBasis_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : UniformSpace.{u2} G] [_inst_3 : UniformGroup.{u2} G _inst_2 _inst_1], Filter.HasBasis.{max u1 u2, succ u2} (UniformFun.{u1, u2} α G) (Set.{u2} G) (nhds.{max u1 u2} (UniformFun.{u1, u2} α G) (UniformFun.topologicalSpace.{u1, u2} α G _inst_2) (OfNat.ofNat.{max u1 u2} (UniformFun.{u1, u2} α G) 1 (OfNat.mk.{max u1 u2} (UniformFun.{u1, u2} α G) 1 (One.one.{max u1 u2} (UniformFun.{u1, u2} α G) (MulOneClass.toHasOne.{max u1 u2} (UniformFun.{u1, u2} α G) (Monoid.toMulOneClass.{max u1 u2} (UniformFun.{u1, u2} α G) (UniformFun.monoid.{u1, u2} α G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))))) (fun (V : Set.{u2} G) => Membership.Mem.{u2, u2} (Set.{u2} G) (Filter.{u2} G) (Filter.hasMem.{u2} G) V (nhds.{u2} G (UniformSpace.toTopologicalSpace.{u2} G _inst_2) (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))))) (fun (V : Set.{u2} G) => setOf.{max u1 u2} (UniformFun.{u1, u2} α G) (fun (f : α -> G) => forall (x : α), Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) (f x) V))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : UniformSpace.{u1} G] [_inst_3 : UniformGroup.{u1} G _inst_2 _inst_1], Filter.HasBasis.{max u2 u1, succ u1} (UniformFun.{u2, u1} α G) (Set.{u1} G) (nhds.{max u2 u1} (UniformFun.{u2, u1} α G) (UniformFun.topologicalSpace.{u2, u1} α G _inst_2) (OfNat.ofNat.{max u2 u1} (UniformFun.{u2, u1} α G) 1 (One.toOfNat1.{max u2 u1} (UniformFun.{u2, u1} α G) (InvOneClass.toOne.{max u2 u1} (UniformFun.{u2, u1} α G) (DivInvOneMonoid.toInvOneClass.{max u2 u1} (UniformFun.{u2, u1} α G) (DivisionMonoid.toDivInvOneMonoid.{max u2 u1} (UniformFun.{u2, u1} α G) (Group.toDivisionMonoid.{max u2 u1} (UniformFun.{u2, u1} α G) (instGroupUniformFun.{u2, u1} α G _inst_1)))))))) (fun (V : Set.{u1} G) => Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) V (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G _inst_2) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))) (fun (V : Set.{u1} G) => setOf.{max u2 u1} (UniformFun.{u2, u1} α G) (fun (f : α -> G) => forall (x : α), Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (f x) V))
Case conversion may be inaccurate. Consider using '#align uniform_fun.has_basis_nhds_one UniformFun.hasBasis_nhds_oneₓ'. -/
@[to_additive]
protected theorem UniformFun.hasBasis_nhds_one :
    (𝓝 1 : Filter (α →ᵤ G)).HasBasis (fun V : Set G => V ∈ (𝓝 1 : Filter G)) fun V =>
      { f : α → G | ∀ x, f x ∈ V } :=
  UniformFun.hasBasis_nhds_one_of_basis (basis_sets _)
#align uniform_fun.has_basis_nhds_one UniformFun.hasBasis_nhds_one
#align uniform_fun.has_basis_nhds_zero UniformFun.hasBasis_nhds_zero

/-- Let `𝔖 : set (set α)`. If `G` is a uniform group, then `α →ᵤ[𝔖] G` is a uniform group as
well. -/
@[to_additive
      "Let `𝔖 : set (set α)`. If `G` is a uniform additive group, then `α →ᵤ[𝔖] G` is a\nuniform additive group as well. "]
instance : UniformGroup (α →ᵤ[𝔖] G) :=
  ⟨(-- Since `(/) : G × G → G` is uniformly continuous,
          -- `uniform_on_fun.postcomp_uniform_continuous` tells us that
          -- `((/) ∘ —) : (α →ᵤ[𝔖] G × G) → (α →ᵤ[𝔖] G)` is uniformly continuous too. By precomposing with
          -- `uniform_on_fun.uniform_equiv_prod_arrow`, this gives that
          -- `(/) : (α →ᵤ[𝔖] G) × (α →ᵤ[𝔖] G) → (α →ᵤ[𝔖] G)` is also uniformly continuous
          UniformOnFun.postcomp_uniformContinuous
          uniformContinuous_div).comp
      UniformOnFun.uniformEquivProdArrow.symm.UniformContinuous⟩

/- warning: uniform_on_fun.has_basis_nhds_one_of_basis -> UniformOnFun.hasBasis_nhds_one_of_basis is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Group.{u2} G] [_inst_2 : UniformSpace.{u2} G] [_inst_3 : UniformGroup.{u2} G _inst_2 _inst_1] (𝔖 : Set.{u1} (Set.{u1} α)), (Set.Nonempty.{u1} (Set.{u1} α) 𝔖) -> (DirectedOn.{u1} (Set.{u1} α) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) 𝔖) -> (forall {p : ι -> Prop} {b : ι -> (Set.{u2} G)}, (Filter.HasBasis.{u2, succ u3} G ι (nhds.{u2} G (UniformSpace.toTopologicalSpace.{u2} G _inst_2) (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))))) p b) -> (Filter.HasBasis.{max u1 u2, max (succ u1) (succ u3)} (UniformOnFun.{u1, u2} α G 𝔖) (Prod.{u1, u3} (Set.{u1} α) ι) (nhds.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (UniformOnFun.topologicalSpace.{u1, u2} α G _inst_2 𝔖) (OfNat.ofNat.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) 1 (OfNat.mk.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) 1 (One.one.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (MulOneClass.toHasOne.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (Monoid.toMulOneClass.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (UniformOnFun.monoid.{u1, u2} α G 𝔖 (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))))) (fun (Si : Prod.{u1, u3} (Set.{u1} α) ι) => And (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Prod.fst.{u1, u3} (Set.{u1} α) ι Si) 𝔖) (p (Prod.snd.{u1, u3} (Set.{u1} α) ι Si))) (fun (Si : Prod.{u1, u3} (Set.{u1} α) ι) => setOf.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (fun (f : UniformOnFun.{u1, u2} α G 𝔖) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Prod.fst.{u1, u3} (Set.{u1} α) ι Si)) -> (Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) (f x) (b (Prod.snd.{u1, u3} (Set.{u1} α) ι Si)))))))
but is expected to have type
  forall {α : Type.{u3}} {G : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : UniformSpace.{u2} G] [_inst_3 : UniformGroup.{u2} G _inst_2 _inst_1] (𝔖 : Set.{u3} (Set.{u3} α)), (Set.Nonempty.{u3} (Set.{u3} α) 𝔖) -> (DirectedOn.{u3} (Set.{u3} α) (fun (x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1382 : Set.{u3} α) (x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1384 : Set.{u3} α) => HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1382 x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1384) 𝔖) -> (forall {p : ι -> Prop} {b : ι -> (Set.{u2} G)}, (Filter.HasBasis.{u2, succ u1} G ι (nhds.{u2} G (UniformSpace.toTopologicalSpace.{u2} G _inst_2) (OfNat.ofNat.{u2} G 1 (One.toOfNat1.{u2} G (InvOneClass.toOne.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_1))))))) p b) -> (Filter.HasBasis.{max u3 u2, max (succ u3) (succ u1)} (UniformOnFun.{u3, u2} α G 𝔖) (Prod.{u3, u1} (Set.{u3} α) ι) (nhds.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (UniformOnFun.topologicalSpace.{u3, u2} α G _inst_2 𝔖) (OfNat.ofNat.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) 1 (One.toOfNat1.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (InvOneClass.toOne.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (DivInvOneMonoid.toInvOneClass.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (DivisionMonoid.toDivInvOneMonoid.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (Group.toDivisionMonoid.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (instGroupUniformOnFun.{u3, u2} α G 𝔖 _inst_1)))))))) (fun (Si : Prod.{u3, u1} (Set.{u3} α) ι) => And (Membership.mem.{u3, u3} (Set.{u3} α) (Set.{u3} (Set.{u3} α)) (Set.instMembershipSet.{u3} (Set.{u3} α)) (Prod.fst.{u3, u1} (Set.{u3} α) ι Si) 𝔖) (p (Prod.snd.{u3, u1} (Set.{u3} α) ι Si))) (fun (Si : Prod.{u3, u1} (Set.{u3} α) ι) => setOf.{max u3 u2} (UniformOnFun.{u3, u2} α G 𝔖) (fun (f : UniformOnFun.{u3, u2} α G 𝔖) => forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x (Prod.fst.{u3, u1} (Set.{u3} α) ι Si)) -> (Membership.mem.{u2, u2} G (Set.{u2} G) (Set.instMembershipSet.{u2} G) (f x) (b (Prod.snd.{u3, u1} (Set.{u3} α) ι Si)))))))
Case conversion may be inaccurate. Consider using '#align uniform_on_fun.has_basis_nhds_one_of_basis UniformOnFun.hasBasis_nhds_one_of_basisₓ'. -/
@[to_additive]
protected theorem UniformOnFun.hasBasis_nhds_one_of_basis (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) {p : ι → Prop} {b : ι → Set G}
    (h : (𝓝 1 : Filter G).HasBasis p b) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis (fun Si : Set α × ι => Si.1 ∈ 𝔖 ∧ p Si.2) fun Si =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  by
  have := h.comap fun p : G × G => p.1 / p.2
  rw [← uniformity_eq_comap_nhds_one_swapped] at this
  convert UniformOnFun.hasBasis_nhds_of_basis α _ 𝔖 1 h𝔖₁ h𝔖₂ this
  ext (i f)
  simp [UniformOnFun.gen]
#align uniform_on_fun.has_basis_nhds_one_of_basis UniformOnFun.hasBasis_nhds_one_of_basis
#align uniform_on_fun.has_basis_nhds_zero_of_basis UniformOnFun.hasBasis_nhds_zero_of_basis

/- warning: uniform_on_fun.has_basis_nhds_one -> UniformOnFun.hasBasis_nhds_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : UniformSpace.{u2} G] [_inst_3 : UniformGroup.{u2} G _inst_2 _inst_1] (𝔖 : Set.{u1} (Set.{u1} α)), (Set.Nonempty.{u1} (Set.{u1} α) 𝔖) -> (DirectedOn.{u1} (Set.{u1} α) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α)) 𝔖) -> (Filter.HasBasis.{max u1 u2, max (succ u1) (succ u2)} (UniformOnFun.{u1, u2} α G 𝔖) (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} G)) (nhds.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (UniformOnFun.topologicalSpace.{u1, u2} α G _inst_2 𝔖) (OfNat.ofNat.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) 1 (OfNat.mk.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) 1 (One.one.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (MulOneClass.toHasOne.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (Monoid.toMulOneClass.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (UniformOnFun.monoid.{u1, u2} α G 𝔖 (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))))))) (fun (SV : Prod.{u1, u2} (Set.{u1} α) (Set.{u2} G)) => And (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} G) SV) 𝔖) (Membership.Mem.{u2, u2} (Set.{u2} G) (Filter.{u2} G) (Filter.hasMem.{u2} G) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} G) SV) (nhds.{u2} G (UniformSpace.toTopologicalSpace.{u2} G _inst_2) (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))))))))) (fun (SV : Prod.{u1, u2} (Set.{u1} α) (Set.{u2} G)) => setOf.{max u1 u2} (UniformOnFun.{u1, u2} α G 𝔖) (fun (f : UniformOnFun.{u1, u2} α G 𝔖) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} G) SV)) -> (Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) (f x) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} G) SV)))))
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : UniformSpace.{u1} G] [_inst_3 : UniformGroup.{u1} G _inst_2 _inst_1] (𝔖 : Set.{u2} (Set.{u2} α)), (Set.Nonempty.{u2} (Set.{u2} α) 𝔖) -> (DirectedOn.{u2} (Set.{u2} α) (fun (x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1656 : Set.{u2} α) (x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1658 : Set.{u2} α) => HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1656 x._@.Mathlib.Topology.Algebra.UniformConvergence._hyg.1658) 𝔖) -> (Filter.HasBasis.{max u2 u1, max (succ u2) (succ u1)} (UniformOnFun.{u2, u1} α G 𝔖) (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} G)) (nhds.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (UniformOnFun.topologicalSpace.{u2, u1} α G _inst_2 𝔖) (OfNat.ofNat.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) 1 (One.toOfNat1.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (InvOneClass.toOne.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (DivInvOneMonoid.toInvOneClass.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (DivisionMonoid.toDivInvOneMonoid.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (Group.toDivisionMonoid.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (instGroupUniformOnFun.{u2, u1} α G 𝔖 _inst_1)))))))) (fun (SV : Prod.{u2, u1} (Set.{u2} α) (Set.{u1} G)) => And (Membership.mem.{u2, u2} (Set.{u2} α) (Set.{u2} (Set.{u2} α)) (Set.instMembershipSet.{u2} (Set.{u2} α)) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} G) SV) 𝔖) (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} G) SV) (nhds.{u1} G (UniformSpace.toTopologicalSpace.{u1} G _inst_2) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))))) (fun (SV : Prod.{u2, u1} (Set.{u2} α) (Set.{u1} G)) => setOf.{max u2 u1} (UniformOnFun.{u2, u1} α G 𝔖) (fun (f : UniformOnFun.{u2, u1} α G 𝔖) => forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} G) SV)) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (f x) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} G) SV)))))
Case conversion may be inaccurate. Consider using '#align uniform_on_fun.has_basis_nhds_one UniformOnFun.hasBasis_nhds_oneₓ'. -/
@[to_additive]
protected theorem UniformOnFun.hasBasis_nhds_one (𝔖 : Set <| Set α) (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) :
    (𝓝 1 : Filter (α →ᵤ[𝔖] G)).HasBasis
      (fun SV : Set α × Set G => SV.1 ∈ 𝔖 ∧ SV.2 ∈ (𝓝 1 : Filter G)) fun SV =>
      { f : α →ᵤ[𝔖] G | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  UniformOnFun.hasBasis_nhds_one_of_basis 𝔖 h𝔖₁ h𝔖₂ (basis_sets _)
#align uniform_on_fun.has_basis_nhds_one UniformOnFun.hasBasis_nhds_one
#align uniform_on_fun.has_basis_nhds_zero UniformOnFun.hasBasis_nhds_zero

end Group

section Module

variable (𝕜 α E H : Type _) {hom : Type _} [NormedField 𝕜] [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace H] [UniformSpace E] [UniformAddGroup E]
  [ContinuousSMul 𝕜 E] {𝔖 : Set <| Set α} [LinearMapClass hom 𝕜 H (α →ᵤ[𝔖] E)]

/- warning: uniform_on_fun.has_continuous_smul_induced_of_image_bounded -> UniformOnFun.continuousSMul_induced_of_image_bounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align uniform_on_fun.has_continuous_smul_induced_of_image_bounded UniformOnFun.continuousSMul_induced_of_image_boundedₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

For convenience, we don't literally ask for `H : submodule (α →ᵤ[𝔖] E)`. Instead, we prove the
result for any vector space `H` equipped with a linear inducing to `α →ᵤ[𝔖] E`, which is often
easier to use. We also state the `submodule` version as
`uniform_on_fun.has_continuous_smul_submodule_of_image_bounded`. -/
theorem UniformOnFun.continuousSMul_induced_of_image_bounded (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (φ : hom) (hφ : Inducing φ)
    (h : ∀ u : H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 ((φ u : α → E) '' s)) : ContinuousSMul 𝕜 H :=
  by
  have : TopologicalAddGroup H := by
    rw [hφ.induced]
    exact topologicalAddGroup_induced φ
  have : (𝓝 0 : Filter H).HasBasis _ _ :=
    by
    rw [hφ.induced, nhds_induced, map_zero]
    exact (UniformOnFun.hasBasis_nhds_zero 𝔖 h𝔖₁ h𝔖₂).comap φ
  refine' ContinuousSMul.of_basis_zero this _ _ _
  · rintro ⟨S, V⟩ ⟨hS, hV⟩
    have : tendsto (fun kx : 𝕜 × E => kx.1 • kx.2) (𝓝 (0, 0)) (𝓝 <| (0 : 𝕜) • 0) :=
      continuous_smul.tendsto (0 : 𝕜 × E)
    rw [zero_smul, nhds_prod_eq] at this
    have := this hV
    rw [mem_map, mem_prod_iff] at this
    rcases this with ⟨U, hU, W, hW, hUW⟩
    refine' ⟨U, hU, ⟨S, W⟩, ⟨hS, hW⟩, _⟩
    rw [Set.smul_subset_iff]
    intro a ha u hu x hx
    rw [SMulHomClass.map_smul]
    exact hUW (⟨ha, hu x hx⟩ : (a, φ u x) ∈ U ×ˢ W)
  · rintro a ⟨S, V⟩ ⟨hS, hV⟩
    have : tendsto (fun x : E => a • x) (𝓝 0) (𝓝 <| a • 0) := tendsto_id.const_smul a
    rw [smul_zero] at this
    refine' ⟨⟨S, (· • ·) a ⁻¹' V⟩, ⟨hS, this hV⟩, fun f hf x hx => _⟩
    rw [SMulHomClass.map_smul]
    exact hf x hx
  · rintro u ⟨S, V⟩ ⟨hS, hV⟩
    rcases h u S hS hV with ⟨r, hrpos, hr⟩
    rw [Metric.eventually_nhds_iff_ball]
    refine' ⟨r⁻¹, inv_pos.mpr hrpos, fun a ha x hx => _⟩
    by_cases ha0 : a = 0
    · rw [ha0]
      simp [mem_of_mem_nhds hV]
    · rw [mem_ball_zero_iff] at ha
      rw [SMulHomClass.map_smul, Pi.smul_apply]
      have : φ u x ∈ a⁻¹ • V :=
        by
        have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr ha0
        refine' (hr a⁻¹ _) (Set.mem_image_of_mem (φ u) hx)
        rw [norm_inv, le_inv hrpos ha0]
        exact ha.le
      rwa [Set.mem_inv_smul_set_iff₀ ha0] at this
#align uniform_on_fun.has_continuous_smul_induced_of_image_bounded UniformOnFun.continuousSMul_induced_of_image_bounded

/- warning: uniform_on_fun.has_continuous_smul_submodule_of_image_bounded -> UniformOnFun.continuousSMul_submodule_of_image_bounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align uniform_on_fun.has_continuous_smul_submodule_of_image_bounded UniformOnFun.continuousSMul_submodule_of_image_boundedₓ'. -/
/-- Let `E` be a TVS, `𝔖 : set (set α)` and `H` a submodule of `α →ᵤ[𝔖] E`. If the image of any
`S ∈ 𝔖` by any `u ∈ H` is bounded (in the sense of `bornology.is_vonN_bounded`), then `H`,
equipped with the topology of `𝔖`-convergence, is a TVS.

If you have a hard time using this lemma, try the one above instead. -/
theorem UniformOnFun.continuousSMul_submodule_of_image_bounded (h𝔖₁ : 𝔖.Nonempty)
    (h𝔖₂ : DirectedOn (· ⊆ ·) 𝔖) (H : Submodule 𝕜 (α →ᵤ[𝔖] E))
    (h : ∀ u ∈ H, ∀ s ∈ 𝔖, Bornology.IsVonNBounded 𝕜 (u '' s)) :
    @ContinuousSMul 𝕜 H _ _ ((UniformOnFun.topologicalSpace α E 𝔖).induced (coe : H → α →ᵤ[𝔖] E)) :=
  haveI : TopologicalAddGroup H :=
    topologicalAddGroup_induced (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E)
  UniformOnFun.continuousSMul_induced_of_image_bounded 𝕜 α E H h𝔖₁ h𝔖₂
    (linear_map.id.dom_restrict H : H →ₗ[𝕜] α → E) inducing_subtype_val fun ⟨u, hu⟩ => h u hu
#align uniform_on_fun.has_continuous_smul_submodule_of_image_bounded UniformOnFun.continuousSMul_submodule_of_image_bounded

end Module

