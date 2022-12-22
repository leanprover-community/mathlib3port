/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.algebra.constructions
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homeomorph

/-!
# Topological space structure on the opposite monoid and on the units group

In this file we define `topological_space` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `add_units M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `has_continuous_mul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

topological space, opposite monoid, units
-/


variable {M X : Type _}

open Filter

open TopologicalSpace

namespace MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive
      "Put the same topological space structure on the opposite monoid as on the original\nspace."]
instance [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ → M) ‹_›

variable [TopologicalSpace M]

@[continuity, to_additive]
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) :=
  continuous_induced_dom
#align mul_opposite.continuous_unop MulOpposite.continuous_unop

@[continuity, to_additive]
theorem continuous_op : Continuous (op : M → Mᵐᵒᵖ) :=
  continuous_induced_rng.2 continuous_id
#align mul_opposite.continuous_op MulOpposite.continuous_op

/-- `mul_opposite.op` as a homeomorphism. -/
@[to_additive "`add_opposite.op` as a homeomorphism.", simps]
def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where 
  toEquiv := opEquiv
  continuous_to_fun := continuous_op
  continuous_inv_fun := continuous_unop
#align mul_opposite.op_homeomorph MulOpposite.opHomeomorph

@[to_additive]
instance [T2Space M] : T2Space Mᵐᵒᵖ :=
  opHomeomorph.symm.Embedding.T2Space

@[simp, to_additive]
theorem map_op_nhds (x : M) : map (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.map_nhds_eq x
#align mul_opposite.map_op_nhds MulOpposite.map_op_nhds

@[simp, to_additive]
theorem map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.symm.map_nhds_eq x
#align mul_opposite.map_unop_nhds MulOpposite.map_unop_nhds

@[simp, to_additive]
theorem comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.comap_nhds_eq x
#align mul_opposite.comap_op_nhds MulOpposite.comap_op_nhds

@[simp, to_additive]
theorem comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.symm.comap_nhds_eq x
#align mul_opposite.comap_unop_nhds MulOpposite.comap_unop_nhds

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace M] [Monoid M] [TopologicalSpace X]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive
      "The additive units of a monoid are equipped with a topology, via the embedding into\n`M × M`."]
instance : TopologicalSpace Mˣ :=
  Prod.topologicalSpace.induced (embedProduct M)

@[to_additive]
theorem inducing_embed_product : Inducing (embedProduct M) :=
  ⟨rfl⟩
#align units.inducing_embed_product Units.inducing_embed_product

@[to_additive]
theorem embedding_embed_product : Embedding (embedProduct M) :=
  ⟨inducing_embed_product, embedProduct_injective M⟩
#align units.embedding_embed_product Units.embedding_embed_product

@[to_additive]
theorem continuous_embed_product : Continuous (embedProduct M) :=
  continuous_induced_dom
#align units.continuous_embed_product Units.continuous_embed_product

@[to_additive]
theorem continuous_coe : Continuous (coe : Mˣ → M) :=
  (@continuous_embed_product M _ _).fst
#align units.continuous_coe Units.continuous_coe

@[to_additive]
protected theorem continuous_iff {f : X → Mˣ} :
    Continuous f ↔ Continuous (coe ∘ f : X → M) ∧ Continuous (fun x => ↑(f x)⁻¹ : X → M) := by
  simp only [inducing_embed_product.continuous_iff, embed_product_apply, (· ∘ ·),
    continuous_prod_mk, op_homeomorph.symm.inducing.continuous_iff, op_homeomorph_symm_apply,
    unop_op]
#align units.continuous_iff Units.continuous_iff

@[to_additive]
theorem continuous_coe_inv : Continuous (fun u => ↑u⁻¹ : Mˣ → M) :=
  (Units.continuous_iff.1 continuous_id).2
#align units.continuous_coe_inv Units.continuous_coe_inv

end Units

