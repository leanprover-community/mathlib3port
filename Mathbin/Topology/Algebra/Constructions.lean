/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.algebra.constructions
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homeomorph

/-!
# Topological space structure on the opposite monoid and on the units group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `topological_space` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `add_units M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `has_continuous_mul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

topological space, opposite monoid, units
-/


variable {M X : Type _}

open Filter

open Topology

namespace MulOpposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive
      "Put the same topological space structure on the opposite monoid as on the original\nspace."]
instance [TopologicalSpace M] : TopologicalSpace Mᵐᵒᵖ :=
  TopologicalSpace.induced (unop : Mᵐᵒᵖ → M) ‹_›

variable [TopologicalSpace M]

#print MulOpposite.continuous_unop /-
@[continuity, to_additive]
theorem continuous_unop : Continuous (unop : Mᵐᵒᵖ → M) :=
  continuous_induced_dom
#align mul_opposite.continuous_unop MulOpposite.continuous_unop
#align add_opposite.continuous_unop AddOpposite.continuous_unop
-/

#print MulOpposite.continuous_op /-
@[continuity, to_additive]
theorem continuous_op : Continuous (op : M → Mᵐᵒᵖ) :=
  continuous_induced_rng.2 continuous_id
#align mul_opposite.continuous_op MulOpposite.continuous_op
#align add_opposite.continuous_op AddOpposite.continuous_op
-/

#print MulOpposite.opHomeomorph /-
/-- `mul_opposite.op` as a homeomorphism. -/
@[to_additive "`add_opposite.op` as a homeomorphism.", simps]
def opHomeomorph : M ≃ₜ Mᵐᵒᵖ where
  toEquiv := opEquiv
  continuous_toFun := continuous_op
  continuous_invFun := continuous_unop
#align mul_opposite.op_homeomorph MulOpposite.opHomeomorph
#align add_opposite.op_homeomorph AddOpposite.opHomeomorph
-/

@[to_additive]
instance [T2Space M] : T2Space Mᵐᵒᵖ :=
  opHomeomorph.symm.Embedding.T2Space

#print MulOpposite.map_op_nhds /-
@[simp, to_additive]
theorem map_op_nhds (x : M) : map (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.map_nhds_eq x
#align mul_opposite.map_op_nhds MulOpposite.map_op_nhds
#align add_opposite.map_op_nhds AddOpposite.map_op_nhds
-/

#print MulOpposite.map_unop_nhds /-
@[simp, to_additive]
theorem map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.symm.map_nhds_eq x
#align mul_opposite.map_unop_nhds MulOpposite.map_unop_nhds
#align add_opposite.map_unop_nhds AddOpposite.map_unop_nhds
-/

#print MulOpposite.comap_op_nhds /-
@[simp, to_additive]
theorem comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
  opHomeomorph.comap_nhds_eq x
#align mul_opposite.comap_op_nhds MulOpposite.comap_op_nhds
#align add_opposite.comap_op_nhds AddOpposite.comap_op_nhds
-/

#print MulOpposite.comap_unop_nhds /-
@[simp, to_additive]
theorem comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (op x) :=
  opHomeomorph.symm.comap_nhds_eq x
#align mul_opposite.comap_unop_nhds MulOpposite.comap_unop_nhds
#align add_opposite.comap_unop_nhds AddOpposite.comap_unop_nhds
-/

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace M] [Monoid M] [TopologicalSpace X]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive
      "The additive units of a monoid are equipped with a topology, via the embedding into\n`M × M`."]
instance : TopologicalSpace Mˣ :=
  Prod.topologicalSpace.induced (embedProduct M)

/- warning: units.inducing_embed_product -> Units.inducing_embedProduct is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Inducing.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.topologicalSpace.{u1} M _inst_1 _inst_2) (Prod.topologicalSpace.{u1, u1} M (MulOpposite.{u1} M) _inst_1 (MulOpposite.topologicalSpace.{u1} M _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (fun (_x : MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) => (Units.{u1} M _inst_2) -> (Prod.{u1, u1} M (MulOpposite.{u1} M))) (MonoidHom.hasCoeToFun.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.embedProduct.{u1} M _inst_2))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Inducing.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instTopologicalSpaceUnits.{u1} M _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u1} M (MulOpposite.{u1} M) _inst_1 (MulOpposite.instTopologicalSpaceMulOpposite.{u1} M _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (fun (_x : Units.{u1} M _inst_2) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Units.{u1} M _inst_2) => Prod.{u1, u1} M (MulOpposite.{u1} M)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_2) (Units.instMulOneClassUnits.{u1} M _inst_2)) (MulOneClass.toMul.{u1} (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2))) (MonoidHom.monoidHomClass.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))))) (Units.embedProduct.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align units.inducing_embed_product Units.inducing_embedProductₓ'. -/
@[to_additive]
theorem inducing_embedProduct : Inducing (embedProduct M) :=
  ⟨rfl⟩
#align units.inducing_embed_product Units.inducing_embedProduct
#align add_units.inducing_embed_product AddUnits.inducing_embedProduct

/- warning: units.embedding_embed_product -> Units.embedding_embedProduct is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Embedding.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.topologicalSpace.{u1} M _inst_1 _inst_2) (Prod.topologicalSpace.{u1, u1} M (MulOpposite.{u1} M) _inst_1 (MulOpposite.topologicalSpace.{u1} M _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (fun (_x : MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) => (Units.{u1} M _inst_2) -> (Prod.{u1, u1} M (MulOpposite.{u1} M))) (MonoidHom.hasCoeToFun.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.embedProduct.{u1} M _inst_2))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Embedding.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instTopologicalSpaceUnits.{u1} M _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u1} M (MulOpposite.{u1} M) _inst_1 (MulOpposite.instTopologicalSpaceMulOpposite.{u1} M _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (fun (_x : Units.{u1} M _inst_2) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Units.{u1} M _inst_2) => Prod.{u1, u1} M (MulOpposite.{u1} M)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_2) (Units.instMulOneClassUnits.{u1} M _inst_2)) (MulOneClass.toMul.{u1} (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2))) (MonoidHom.monoidHomClass.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))))) (Units.embedProduct.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align units.embedding_embed_product Units.embedding_embedProductₓ'. -/
@[to_additive]
theorem embedding_embedProduct : Embedding (embedProduct M) :=
  ⟨inducing_embedProduct, embedProduct_injective M⟩
#align units.embedding_embed_product Units.embedding_embedProduct
#align add_units.embedding_embed_product AddUnits.embedding_embedProduct

/- warning: units.continuous_embed_product -> Units.continuous_embedProduct is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Continuous.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.topologicalSpace.{u1} M _inst_1 _inst_2) (Prod.topologicalSpace.{u1, u1} M (MulOpposite.{u1} M) _inst_1 (MulOpposite.topologicalSpace.{u1} M _inst_1)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (fun (_x : MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) => (Units.{u1} M _inst_2) -> (Prod.{u1, u1} M (MulOpposite.{u1} M))) (MonoidHom.hasCoeToFun.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.mulOneClass.{u1} M _inst_2) (Prod.mulOneClass.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.mulOneClass.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.embedProduct.{u1} M _inst_2))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Continuous.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instTopologicalSpaceUnits.{u1} M _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u1} M (MulOpposite.{u1} M) _inst_1 (MulOpposite.instTopologicalSpaceMulOpposite.{u1} M _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (fun (_x : Units.{u1} M _inst_2) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Units.{u1} M _inst_2) => Prod.{u1, u1} M (MulOpposite.{u1} M)) _x) (MulHomClass.toFunLike.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_2) (Units.instMulOneClassUnits.{u1} M _inst_2)) (MulOneClass.toMul.{u1} (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (MonoidHomClass.toMulHomClass.{u1, u1, u1} (MonoidHom.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))) (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2))) (MonoidHom.monoidHomClass.{u1, u1} (Units.{u1} M _inst_2) (Prod.{u1, u1} M (MulOpposite.{u1} M)) (Units.instMulOneClassUnits.{u1} M _inst_2) (Prod.instMulOneClassProd.{u1, u1} M (MulOpposite.{u1} M) (Monoid.toMulOneClass.{u1} M _inst_2) (MulOpposite.instMulOneClassMulOpposite.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)))))) (Units.embedProduct.{u1} M _inst_2))
Case conversion may be inaccurate. Consider using '#align units.continuous_embed_product Units.continuous_embedProductₓ'. -/
@[to_additive]
theorem continuous_embedProduct : Continuous (embedProduct M) :=
  continuous_induced_dom
#align units.continuous_embed_product Units.continuous_embedProduct
#align add_units.continuous_embed_product AddUnits.continuous_embedProduct

/- warning: units.continuous_coe -> Units.continuous_val is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Continuous.{u1, u1} (Units.{u1} M _inst_2) M (Units.topologicalSpace.{u1} M _inst_1 _inst_2) _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_2) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_2) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_2) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_2) M (Units.hasCoe.{u1} M _inst_2)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Continuous.{u1, u1} (Units.{u1} M _inst_2) M (Units.instTopologicalSpaceUnits.{u1} M _inst_1 _inst_2) _inst_1 (Units.val.{u1} M _inst_2)
Case conversion may be inaccurate. Consider using '#align units.continuous_coe Units.continuous_valₓ'. -/
@[to_additive]
theorem continuous_val : Continuous (coe : Mˣ → M) :=
  (@continuous_embedProduct M _ _).fst
#align units.continuous_coe Units.continuous_val
#align add_units.continuous_coe AddUnits.continuous_val

/- warning: units.continuous_iff -> Units.continuous_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {X : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u2} X] {f : X -> (Units.{u1} M _inst_2)}, Iff (Continuous.{u2, u1} X (Units.{u1} M _inst_2) _inst_3 (Units.topologicalSpace.{u1} M _inst_1 _inst_2) f) (And (Continuous.{u2, u1} X M _inst_3 _inst_1 (Function.comp.{succ u2, succ u1, succ u1} X (Units.{u1} M _inst_2) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_2) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_2) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_2) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_2) M (Units.hasCoe.{u1} M _inst_2))))) f)) (Continuous.{u2, u1} X M _inst_3 _inst_1 (fun (x : X) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_2) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_2) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_2) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_2) M (Units.hasCoe.{u1} M _inst_2)))) (Inv.inv.{u1} (Units.{u1} M _inst_2) (Units.hasInv.{u1} M _inst_2) (f x)))))
but is expected to have type
  forall {M : Type.{u2}} {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} M] [_inst_2 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u1} X] {f : X -> (Units.{u2} M _inst_2)}, Iff (Continuous.{u1, u2} X (Units.{u2} M _inst_2) _inst_3 (Units.instTopologicalSpaceUnits.{u2} M _inst_1 _inst_2) f) (And (Continuous.{u1, u2} X M _inst_3 _inst_1 (Function.comp.{succ u1, succ u2, succ u2} X (Units.{u2} M _inst_2) M (Units.val.{u2} M _inst_2) f)) (Continuous.{u1, u2} X M _inst_3 _inst_1 (fun (x : X) => Units.val.{u2} M _inst_2 (Inv.inv.{u2} (Units.{u2} M _inst_2) (Units.instInvUnits.{u2} M _inst_2) (f x)))))
Case conversion may be inaccurate. Consider using '#align units.continuous_iff Units.continuous_iffₓ'. -/
@[to_additive]
protected theorem continuous_iff {f : X → Mˣ} :
    Continuous f ↔ Continuous (coe ∘ f : X → M) ∧ Continuous (fun x => ↑(f x)⁻¹ : X → M) := by
  simp only [inducing_embed_product.continuous_iff, embed_product_apply, (· ∘ ·),
    continuous_prod_mk, op_homeomorph.symm.inducing.continuous_iff, op_homeomorph_symm_apply,
    unop_op]
#align units.continuous_iff Units.continuous_iff
#align add_units.continuous_iff AddUnits.continuous_iff

/- warning: units.continuous_coe_inv -> Units.continuous_coe_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Continuous.{u1, u1} (Units.{u1} M _inst_2) M (Units.topologicalSpace.{u1} M _inst_1 _inst_2) _inst_1 (fun (u : Units.{u1} M _inst_2) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_2) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_2) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_2) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_2) M (Units.hasCoe.{u1} M _inst_2)))) (Inv.inv.{u1} (Units.{u1} M _inst_2) (Units.hasInv.{u1} M _inst_2) u))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} M] [_inst_2 : Monoid.{u1} M], Continuous.{u1, u1} (Units.{u1} M _inst_2) M (Units.instTopologicalSpaceUnits.{u1} M _inst_1 _inst_2) _inst_1 (fun (u : Units.{u1} M _inst_2) => Units.val.{u1} M _inst_2 (Inv.inv.{u1} (Units.{u1} M _inst_2) (Units.instInvUnits.{u1} M _inst_2) u))
Case conversion may be inaccurate. Consider using '#align units.continuous_coe_inv Units.continuous_coe_invₓ'. -/
@[to_additive]
theorem continuous_coe_inv : Continuous (fun u => ↑u⁻¹ : Mˣ → M) :=
  (Units.continuous_iff.1 continuous_id).2
#align units.continuous_coe_inv Units.continuous_coe_inv
#align add_units.continuous_coe_neg AddUnits.continuous_coe_neg

end Units

