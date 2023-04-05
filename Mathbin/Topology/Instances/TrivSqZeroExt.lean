/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module topology.instances.triv_sq_zero_ext
! leanprover-community/mathlib commit b8d2eaa69d69ce8f03179a5cda774fc0cde984e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.TrivSqZeroExt
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Topology on `triv_sq_zero_ext R M`

The type `triv_sq_zero_ext R M` inherits the topology from `R × M`.

Note that this is not the topology induced by the seminorm on the dual numbers suggested by
[this Math.SE answer](https://math.stackexchange.com/a/1056378/1896), which instead induces
the topology pulled back through the projection map `triv_sq_zero_ext.fst : tsze R M → R`.
Obviously, that topology is not Hausdorff and using it would result in `exp` converging to more than
one value.

## Main results

* `triv_sq_zero_ext.topological_ring`: the ring operations are continuous

-/


variable {α S R M : Type _}

-- mathport name: exprtsze
local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

variable [TopologicalSpace R] [TopologicalSpace M]

instance : TopologicalSpace (tsze R M) :=
  TopologicalSpace.induced fst ‹_› ⊓ TopologicalSpace.induced snd ‹_›

instance [T2Space R] [T2Space M] : T2Space (tsze R M) :=
  Prod.t2Space

/- warning: triv_sq_zero_ext.nhds_def -> TrivSqZeroExt.nhds_def is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] (x : TrivSqZeroExt.{u1, u2} R M), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M)) (nhds.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) x) (Filter.prod.{u1, u2} R M (nhds.{u1} R _inst_1 (TrivSqZeroExt.fst.{u1, u2} R M x)) (nhds.{u2} M _inst_2 (TrivSqZeroExt.snd.{u1, u2} R M x)))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M] (x : TrivSqZeroExt.{u2, u1} R M), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (TrivSqZeroExt.{u2, u1} R M)) (nhds.{max u2 u1} (TrivSqZeroExt.{u2, u1} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) x) (Filter.prod.{u2, u1} R M (nhds.{u2} R _inst_1 (TrivSqZeroExt.fst.{u2, u1} R M x)) (nhds.{u1} M _inst_2 (TrivSqZeroExt.snd.{u2, u1} R M x)))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.nhds_def TrivSqZeroExt.nhds_defₓ'. -/
theorem nhds_def (x : tsze R M) : nhds x = (nhds x.fst).Prod (nhds x.snd) := by
  cases x <;> exact nhds_prod_eq
#align triv_sq_zero_ext.nhds_def TrivSqZeroExt.nhds_def

/- warning: triv_sq_zero_ext.nhds_inl -> TrivSqZeroExt.nhds_inl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u2} M] (x : R), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M)) (nhds.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inl.{u1, u2} R M _inst_3 x)) (Filter.prod.{u1, u2} R M (nhds.{u1} R _inst_1 x) (nhds.{u2} M _inst_2 (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_3)))))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u2} M] (x : R), Eq.{max (succ u1) (succ u2)} (Filter.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M)) (nhds.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inl.{u1, u2} R M _inst_3 x)) (Filter.prod.{u1, u2} R M (nhds.{u1} R _inst_1 x) (nhds.{u2} M _inst_2 (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M _inst_3))))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.nhds_inl TrivSqZeroExt.nhds_inlₓ'. -/
theorem nhds_inl [Zero M] (x : R) : nhds (inl x : tsze R M) = (nhds x).Prod (nhds 0) :=
  nhds_def _
#align triv_sq_zero_ext.nhds_inl TrivSqZeroExt.nhds_inl

/- warning: triv_sq_zero_ext.nhds_inr -> TrivSqZeroExt.nhds_inr is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u1} R] (m : M), Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M)) (nhds.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inr.{u1, u2} R M _inst_3 m)) (Filter.prod.{u1, u2} R M (nhds.{u1} R _inst_1 (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R _inst_3)))) (nhds.{u2} M _inst_2 m))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Zero.{u2} R] (m : M), Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (TrivSqZeroExt.{u2, u1} R M)) (nhds.{max u2 u1} (TrivSqZeroExt.{u2, u1} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) (TrivSqZeroExt.inr.{u2, u1} R M _inst_3 m)) (Filter.prod.{u2, u1} R M (nhds.{u2} R _inst_1 (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R _inst_3))) (nhds.{u1} M _inst_2 m))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.nhds_inr TrivSqZeroExt.nhds_inrₓ'. -/
theorem nhds_inr [Zero R] (m : M) : nhds (inr m : tsze R M) = (nhds 0).Prod (nhds m) :=
  nhds_def _
#align triv_sq_zero_ext.nhds_inr TrivSqZeroExt.nhds_inr

/- warning: triv_sq_zero_ext.continuous_fst -> TrivSqZeroExt.continuous_fst is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M], Continuous.{max u1 u2, u1} (TrivSqZeroExt.{u1, u2} R M) R (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) _inst_1 (TrivSqZeroExt.fst.{u1, u2} R M)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M], Continuous.{max u2 u1, u2} (TrivSqZeroExt.{u2, u1} R M) R (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) _inst_1 (TrivSqZeroExt.fst.{u2, u1} R M)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.continuous_fst TrivSqZeroExt.continuous_fstₓ'. -/
theorem continuous_fst : Continuous (fst : tsze R M → R) :=
  continuous_fst
#align triv_sq_zero_ext.continuous_fst TrivSqZeroExt.continuous_fst

/- warning: triv_sq_zero_ext.continuous_snd -> TrivSqZeroExt.continuous_snd is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M], Continuous.{max u1 u2, u2} (TrivSqZeroExt.{u1, u2} R M) M (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) _inst_2 (TrivSqZeroExt.snd.{u1, u2} R M)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M], Continuous.{max u2 u1, u1} (TrivSqZeroExt.{u2, u1} R M) M (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) _inst_2 (TrivSqZeroExt.snd.{u2, u1} R M)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.continuous_snd TrivSqZeroExt.continuous_sndₓ'. -/
theorem continuous_snd : Continuous (snd : tsze R M → M) :=
  continuous_snd
#align triv_sq_zero_ext.continuous_snd TrivSqZeroExt.continuous_snd

/- warning: triv_sq_zero_ext.continuous_inl -> TrivSqZeroExt.continuous_inl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u2} M], Continuous.{u1, max u1 u2} R (TrivSqZeroExt.{u1, u2} R M) _inst_1 (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inl.{u1, u2} R M _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u2} M], Continuous.{u1, max u1 u2} R (TrivSqZeroExt.{u1, u2} R M) _inst_1 (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inl.{u1, u2} R M _inst_3)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.continuous_inl TrivSqZeroExt.continuous_inlₓ'. -/
theorem continuous_inl [Zero M] : Continuous (inl : R → tsze R M) :=
  continuous_id.prod_mk continuous_const
#align triv_sq_zero_ext.continuous_inl TrivSqZeroExt.continuous_inl

/- warning: triv_sq_zero_ext.continuous_inr -> TrivSqZeroExt.continuous_inr is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u1} R], Continuous.{u2, max u1 u2} M (TrivSqZeroExt.{u1, u2} R M) _inst_2 (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inr.{u1, u2} R M _inst_3)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Zero.{u2} R], Continuous.{u1, max u2 u1} M (TrivSqZeroExt.{u2, u1} R M) _inst_2 (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) (TrivSqZeroExt.inr.{u2, u1} R M _inst_3)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.continuous_inr TrivSqZeroExt.continuous_inrₓ'. -/
theorem continuous_inr [Zero R] : Continuous (inr : M → tsze R M) :=
  continuous_const.prod_mk continuous_id
#align triv_sq_zero_ext.continuous_inr TrivSqZeroExt.continuous_inr

/- warning: triv_sq_zero_ext.embedding_inl -> TrivSqZeroExt.embedding_inl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u2} M], Embedding.{u1, max u1 u2} R (TrivSqZeroExt.{u1, u2} R M) _inst_1 (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inl.{u1, u2} R M _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u2} M], Embedding.{u1, max u1 u2} R (TrivSqZeroExt.{u1, u2} R M) _inst_1 (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inl.{u1, u2} R M _inst_3)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.embedding_inl TrivSqZeroExt.embedding_inlₓ'. -/
theorem embedding_inl [Zero M] : Embedding (inl : R → tsze R M) :=
  embedding_of_embedding_compose continuous_inl continuous_fst embedding_id
#align triv_sq_zero_ext.embedding_inl TrivSqZeroExt.embedding_inl

/- warning: triv_sq_zero_ext.embedding_inr -> TrivSqZeroExt.embedding_inr is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Zero.{u1} R], Embedding.{u2, max u1 u2} M (TrivSqZeroExt.{u1, u2} R M) _inst_2 (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.inr.{u1, u2} R M _inst_3)
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Zero.{u2} R], Embedding.{u1, max u2 u1} M (TrivSqZeroExt.{u2, u1} R M) _inst_2 (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) (TrivSqZeroExt.inr.{u2, u1} R M _inst_3)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.embedding_inr TrivSqZeroExt.embedding_inrₓ'. -/
theorem embedding_inr [Zero R] : Embedding (inr : M → tsze R M) :=
  embedding_of_embedding_compose continuous_inr continuous_snd embedding_id
#align triv_sq_zero_ext.embedding_inr TrivSqZeroExt.embedding_inr

variable (R M)

/- warning: triv_sq_zero_ext.fst_clm -> TrivSqZeroExt.fstClm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, max u1 u2, u1} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, max u2 u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.fst_clm TrivSqZeroExt.fstClmₓ'. -/
/-- `triv_sq_zero_ext.fst` as a continuous linear map. -/
@[simps]
def fstClm [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] R :=
  { ContinuousLinearMap.fst R R M with toFun := fst }
#align triv_sq_zero_ext.fst_clm TrivSqZeroExt.fstClm

/- warning: triv_sq_zero_ext.snd_clm -> TrivSqZeroExt.sndClm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, max u1 u2, u2} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) M _inst_2 _inst_4 (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5) _inst_5
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, max u2 u1, u2} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) M _inst_2 _inst_4 (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5) _inst_5
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.snd_clm TrivSqZeroExt.sndClmₓ'. -/
/-- `triv_sq_zero_ext.snd` as a continuous linear map. -/
@[simps]
def sndClm [CommSemiring R] [AddCommMonoid M] [Module R M] : tsze R M →L[R] M :=
  { ContinuousLinearMap.snd R R M with
    toFun := snd
    cont := continuous_snd }
#align triv_sq_zero_ext.snd_clm TrivSqZeroExt.sndClm

/- warning: triv_sq_zero_ext.inl_clm -> TrivSqZeroExt.inlClm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, u1, max u1 u2} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5)
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, u1, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.inl_clm TrivSqZeroExt.inlClmₓ'. -/
/-- `triv_sq_zero_ext.inl` as a continuous linear map. -/
@[simps]
def inlClm [CommSemiring R] [AddCommMonoid M] [Module R M] : R →L[R] tsze R M :=
  { ContinuousLinearMap.inl R R M with toFun := inl }
#align triv_sq_zero_ext.inl_clm TrivSqZeroExt.inlClm

/- warning: triv_sq_zero_ext.inr_clm -> TrivSqZeroExt.inrClm is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, u2, max u1 u2} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) M _inst_2 _inst_4 (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) _inst_5 (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5)
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : CommSemiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_3) _inst_4], ContinuousLinearMap.{u1, u1, u2, max u2 u1} R R (CommSemiring.toSemiring.{u1} R _inst_3) (CommSemiring.toSemiring.{u1} R _inst_3) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3))) M _inst_2 _inst_4 (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u1, u2} R M _inst_1 _inst_2) (TrivSqZeroExt.addCommMonoid.{u1, u2} R M (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4) _inst_5 (TrivSqZeroExt.module.{u1, u2, u1} R R M (CommSemiring.toSemiring.{u1} R _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)))) _inst_4 (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_3)) _inst_5)
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.inr_clm TrivSqZeroExt.inrClmₓ'. -/
/-- `triv_sq_zero_ext.inr` as a continuous linear map. -/
@[simps]
def inrClm [CommSemiring R] [AddCommMonoid M] [Module R M] : M →L[R] tsze R M :=
  { ContinuousLinearMap.inr R R M with toFun := inr }
#align triv_sq_zero_ext.inr_clm TrivSqZeroExt.inrClm

variable {R M}

instance [Add R] [Add M] [ContinuousAdd R] [ContinuousAdd M] : ContinuousAdd (tsze R M) :=
  Prod.has_continuous_add

instance [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousMul R] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] [ContinuousAdd M] : ContinuousMul (tsze R M) :=
  ⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk <|
      ((continuous_fst.comp continuous_fst).smul (continuous_snd.comp continuous_snd)).add
        ((MulOpposite.continuous_op.comp <| continuous_fst.comp <| continuous_snd).smul
          (continuous_snd.comp continuous_fst))⟩

instance [Neg R] [Neg M] [ContinuousNeg R] [ContinuousNeg M] : ContinuousNeg (tsze R M) :=
  Prod.has_continuous_neg

/- warning: triv_sq_zero_ext.topological_semiring -> TrivSqZeroExt.topologicalSemiring is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : Semiring.{u1} R] [_inst_4 : AddCommMonoid.{u2} M] [_inst_5 : Module.{u1, u2} R M _inst_3 _inst_4] [_inst_6 : Module.{u1, u2} (MulOpposite.{u1} R) M (MulOpposite.semiring.{u1} R _inst_3) _inst_4] [_inst_7 : TopologicalSemiring.{u1} R _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))] [_inst_8 : ContinuousAdd.{u2} M _inst_2 (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)))] [_inst_9 : ContinuousSMul.{u1, u2} R M (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_3)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_3) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (Module.toMulActionWithZero.{u1, u2} R M _inst_3 _inst_4 _inst_5)))) _inst_1 _inst_2] [_inst_10 : ContinuousSMul.{u1, u2} (MulOpposite.{u1} R) M (SMulZeroClass.toHasSmul.{u1, u2} (MulOpposite.{u1} R) M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u1, u2} (MulOpposite.{u1} R) M (MulZeroClass.toHasZero.{u1} (MulOpposite.{u1} R) (MulZeroOneClass.toMulZeroClass.{u1} (MulOpposite.{u1} R) (MonoidWithZero.toMulZeroOneClass.{u1} (MulOpposite.{u1} R) (Semiring.toMonoidWithZero.{u1} (MulOpposite.{u1} R) (MulOpposite.semiring.{u1} R _inst_3))))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u1, u2} (MulOpposite.{u1} R) M (Semiring.toMonoidWithZero.{u1} (MulOpposite.{u1} R) (MulOpposite.semiring.{u1} R _inst_3)) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4))) (Module.toMulActionWithZero.{u1, u2} (MulOpposite.{u1} R) M (MulOpposite.semiring.{u1} R _inst_3) _inst_4 _inst_6)))) (MulOpposite.topologicalSpace.{u1} R _inst_1) _inst_2], TopologicalSemiring.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.topologicalSpace.{u1, u2} R M _inst_1 _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (TrivSqZeroExt.{u1, u2} R M) (TrivSqZeroExt.nonAssocSemiring.{u1, u2} R M _inst_3 _inst_4 _inst_5 _inst_6))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u1} M] [_inst_3 : Semiring.{u2} R] [_inst_4 : AddCommMonoid.{u1} M] [_inst_5 : Module.{u2, u1} R M _inst_3 _inst_4] [_inst_6 : Module.{u2, u1} (MulOpposite.{u2} R) M (MulOpposite.semiring.{u2} R _inst_3) _inst_4] [_inst_7 : TopologicalSemiring.{u2} R _inst_1 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3))] [_inst_8 : ContinuousAdd.{u1} M _inst_2 (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)))] [_inst_9 : ContinuousSMul.{u2, u1} R M (SMulZeroClass.toSMul.{u2, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u1} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u2, u1} R M (Semiring.toMonoidWithZero.{u2} R _inst_3) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u2, u1} R M _inst_3 _inst_4 _inst_5)))) _inst_1 _inst_2] [_inst_10 : ContinuousSMul.{u2, u1} (MulOpposite.{u2} R) M (SMulZeroClass.toSMul.{u2, u1} (MulOpposite.{u2} R) M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u2, u1} (MulOpposite.{u2} R) M (MulOpposite.zero.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3))) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u2, u1} (MulOpposite.{u2} R) M (MulOpposite.monoidWithZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u2, u1} (MulOpposite.{u2} R) M (MulOpposite.semiring.{u2} R _inst_3) _inst_4 _inst_6)))) (MulOpposite.instTopologicalSpaceMulOpposite.{u2} R _inst_1) _inst_2], TopologicalSemiring.{max u1 u2} (TrivSqZeroExt.{u2, u1} R M) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u2, u1} R M _inst_1 _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (TrivSqZeroExt.{u2, u1} R M) (TrivSqZeroExt.nonAssocSemiring.{u2, u1} R M _inst_3 _inst_4 _inst_5 _inst_6))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.topological_semiring TrivSqZeroExt.topologicalSemiringₓ'. -/
/-- This is not an instance due to complaints by the `fails_quickly` linter. At any rate, we only
really care about the `topological_ring` instance below. -/
theorem topologicalSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [TopologicalSemiring R] [ContinuousAdd M] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ
        M] :-- note: lean times out looking for the non_assoc_semiring instance without this hint
      @TopologicalSemiring
      (tsze R M) _ (NonAssocSemiring.toNonUnitalNonAssocSemiring _) :=
  { }
#align triv_sq_zero_ext.topological_semiring TrivSqZeroExt.topologicalSemiring

instance [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [TopologicalRing R]
    [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] :
    TopologicalRing (tsze R M) where

instance [SMul S R] [SMul S M] [ContinuousConstSMul S R] [ContinuousConstSMul S M] :
    ContinuousConstSMul S (tsze R M) :=
  Prod.continuousConstSMul

instance [TopologicalSpace S] [SMul S R] [SMul S M] [ContinuousSMul S R] [ContinuousSMul S M] :
    ContinuousSMul S (tsze R M) :=
  Prod.continuousSMul

variable (M)

/- warning: triv_sq_zero_ext.has_sum_inl -> TrivSqZeroExt.hasSum_inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} (M : Type.{u3}) [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : AddCommMonoid.{u2} R] [_inst_4 : AddCommMonoid.{u3} M] {f : α -> R} {a : R}, (HasSum.{u2, u1} R α _inst_3 _inst_1 f a) -> (HasSum.{max u2 u3, u1} (TrivSqZeroExt.{u2, u3} R M) α (TrivSqZeroExt.addCommMonoid.{u2, u3} R M _inst_3 _inst_4) (TrivSqZeroExt.topologicalSpace.{u2, u3} R M _inst_1 _inst_2) (fun (x : α) => TrivSqZeroExt.inl.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (f x)) (TrivSqZeroExt.inl.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) a))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u3}} (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u3} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : AddCommMonoid.{u3} R] [_inst_4 : AddCommMonoid.{u2} M] {f : α -> R} {a : R}, (HasSum.{u3, u1} R α _inst_3 _inst_1 f a) -> (HasSum.{max u2 u3, u1} (TrivSqZeroExt.{u3, u2} R M) α (TrivSqZeroExt.addCommMonoid.{u3, u2} R M _inst_3 _inst_4) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u3, u2} R M _inst_1 _inst_2) (fun (x : α) => TrivSqZeroExt.inl.{u3, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) (f x)) (TrivSqZeroExt.inl.{u3, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_4)) a))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.has_sum_inl TrivSqZeroExt.hasSum_inlₓ'. -/
theorem hasSum_inl [AddCommMonoid R] [AddCommMonoid M] {f : α → R} {a : R} (h : HasSum f a) :
    HasSum (fun x => inl (f x)) (inl a : tsze R M) :=
  h.map (⟨inl, inl_zero _, inl_add _⟩ : R →+ tsze R M) continuous_inl
#align triv_sq_zero_ext.has_sum_inl TrivSqZeroExt.hasSum_inl

/- warning: triv_sq_zero_ext.has_sum_inr -> TrivSqZeroExt.hasSum_inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} (M : Type.{u3}) [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : AddCommMonoid.{u2} R] [_inst_4 : AddCommMonoid.{u3} M] {f : α -> M} {a : M}, (HasSum.{u3, u1} M α _inst_4 _inst_2 f a) -> (HasSum.{max u2 u3, u1} (TrivSqZeroExt.{u2, u3} R M) α (TrivSqZeroExt.addCommMonoid.{u2, u3} R M _inst_3 _inst_4) (TrivSqZeroExt.topologicalSpace.{u2, u3} R M _inst_1 _inst_2) (fun (x : α) => TrivSqZeroExt.inr.{u2, u3} R M (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_3))) (f x)) (TrivSqZeroExt.inr.{u2, u3} R M (AddZeroClass.toHasZero.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R _inst_3))) a))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u3}} (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u3} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : AddCommMonoid.{u3} R] [_inst_4 : AddCommMonoid.{u2} M] {f : α -> M} {a : M}, (HasSum.{u2, u1} M α _inst_4 _inst_2 f a) -> (HasSum.{max u2 u3, u1} (TrivSqZeroExt.{u3, u2} R M) α (TrivSqZeroExt.addCommMonoid.{u3, u2} R M _inst_3 _inst_4) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u3, u2} R M _inst_1 _inst_2) (fun (x : α) => TrivSqZeroExt.inr.{u3, u2} R M (AddMonoid.toZero.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_3)) (f x)) (TrivSqZeroExt.inr.{u3, u2} R M (AddMonoid.toZero.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_3)) a))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.has_sum_inr TrivSqZeroExt.hasSum_inrₓ'. -/
theorem hasSum_inr [AddCommMonoid R] [AddCommMonoid M] {f : α → M} {a : M} (h : HasSum f a) :
    HasSum (fun x => inr (f x)) (inr a : tsze R M) :=
  h.map (⟨inr, inr_zero _, inr_add _⟩ : M →+ tsze R M) continuous_inr
#align triv_sq_zero_ext.has_sum_inr TrivSqZeroExt.hasSum_inr

/- warning: triv_sq_zero_ext.has_sum_fst -> TrivSqZeroExt.hasSum_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} (M : Type.{u3}) [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : AddCommMonoid.{u2} R] [_inst_4 : AddCommMonoid.{u3} M] {f : α -> (TrivSqZeroExt.{u2, u3} R M)} {a : TrivSqZeroExt.{u2, u3} R M}, (HasSum.{max u2 u3, u1} (TrivSqZeroExt.{u2, u3} R M) α (TrivSqZeroExt.addCommMonoid.{u2, u3} R M _inst_3 _inst_4) (TrivSqZeroExt.topologicalSpace.{u2, u3} R M _inst_1 _inst_2) f a) -> (HasSum.{u2, u1} R α _inst_3 _inst_1 (fun (x : α) => TrivSqZeroExt.fst.{u2, u3} R M (f x)) (TrivSqZeroExt.fst.{u2, u3} R M a))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u3}} (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u3} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : AddCommMonoid.{u3} R] [_inst_4 : AddCommMonoid.{u2} M] {f : α -> (TrivSqZeroExt.{u3, u2} R M)} {a : TrivSqZeroExt.{u3, u2} R M}, (HasSum.{max u3 u2, u1} (TrivSqZeroExt.{u3, u2} R M) α (TrivSqZeroExt.addCommMonoid.{u3, u2} R M _inst_3 _inst_4) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u3, u2} R M _inst_1 _inst_2) f a) -> (HasSum.{u3, u1} R α _inst_3 _inst_1 (fun (x : α) => TrivSqZeroExt.fst.{u3, u2} R M (f x)) (TrivSqZeroExt.fst.{u3, u2} R M a))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.has_sum_fst TrivSqZeroExt.hasSum_fstₓ'. -/
theorem hasSum_fst [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x => fst (f x)) (fst a) :=
  h.map (⟨fst, fst_zero, fst_add⟩ : tsze R M →+ R) continuous_fst
#align triv_sq_zero_ext.has_sum_fst TrivSqZeroExt.hasSum_fst

/- warning: triv_sq_zero_ext.has_sum_snd -> TrivSqZeroExt.hasSum_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {R : Type.{u2}} (M : Type.{u3}) [_inst_1 : TopologicalSpace.{u2} R] [_inst_2 : TopologicalSpace.{u3} M] [_inst_3 : AddCommMonoid.{u2} R] [_inst_4 : AddCommMonoid.{u3} M] {f : α -> (TrivSqZeroExt.{u2, u3} R M)} {a : TrivSqZeroExt.{u2, u3} R M}, (HasSum.{max u2 u3, u1} (TrivSqZeroExt.{u2, u3} R M) α (TrivSqZeroExt.addCommMonoid.{u2, u3} R M _inst_3 _inst_4) (TrivSqZeroExt.topologicalSpace.{u2, u3} R M _inst_1 _inst_2) f a) -> (HasSum.{u3, u1} M α _inst_4 _inst_2 (fun (x : α) => TrivSqZeroExt.snd.{u2, u3} R M (f x)) (TrivSqZeroExt.snd.{u2, u3} R M a))
but is expected to have type
  forall {α : Type.{u1}} {R : Type.{u3}} (M : Type.{u2}) [_inst_1 : TopologicalSpace.{u3} R] [_inst_2 : TopologicalSpace.{u2} M] [_inst_3 : AddCommMonoid.{u3} R] [_inst_4 : AddCommMonoid.{u2} M] {f : α -> (TrivSqZeroExt.{u3, u2} R M)} {a : TrivSqZeroExt.{u3, u2} R M}, (HasSum.{max u3 u2, u1} (TrivSqZeroExt.{u3, u2} R M) α (TrivSqZeroExt.addCommMonoid.{u3, u2} R M _inst_3 _inst_4) (TrivSqZeroExt.instTopologicalSpaceTrivSqZeroExt.{u3, u2} R M _inst_1 _inst_2) f a) -> (HasSum.{u2, u1} M α _inst_4 _inst_2 (fun (x : α) => TrivSqZeroExt.snd.{u3, u2} R M (f x)) (TrivSqZeroExt.snd.{u3, u2} R M a))
Case conversion may be inaccurate. Consider using '#align triv_sq_zero_ext.has_sum_snd TrivSqZeroExt.hasSum_sndₓ'. -/
theorem hasSum_snd [AddCommMonoid R] [AddCommMonoid M] {f : α → tsze R M} {a : tsze R M}
    (h : HasSum f a) : HasSum (fun x => snd (f x)) (snd a) :=
  h.map (⟨snd, snd_zero, snd_add⟩ : tsze R M →+ M) continuous_snd
#align triv_sq_zero_ext.has_sum_snd TrivSqZeroExt.hasSum_snd

end TrivSqZeroExt

