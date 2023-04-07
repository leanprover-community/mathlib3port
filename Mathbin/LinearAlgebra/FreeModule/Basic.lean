/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.basic
! leanprover-community/mathlib commit 4e7e7009099d4a88a750de710909b95487bf0124
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.DirectSum.Finsupp
import Mathbin.Logic.Small.Basic
import Mathbin.LinearAlgebra.StdBasis
import Mathbin.LinearAlgebra.FinsuppVectorSpace
import Mathbin.LinearAlgebra.TensorProductBasis

/-!

# Free modules

We introduce a class `module.free R M`, for `R` a `semiring` and `M` an `R`-module and we provide
several basic instances for this class.

Use `finsupp.total_id_surjective` to prove that any module is the quotient of a free module.

## Main definition

* `module.free R M` : the class of free `R`-modules.

-/


universe u v w z

variable {ι : Type _} (R : Type u) (M : Type v) (N : Type z)

open TensorProduct DirectSum BigOperators

section Basic

variable [Semiring R] [AddCommMonoid M] [Module R M]

#print Module.Free /-
/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`exists_basis] [] -/
/-- `module.free R M` is the statement that the `R`-module `M` is free.-/
class Module.Free : Prop where
  exists_basis : Nonempty (ΣI : Type v, Basis I R M)
#align module.free Module.Free
-/

#print Module.free_def /-
/- If `M` fits in universe `w`, then freeness is equivalent to existence of a basis in that
universe.

Note that if `M` does not fit in `w`, the reverse direction of this implication is still true as
`module.free.of_basis`. -/
theorem Module.free_def [Small.{w} M] : Module.Free R M ↔ ∃ I : Type w, Nonempty (Basis I R M) :=
  ⟨fun h =>
    ⟨Shrink (Set.range h.exists_basis.some.2),
      ⟨(Basis.reindexRange h.exists_basis.some.2).reindex (equivShrink _)⟩⟩,
    fun h => ⟨(nonempty_sigma.2 h).map fun ⟨i, b⟩ => ⟨Set.range b, b.reindexRange⟩⟩⟩
#align module.free_def Module.free_def
-/

#print Module.free_iff_set /-
theorem Module.free_iff_set : Module.Free R M ↔ ∃ S : Set M, Nonempty (Basis S R M) :=
  ⟨fun h => ⟨Set.range h.exists_basis.some.2, ⟨Basis.reindexRange h.exists_basis.some.2⟩⟩,
    fun ⟨S, hS⟩ => ⟨nonempty_sigma.2 ⟨S, hS⟩⟩⟩
#align module.free_iff_set Module.free_iff_set
-/

variable {R M}

#print Module.Free.of_basis /-
theorem Module.Free.of_basis {ι : Type w} (b : Basis ι R M) : Module.Free R M :=
  (Module.free_def R M).2 ⟨Set.range b, ⟨b.reindexRange⟩⟩
#align module.free.of_basis Module.Free.of_basis
-/

end Basic

namespace Module.Free

section Semiring

variable (R M) [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]

variable [AddCommMonoid N] [Module R N]

#print Module.Free.ChooseBasisIndex /-
/-- If `module.free R M` then `choose_basis_index R M` is the `ι` which indexes the basis
  `ι → M`. -/
def ChooseBasisIndex :=
  (exists_basis R M).some.1
#align module.free.choose_basis_index Module.Free.ChooseBasisIndex
-/

#print Module.Free.chooseBasis /-
/-- If `module.free R M` then `choose_basis : ι → M` is the basis.
Here `ι = choose_basis_index R M`. -/
noncomputable def chooseBasis : Basis (ChooseBasisIndex R M) R M :=
  (exists_basis R M).some.2
#align module.free.choose_basis Module.Free.chooseBasis
-/

/- warning: module.free.repr -> Module.Free.repr is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3], LinearEquiv.{u1, u1, u2, max u2 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M (Finsupp.{u2, u1} (Module.Free.ChooseBasisIndex.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4) R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_2 (Finsupp.addCommMonoid.{u2, u1} (Module.Free.ChooseBasisIndex.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4) R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3 (Finsupp.module.{u2, u1, u1} (Module.Free.ChooseBasisIndex.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3], LinearEquiv.{u1, u1, u2, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) M (Finsupp.{u2, u1} (Module.Free.ChooseBasisIndex.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4) R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) _inst_2 (Finsupp.addCommMonoid.{u2, u1} (Module.Free.ChooseBasisIndex.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4) R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) _inst_3 (Finsupp.module.{u2, u1, u1} (Module.Free.ChooseBasisIndex.{u1, u2} R M _inst_1 _inst_2 _inst_3 _inst_4) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align module.free.repr Module.Free.reprₓ'. -/
/-- The isomorphism `M ≃ₗ[R] (choose_basis_index R M →₀ R)`. -/
noncomputable def repr : M ≃ₗ[R] ChooseBasisIndex R M →₀ R :=
  (chooseBasis R M).repr
#align module.free.repr Module.Free.repr

#print Module.Free.constr /-
/-- The universal property of free modules: giving a functon `(choose_basis_index R M) → N`, for `N`
an `R`-module, is the same as giving an `R`-linear map `M →ₗ[R] N`.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
See library note [bundled maps over different rings]. -/
noncomputable def constr {S : Type z} [Semiring S] [Module S N] [SMulCommClass R S N] :
    (ChooseBasisIndex R M → N) ≃ₗ[S] M →ₗ[R] N :=
  Basis.constr (chooseBasis R M) S
#align module.free.constr Module.Free.constr
-/

/- warning: module.free.no_zero_smul_divisors -> Module.Free.noZeroSMulDivisors is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3] [_inst_7 : NoZeroDivisors.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))], NoZeroSMulDivisors.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (SMulZeroClass.toHasSmul.{u1, u2} R M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} R M (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Module.toMulActionWithZero.{u1, u2} R M _inst_1 _inst_2 _inst_3))))
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3] [_inst_7 : NoZeroDivisors.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))], NoZeroSMulDivisors.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (SMulZeroClass.toSMul.{u1, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} R M (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} R M (Semiring.toMonoidWithZero.{u1} R _inst_1) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Module.toMulActionWithZero.{u1, u2} R M _inst_1 _inst_2 _inst_3))))
Case conversion may be inaccurate. Consider using '#align module.free.no_zero_smul_divisors Module.Free.noZeroSMulDivisorsₓ'. -/
instance (priority := 100) noZeroSMulDivisors [NoZeroDivisors R] : NoZeroSMulDivisors R M :=
  let ⟨⟨_, b⟩⟩ := exists_basis R M
  b.NoZeroSMulDivisors
#align module.free.no_zero_smul_divisors Module.Free.noZeroSMulDivisors

instance [Nontrivial M] : Nonempty (Module.Free.ChooseBasisIndex R M) :=
  (Module.Free.chooseBasis R M).index_nonempty

variable {R M N}

#print Module.Free.of_equiv /-
theorem of_equiv (e : M ≃ₗ[R] N) : Module.Free R N :=
  of_basis <| (chooseBasis R M).map e
#align module.free.of_equiv Module.Free.of_equiv
-/

#print Module.Free.of_equiv' /-
/-- A variation of `of_equiv`: the assumption `module.free R P` here is explicit rather than an
instance. -/
theorem of_equiv' {P : Type v} [AddCommMonoid P] [Module R P] (h : Module.Free R P)
    (e : P ≃ₗ[R] N) : Module.Free R N :=
  of_equiv e
#align module.free.of_equiv' Module.Free.of_equiv'
-/

variable (R M N)

#print Module.Free.self /-
/-- The module structure provided by `semiring.to_module` is free. -/
instance self : Module.Free R R :=
  of_basis (Basis.singleton Unit R)
#align module.free.self Module.Free.self
-/

/- warning: module.free.prod -> Module.Free.prod is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) (N : Type.{u3}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3] [_inst_5 : AddCommMonoid.{u3} N] [_inst_6 : Module.{u1, u3} R N _inst_1 _inst_5] [_inst_7 : Module.Free.{u1, u3} R N _inst_1 _inst_5 _inst_6], Module.Free.{u1, max u2 u3} R (Prod.{u2, u3} M N) _inst_1 (Prod.addCommMonoid.{u2, u3} M N _inst_2 _inst_5) (Prod.module.{u1, u2, u3} R M N _inst_1 _inst_2 _inst_5 _inst_3 _inst_6)
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) (N : Type.{u3}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3] [_inst_5 : AddCommMonoid.{u3} N] [_inst_6 : Module.{u1, u3} R N _inst_1 _inst_5] [_inst_7 : Module.Free.{u1, u3} R N _inst_1 _inst_5 _inst_6], Module.Free.{u1, max u3 u2} R (Prod.{u2, u3} M N) _inst_1 (Prod.instAddCommMonoidSum.{u2, u3} M N _inst_2 _inst_5) (Prod.module.{u1, u2, u3} R M N _inst_1 _inst_2 _inst_5 _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align module.free.prod Module.Free.prodₓ'. -/
instance prod [Module.Free R N] : Module.Free R (M × N) :=
  of_basis <| (chooseBasis R M).Prod (chooseBasis R N)
#align module.free.prod Module.Free.prod

#print Module.Free.pi /-
/-- The product of finitely many free modules is free. -/
instance pi (M : ι → Type _) [Finite ι] [∀ i : ι, AddCommMonoid (M i)] [∀ i : ι, Module R (M i)]
    [∀ i : ι, Module.Free R (M i)] : Module.Free R (∀ i, M i) :=
  let ⟨_⟩ := nonempty_fintype ι
  of_basis <| Pi.basis fun i => choose_basis R (M i)
#align module.free.pi Module.Free.pi
-/

#print Module.Free.matrix /-
/-- The module of finite matrices is free. -/
instance matrix {m n : Type _} [Finite m] [Finite n] : Module.Free R (Matrix m n M) :=
  Module.Free.pi R _
#align module.free.matrix Module.Free.matrix
-/

variable (ι)

#print Module.Free.function /-
/-- The product of finitely many free modules is free (non-dependent version to help with typeclass
search). -/
instance function [Finite ι] : Module.Free R (ι → M) :=
  Free.pi _ _
#align module.free.function Module.Free.function
-/

/- warning: module.free.finsupp -> Module.Free.finsupp is a dubious translation:
lean 3 declaration is
  forall (ι : Type.{u3}) (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3], Module.Free.{u1, max u3 u2} R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall (ι : Type.{u3}) (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] [_inst_4 : Module.Free.{u1, u2} R M _inst_1 _inst_2 _inst_3], Module.Free.{u1, max u2 u3} R (Finsupp.{u3, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align module.free.finsupp Module.Free.finsuppₓ'. -/
instance finsupp : Module.Free R (ι →₀ M) :=
  of_basis (Finsupp.basis fun i => chooseBasis R M)
#align module.free.finsupp Module.Free.finsupp

variable {ι}

/- warning: module.free.of_subsingleton -> Module.Free.of_subsingleton is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u}) (N : Type.{z}) [_inst_1 : Semiring.{u} R] [_inst_5 : AddCommMonoid.{z} N] [_inst_6 : Module.{u, z} R N _inst_1 _inst_5] [_inst_7 : Subsingleton.{succ z} N], Module.Free.{u, z} R N _inst_1 _inst_5 _inst_6
but is expected to have type
  forall (R : Type.{u}) (N : Type.{z}) [_inst_1 : Semiring.{u} R] [_inst_5 : AddCommMonoid.{z} N] [_inst_6 : Module.{u, z} R N _inst_1 _inst_5] [_inst_7 : Subsingleton.{succ z} N], Module.Free.{u, z} R N _inst_1 _inst_5 _inst_6
Case conversion may be inaccurate. Consider using '#align module.free.of_subsingleton Module.Free.of_subsingletonₓ'. -/
instance (priority := 100) of_subsingleton [Subsingleton N] : Module.Free R N :=
  of_basis (Basis.empty N : Basis PEmpty R N)
#align module.free.of_subsingleton Module.Free.of_subsingleton

/- warning: module.free.of_subsingleton' -> Module.Free.of_subsingleton' is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u}) (N : Type.{z}) [_inst_1 : Semiring.{u} R] [_inst_5 : AddCommMonoid.{z} N] [_inst_6 : Module.{u, z} R N _inst_1 _inst_5] [_inst_7 : Subsingleton.{succ u} R], Module.Free.{u, z} R N _inst_1 _inst_5 _inst_6
but is expected to have type
  forall (R : Type.{u}) (N : Type.{z}) [_inst_1 : Semiring.{u} R] [_inst_5 : AddCommMonoid.{z} N] [_inst_6 : Module.{u, z} R N _inst_1 _inst_5] [_inst_7 : Subsingleton.{succ u} R], Module.Free.{u, z} R N _inst_1 _inst_5 _inst_6
Case conversion may be inaccurate. Consider using '#align module.free.of_subsingleton' Module.Free.of_subsingleton'ₓ'. -/
instance (priority := 100) of_subsingleton' [Subsingleton R] : Module.Free R N :=
  letI := Module.subsingleton R N
  Module.Free.of_subsingleton R N
#align module.free.of_subsingleton' Module.Free.of_subsingleton'

/- warning: module.free.dfinsupp -> Module.Free.dfinsupp is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {ι : Type.{u2}} (M : ι -> Type.{u3}) [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_8 : forall (i : ι), Module.{u1, u3} R (M i) _inst_1 (_inst_7 i)] [_inst_9 : forall (i : ι), Module.Free.{u1, u3} R (M i) _inst_1 (_inst_7 i) (_inst_8 i)], Module.Free.{u1, max u2 u3} R (Dfinsupp.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddZeroClass.toHasZero.{u3} (M i) (AddMonoid.toAddZeroClass.{u3} (M i) (AddCommMonoid.toAddMonoid.{u3} (M i) (_inst_7 i))))) _inst_1 (Dfinsupp.addCommMonoid.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.module.{u2, u3, u1} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_8 i))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {ι : Type.{u2}} (M : ι -> Type.{u3}) [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_8 : forall (i : ι), Module.{u1, u3} R (M i) _inst_1 (_inst_7 i)] [_inst_9 : forall (i : ι), Module.Free.{u1, u3} R (M i) _inst_1 (_inst_7 i) (_inst_8 i)], Module.Free.{u1, max u3 u2} R (Dfinsupp.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => AddMonoid.toZero.{u3} ((fun (i : ι) => M i) i) (AddCommMonoid.toAddMonoid.{u3} ((fun (i : ι) => M i) i) (_inst_7 i)))) _inst_1 (Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i)) (Dfinsupp.module.{u2, u3, u1} ι R (fun (i : ι) => M i) _inst_1 (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_8 i))
Case conversion may be inaccurate. Consider using '#align module.free.dfinsupp Module.Free.dfinsuppₓ'. -/
instance dfinsupp {ι : Type _} (M : ι → Type _) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (Π₀ i, M i) :=
  of_basis <| Dfinsupp.basis fun i => chooseBasis R (M i)
#align module.free.dfinsupp Module.Free.dfinsupp

/- warning: module.free.direct_sum -> Module.Free.directSum is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {ι : Type.{u2}} (M : ι -> Type.{u3}) [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_8 : forall (i : ι), Module.{u1, u3} R (M i) _inst_1 (_inst_7 i)] [_inst_9 : forall (i : ι), Module.Free.{u1, u3} R (M i) _inst_1 (_inst_7 i) (_inst_8 i)], Module.Free.{u1, max u2 u3} R (DirectSum.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i)) _inst_1 (DirectSum.addCommMonoid.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i)) (DirectSum.module.{u1, u2, u3} R _inst_1 ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_8 i))
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] {ι : Type.{u2}} (M : ι -> Type.{u3}) [_inst_7 : forall (i : ι), AddCommMonoid.{u3} (M i)] [_inst_8 : forall (i : ι), Module.{u1, u3} R (M i) _inst_1 (_inst_7 i)] [_inst_9 : forall (i : ι), Module.Free.{u1, u3} R (M i) _inst_1 (_inst_7 i) (_inst_8 i)], Module.Free.{u1, max u3 u2} R (DirectSum.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i)) _inst_1 (instAddCommMonoidDirectSum.{u2, u3} ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i)) (DirectSum.instModuleDirectSumInstAddCommMonoidDirectSum.{u1, u2, u3} R _inst_1 ι (fun (i : ι) => M i) (fun (i : ι) => _inst_7 i) (fun (i : ι) => _inst_8 i))
Case conversion may be inaccurate. Consider using '#align module.free.direct_sum Module.Free.directSumₓ'. -/
instance directSum {ι : Type _} (M : ι → Type _) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] : Module.Free R (⨁ i, M i) :=
  Module.Free.dfinsupp R M
#align module.free.direct_sum Module.Free.directSum

end Semiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

/- warning: module.free.tensor -> Module.Free.tensor is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) (N : Type.{u3}) [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] [_inst_5 : AddCommGroup.{u3} N] [_inst_6 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5)] [_inst_7 : Module.Free.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_6], Module.Free.{u1, max u2 u3} R (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_3 _inst_6) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_3 _inst_6) (TensorProduct.module.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_3 _inst_6)
but is expected to have type
  forall (R : Type.{u1}) (M : Type.{u2}) (N : Type.{u3}) [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] [_inst_4 : Module.Free.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3] [_inst_5 : AddCommGroup.{u3} N] [_inst_6 : Module.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5)] [_inst_7 : Module.Free.{u1, u3} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_6], Module.Free.{u1, max u3 u2} R (TensorProduct.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_3 _inst_6) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (TensorProduct.addCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_3 _inst_6) (TensorProduct.instModuleTensorProductToSemiringAddCommMonoid.{u1, u2, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M N (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) (AddCommGroup.toAddCommMonoid.{u3} N _inst_5) _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align module.free.tensor Module.Free.tensorₓ'. -/
instance tensor : Module.Free R (M ⊗[R] N) :=
  let ⟨bM⟩ := exists_basis R M
  let ⟨bN⟩ := exists_basis R N
  of_basis (bM.2.TensorProduct bN.2)
#align module.free.tensor Module.Free.tensor

end CommRing

section DivisionRing

variable [DivisionRing R] [AddCommGroup M] [Module R M]

#print Module.Free.of_divisionRing /-
instance (priority := 100) of_divisionRing : Module.Free R M :=
  of_basis (Basis.ofVectorSpace R M)
#align module.free.of_division_ring Module.Free.of_divisionRing
-/

end DivisionRing

end Module.Free

