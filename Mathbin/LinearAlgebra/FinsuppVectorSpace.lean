/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module linear_algebra.finsupp_vector_space
! leanprover-community/mathlib commit 19cb3751e5e9b3d97adb51023949c50c13b5fdfd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.StdBasis

/-!
# Linear structures on function with finite support `ι →₀ M`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

-/


noncomputable section

attribute [local instance 100] Classical.propDecidable

open Set LinearMap Submodule

open Cardinal

universe u v w

namespace Finsupp

section Ring

variable {R : Type _} {M : Type _} {ι : Type _}

variable [Ring R] [AddCommGroup M] [Module R M]

/- warning: finsupp.linear_independent_single -> Finsupp.linearIndependent_single is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Ring.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {φ : ι -> Type.{u4}} {f : forall (ι : ι), (φ ι) -> M}, (forall (i : ι), LinearIndependent.{u4, u1, u2} (φ i) R M (f i) (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (LinearIndependent.{max u3 u4, u1, max u3 u2} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2)))))) (fun (ix : Sigma.{u3, u4} ι (fun (i : ι) => φ i)) => Finsupp.single.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_2))))) (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix) (f (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix) (Sigma.snd.{u3, u4} ι (fun (i : ι) => φ i) ix))) (Ring.toSemiring.{u1} R _inst_1) (Finsupp.addCommMonoid.{u3, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)) (Finsupp.module.{u3, u2, u1} ι M R (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Ring.{u3} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : Module.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {φ : ι -> Type.{u4}} {f : forall (ι : ι), (φ ι) -> M}, (forall (i : ι), LinearIndependent.{u4, u3, u2} (φ i) R M (f i) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3) -> (LinearIndependent.{max u1 u4, u3, max u2 u1} (Sigma.{u1, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u1, u2} ι M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2)))))) (fun (ix : Sigma.{u1, u4} ι (fun (i : ι) => φ i)) => Finsupp.single.{u1, u2} ι M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_2))))) (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix) (f (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix) (Sigma.snd.{u1, u4} ι (fun (i : ι) => φ i) ix))) (Ring.toSemiring.{u3} R _inst_1) (Finsupp.addCommMonoid.{u1, u2} ι M (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)) (Finsupp.module.{u1, u2, u3} ι M R (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_3))
Case conversion may be inaccurate. Consider using '#align finsupp.linear_independent_single Finsupp.linearIndependent_singleₓ'. -/
theorem linearIndependent_single {φ : ι → Type _} {f : ∀ ι, φ ι → M}
    (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σi, φ i => single ix.1 (f ix.1 ix.2) :=
  by
  apply @linearIndependent_iUnion_finite R _ _ _ _ ι φ fun i x => single i (f i x)
  · intro i
    have h_disjoint : Disjoint (span R (range (f i))) (ker (lsingle i)) :=
      by
      rw [ker_lsingle]
      exact disjoint_bot_right
    apply (hf i).map h_disjoint
  · intro i t ht hit
    refine' (disjoint_lsingle_lsingle {i} t (disjoint_singleton_left.2 hit)).mono _ _
    · rw [span_le]
      simp only [iSup_singleton]
      rw [range_coe]
      apply range_comp_subset_range
    · refine' iSup₂_mono fun i hi => _
      rw [span_le, range_coe]
      apply range_comp_subset_range
#align finsupp.linear_independent_single Finsupp.linearIndependent_single

end Ring

section Semiring

variable {R : Type _} {M : Type _} {ι : Type _}

variable [Semiring R] [AddCommMonoid M] [Module R M]

open LinearMap Submodule

/- warning: finsupp.basis -> Finsupp.basis is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] {φ : ι -> Type.{u4}}, (forall (i : ι), Basis.{u4, u1, u2} (φ i) R M _inst_1 _inst_2 _inst_3) -> (Basis.{max u3 u4, u1, max u3 u2} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {R : Type.{u1}} {M : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] {φ : ι -> Type.{u4}}, (forall (i : ι), Basis.{u4, u1, u2} (φ i) R M _inst_1 _inst_2 _inst_3) -> (Basis.{max u4 u3, u1, max u2 u3} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align finsupp.basis Finsupp.basisₓ'. -/
/-- The basis on `ι →₀ M` with basis vectors `λ ⟨i, x⟩, single i (b i x)`. -/
protected def basis {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) : Basis (Σi, φ i) R (ι →₀ M) :=
  Basis.ofRepr
    { toFun := fun g =>
        { toFun := fun ix => (b ix.1).repr (g ix.1) ix.2
          support := g.support.Sigma fun i => ((b i).repr (g i)).support
          mem_support_toFun := fun ix =>
            by
            simp only [Finset.mem_sigma, mem_support_iff, and_iff_right_iff_imp, Ne.def]
            intro b hg
            simpa [hg] using b }
      invFun := fun g =>
        { toFun := fun i =>
            (b i).repr.symm (g.comapDomain _ (Set.injOn_of_injective sigma_mk_injective _))
          support := g.support.image Sigma.fst
          mem_support_toFun := fun i =>
            by
            rw [Ne.def, ← (b i).repr.Injective.eq_iff, (b i).repr.apply_symm_apply, ext_iff]
            simp only [exists_prop, LinearEquiv.map_zero, comap_domain_apply, zero_apply,
              exists_and_right, mem_support_iff, exists_eq_right, Sigma.exists, Finset.mem_image,
              not_forall] }
      left_inv := fun g => by
        ext i; rw [← (b i).repr.Injective.eq_iff]; ext x
        simp only [coe_mk, LinearEquiv.apply_symm_apply, comap_domain_apply]
      right_inv := fun g => by
        ext ⟨i, x⟩
        simp only [coe_mk, LinearEquiv.apply_symm_apply, comap_domain_apply]
      map_add' := fun g h => by ext ⟨i, x⟩; simp only [coe_mk, add_apply, LinearEquiv.map_add]
      map_smul' := fun c h => by ext ⟨i, x⟩;
        simp only [coe_mk, smul_apply, LinearEquiv.map_smul, RingHom.id_apply] }
#align finsupp.basis Finsupp.basis

/- warning: finsupp.basis_repr -> Finsupp.basis_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align finsupp.basis_repr Finsupp.basis_reprₓ'. -/
@[simp]
theorem basis_repr {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) (g : ι →₀ M) (ix) :
    (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl
#align finsupp.basis_repr Finsupp.basis_repr

/- warning: finsupp.coe_basis -> Finsupp.coe_basis is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Semiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u1, u2} R M _inst_1 _inst_2] {φ : ι -> Type.{u4}} (b : forall (i : ι), Basis.{u4, u1, u2} (φ i) R M _inst_1 _inst_2 _inst_3), Eq.{max (succ (max u3 u4)) (succ (max u3 u2))} ((Sigma.{u3, u4} ι (fun (i : ι) => φ i)) -> (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (coeFn.{max (succ (max u3 u4)) (succ u1) (succ (max u3 u2)), max (succ (max u3 u4)) (succ (max u3 u2))} (Basis.{max u3 u4, u1, max u3 u2} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3)) (fun (_x : Basis.{max u3 u4, u1, max u3 u2} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3)) => (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) -> (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (FunLike.hasCoeToFun.{max (succ (max u3 u4)) (succ u1) (succ (max u3 u2)), succ (max u3 u4), succ (max u3 u2)} (Basis.{max u3 u4, u1, max u3 u2} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3)) (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) (fun (_x : Sigma.{u3, u4} ι (fun (i : ι) => φ i)) => Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Basis.funLike.{max u3 u4, u1, max u3 u2} (Sigma.{u3, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) _inst_1 (Finsupp.addCommMonoid.{u3, u2} ι M _inst_2) (Finsupp.module.{u3, u2, u1} ι M R _inst_1 _inst_2 _inst_3))) (Finsupp.basis.{u1, u2, u3, u4} R M ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) b)) (fun (ix : Sigma.{u3, u4} ι (fun (i : ι) => φ i)) => Finsupp.single.{u3, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix) (coeFn.{max (succ u4) (succ u1) (succ u2), max (succ u4) (succ u2)} (Basis.{u4, u1, u2} (φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u4, u1, u2} (φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) R M _inst_1 _inst_2 _inst_3) => (φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) -> M) (FunLike.hasCoeToFun.{max (succ u4) (succ u1) (succ u2), succ u4, succ u2} (Basis.{u4, u1, u2} (φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) R M _inst_1 _inst_2 _inst_3) (φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) (fun (_x : φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) => M) (Basis.funLike.{u4, u1, u2} (φ (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) R M _inst_1 _inst_2 _inst_3)) (b (Sigma.fst.{u3, u4} ι (fun (i : ι) => φ i) ix)) (Sigma.snd.{u3, u4} ι (fun (i : ι) => φ i) ix)))
but is expected to have type
  forall {R : Type.{u3}} {M : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] {φ : ι -> Type.{u4}} (b : forall (i : ι), Basis.{u4, u3, u2} (φ i) R M _inst_1 _inst_2 _inst_3), Eq.{max (max (succ u2) (succ u1)) (succ u4)} (forall (a : Sigma.{u1, u4} ι (fun (i : ι) => φ i)), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Sigma.{u1, u4} ι (fun (i : ι) => φ i)) => Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) a) (FunLike.coe.{max (max (max (succ u3) (succ u2)) (succ u1)) (succ u4), max (succ u1) (succ u4), max (succ u2) (succ u1)} (Basis.{max u4 u1, u3, max u2 u1} (Sigma.{u1, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) _inst_1 (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) (Finsupp.module.{u1, u2, u3} ι M R _inst_1 _inst_2 _inst_3)) (Sigma.{u1, u4} ι (fun (i : ι) => φ i)) (fun (_x : Sigma.{u1, u4} ι (fun (i : ι) => φ i)) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Sigma.{u1, u4} ι (fun (i : ι) => φ i)) => Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) _x) (Basis.funLike.{max u1 u4, u3, max u2 u1} (Sigma.{u1, u4} ι (fun (i : ι) => φ i)) R (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) _inst_1 (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) (Finsupp.module.{u1, u2, u3} ι M R _inst_1 _inst_2 _inst_3)) (Finsupp.basis.{u3, u2, u1, u4} R M ι _inst_1 _inst_2 _inst_3 (fun (i : ι) => φ i) b)) (fun (ix : Sigma.{u1, u4} ι (fun (i : ι) => φ i)) => Finsupp.single.{u1, u2} ι ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) => M) (Sigma.snd.{u1, u4} ι (fun (i : ι) => φ i) ix)) (AddMonoid.toZero.{u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) => M) (Sigma.snd.{u1, u4} ι (fun (i : ι) => φ i) ix)) (AddCommMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) => M) (Sigma.snd.{u1, u4} ι (fun (i : ι) => φ i) ix)) _inst_2)) (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u4), succ u4, succ u2} (Basis.{u4, u3, u2} (φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) R M _inst_1 _inst_2 _inst_3) (φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) (fun (_x : φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) => M) _x) (Basis.funLike.{u4, u3, u2} (φ (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) R M _inst_1 _inst_2 _inst_3) (b (Sigma.fst.{u1, u4} ι (fun (i : ι) => φ i) ix)) (Sigma.snd.{u1, u4} ι (fun (i : ι) => φ i) ix)))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_basis Finsupp.coe_basisₓ'. -/
@[simp]
theorem coe_basis {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) :
    ⇑(Finsupp.basis b) = fun ix : Σi, φ i => single ix.1 (b ix.1 ix.2) :=
  funext fun ⟨i, x⟩ =>
    Basis.apply_eq_iff.mpr <| by
      ext ⟨j, y⟩
      by_cases h : i = j
      · cases h
        simp only [basis_repr, single_eq_same, Basis.repr_self,
          Finsupp.single_apply_left sigma_mk_injective]
      simp only [basis_repr, single_apply, h, false_and_iff, if_false, LinearEquiv.map_zero,
        zero_apply]
#align finsupp.coe_basis Finsupp.coe_basis

/- warning: finsupp.basis_single_one -> Finsupp.basisSingleOne is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R], Basis.{u2, u1, max u2 u1} ι R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R], Basis.{u2, u1, max u1 u2} ι R (Finsupp.{u2, u1} ι R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))
Case conversion may be inaccurate. Consider using '#align finsupp.basis_single_one Finsupp.basisSingleOneₓ'. -/
/-- The basis on `ι →₀ M` with basis vectors `λ i, single i 1`. -/
@[simps]
protected def basisSingleOne : Basis ι R (ι →₀ R) :=
  Basis.ofRepr (LinearEquiv.refl _ _)
#align finsupp.basis_single_one Finsupp.basisSingleOne

/- warning: finsupp.coe_basis_single_one -> Finsupp.coe_basisSingleOne is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} [_inst_1 : Semiring.{u1} R], Eq.{max (succ u2) (succ u1)} ((fun (_x : Basis.{u2, u1, max u2 u1} ι R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) => ι -> (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (Finsupp.basisSingleOne.{u1, u2} R ι _inst_1)) (coeFn.{max (succ u2) (succ u1) (succ (max u2 u1)), max (succ u2) (succ (max u2 u1))} (Basis.{u2, u1, max u2 u1} ι R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) (fun (_x : Basis.{u2, u1, max u2 u1} ι R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) => ι -> (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) (FunLike.hasCoeToFun.{max (succ u2) (succ u1) (succ (max u2 u1)), succ u2, succ (max u2 u1)} (Basis.{u2, u1, max u2 u1} ι R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) ι (fun (_x : ι) => Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (Basis.funLike.{u2, u1, max u2 u1} ι R (Finsupp.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) _inst_1 (Finsupp.addCommMonoid.{u2, u1} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Finsupp.module.{u2, u1, u1} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)))) (Finsupp.basisSingleOne.{u1, u2} R ι _inst_1)) (fun (i : ι) => Finsupp.single.{u2, u1} ι R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) i (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u2}} {ι : Type.{u1}} [_inst_1 : Semiring.{u2} R], Eq.{max (succ u2) (succ u1)} (forall (a : ι), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => Finsupp.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, max (succ u1) (succ u2)} (Basis.{u1, u2, max u2 u1} ι R (Finsupp.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) _inst_1 (Finsupp.addCommMonoid.{u1, u2} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Finsupp.module.{u1, u2, u2} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Semiring.toModule.{u2} R _inst_1))) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => Finsupp.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) _x) (Basis.funLike.{u1, u2, max u1 u2} ι R (Finsupp.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) _inst_1 (Finsupp.addCommMonoid.{u1, u2} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Finsupp.module.{u1, u2, u2} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Semiring.toModule.{u2} R _inst_1))) (Finsupp.basisSingleOne.{u2, u1} R ι _inst_1)) (fun (i : ι) => Finsupp.single.{u1, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)) i (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R (Semiring.toOne.{u2} R _inst_1))))
Case conversion may be inaccurate. Consider using '#align finsupp.coe_basis_single_one Finsupp.coe_basisSingleOneₓ'. -/
@[simp]
theorem coe_basisSingleOne : (Finsupp.basisSingleOne : ι → ι →₀ R) = fun i => Finsupp.single i 1 :=
  funext fun i => Basis.apply_eq_iff.mpr rfl
#align finsupp.coe_basis_single_one Finsupp.coe_basisSingleOne

end Semiring

end Finsupp

/-! TODO: move this section to an earlier file. -/


namespace Basis

variable {R M n : Type _}

variable [DecidableEq n] [Fintype n]

variable [Semiring R] [AddCommMonoid M] [Module R M]

/- warning: finset.sum_single_ite -> Finset.sum_single_ite is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {n : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} n] [_inst_2 : Fintype.{u2} n] [_inst_3 : Semiring.{u1} R] (a : R) (i : n), Eq.{succ (max u2 u1)} (Finsupp.{u2, u1} n R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))))) (Finset.sum.{max u2 u1, u2} (Finsupp.{u2, u1} n R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))))) n (Finsupp.addCommMonoid.{u2, u1} n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3)))) (Finset.univ.{u2} n _inst_2) (fun (x : n) => Finsupp.single.{u2, u1} n R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3)))) x (ite.{succ u1} R (Eq.{succ u2} n i x) (_inst_1 i x) a (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3)))))))))) (Finsupp.single.{u2, u1} n R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3)))) i a)
but is expected to have type
  forall {R : Type.{u2}} {n : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} n] [_inst_2 : Fintype.{u1} n] [_inst_3 : Semiring.{u2} R] (a : R) (i : n), Eq.{max (succ u2) (succ u1)} (Finsupp.{u1, u2} n R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3))) (Finset.sum.{max u2 u1, u1} (Finsupp.{u1, u2} n R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3))) n (Finsupp.addCommMonoid.{u1, u2} n R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_3)))) (Finset.univ.{u1} n _inst_2) (fun (x : n) => Finsupp.single.{u1, u2} n R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3)) x (ite.{succ u2} R (Eq.{succ u1} n i x) (_inst_1 i x) a (OfNat.ofNat.{u2} R 0 (Zero.toOfNat0.{u2} R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3))))))) (Finsupp.single.{u1, u2} n R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_3)) i a)
Case conversion may be inaccurate. Consider using '#align finset.sum_single_ite Finset.sum_single_iteₓ'. -/
theorem Finset.sum_single_ite (a : R) (i : n) :
    (Finset.univ.Sum fun x : n => Finsupp.single x (ite (i = x) a 0)) = Finsupp.single i a :=
  by
  rw [Finset.sum_congr_set {i} (fun x : n => Finsupp.single x (ite (i = x) a 0)) fun _ =>
      Finsupp.single i a]
  · simp
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    simp [hx]
  intro x hx
  have hx' : ¬i = x := by
    refine' ne_comm.mp _
    rwa [mem_singleton_iff] at hx
  simp [hx']
#align finset.sum_single_ite Finset.sum_single_ite

/- warning: basis.equiv_fun_symm_std_basis -> Basis.equivFun_symm_stdBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv_fun_symm_std_basis Basis.equivFun_symm_stdBasisₓ'. -/
@[simp]
theorem equivFun_symm_stdBasis (b : Basis n R M) (i : n) :
    b.equivFun.symm (LinearMap.stdBasis R (fun _ => R) i 1) = b i :=
  by
  have := EquivLike.injective b.repr
  apply_fun b.repr
  simp only [equiv_fun_symm_apply, std_basis_apply', LinearEquiv.map_sum, LinearEquiv.map_smulₛₗ,
    RingHom.id_apply, repr_self, Finsupp.smul_single', boole_mul]
  exact Finset.sum_single_ite 1 i
#align basis.equiv_fun_symm_std_basis Basis.equivFun_symm_stdBasis

end Basis

