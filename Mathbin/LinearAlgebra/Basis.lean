/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp

! This file was ported from Lean 3 source module linear_algebra.basis
! leanprover-community/mathlib commit 13bce9a6b6c44f6b4c91ac1c1d2a816e2533d395
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Finsupp
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.Data.Fintype.BigOperators
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.LinearAlgebra.LinearPmap
import Mathbin.LinearAlgebra.Projection

/-!

# Bases

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b : basis ι R M` are available as `b i`, where `i : ι`

* `basis.repr` is the isomorphism sending `x : M` to its coordinates `basis.repr x : ι →₀ R`.
  The converse, turning this isomorphism into a basis, is called `basis.of_repr`.
* If `ι` is finite, there is a variant of `repr` called `basis.equiv_fun b : M ≃ₗ[R] ι → R`
  (saving you from having to work with `finsupp`). The converse, turning this isomorphism into
  a basis, is called `basis.of_equiv_fun`.

* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `basis.reindex` uses an equiv to map a basis to a different indexing set.
* `basis.map` uses a linear equiv to map a basis to a different module.

## Main statements

* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.

* `basis.of_vector_space` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/


noncomputable section

universe u

open Function Set Submodule

open BigOperators

variable {ι : Type _} {ι' : Type _} {R : Type _} {R₂ : Type _} {K : Type _}

variable {M : Type _} {M' M'' : Type _} {V : Type u} {V' : Type _}

section Module

variable [Semiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

section

variable (ι) (R) (M)

#print Basis /-
/-- A `basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `coe_fn (b : basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `basis.repr`.
-/
structure Basis where ofRepr ::
  repr : M ≃ₗ[R] ι →₀ R
#align basis Basis
-/

end

#print uniqueBasis /-
instance uniqueBasis [Subsingleton R] : Unique (Basis ι R M) :=
  ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩
#align unique_basis uniqueBasis
-/

namespace Basis

instance : Inhabited (Basis ι R (ι →₀ R)) :=
  ⟨Basis.ofRepr (LinearEquiv.refl _ _)⟩

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

section repr

/- warning: basis.repr_injective -> Basis.repr_injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2], Function.Injective.{max (succ u1) (succ u2) (succ u3), max (succ u3) (succ (max u1 u2))} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (LinearEquiv.{u2, u2, u3, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) M (Finsupp.{u1, u2} ι R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))) _inst_2 (Finsupp.addCommMonoid.{u1, u2} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3 (Finsupp.module.{u1, u2, u2} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Semiring.toModule.{u2} R _inst_1))) (Basis.repr.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2], Function.Injective.{max (max (succ u3) (succ u2)) (succ u1), max (max (succ u3) (succ u2)) (succ u1)} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) (LinearEquiv.{u2, u2, u1, max u2 u3} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) M (Finsupp.{u3, u2} ι R (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1))) _inst_2 (Finsupp.addCommMonoid.{u3, u2} ι R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3 (Finsupp.module.{u3, u2, u2} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Semiring.toModule.{u2} R _inst_1))) (Basis.repr.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align basis.repr_injective Basis.repr_injectiveₓ'. -/
theorem repr_injective : Injective (repr : Basis ι R M → M ≃ₗ[R] ι →₀ R) := fun f g h => by
  cases f <;> cases g <;> congr
#align basis.repr_injective Basis.repr_injective

#print Basis.funLike /-
/-- `b i` is the `i`th basis vector. -/
instance funLike : FunLike (Basis ι R M) ι fun _ => M
    where
  coe b i := b.repr.symm (Finsupp.single i 1)
  coe_injective' f g h :=
    repr_injective <|
      LinearEquiv.symm_bijective.Injective
        (by
          ext x
          rw [← Finsupp.sum_single x, map_finsupp_sum, map_finsupp_sum]
          congr with (i r)
          have := congr_fun h i
          dsimp at this
          rw [← mul_one r, ← Finsupp.smul_single', LinearEquiv.map_smul, LinearEquiv.map_smul,
            this])
#align basis.fun_like Basis.funLike
-/

/- warning: basis.coe_of_repr -> Basis.coe_ofRepr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_of_repr Basis.coe_ofReprₓ'. -/
@[simp]
theorem coe_ofRepr (e : M ≃ₗ[R] ι →₀ R) : ⇑(ofRepr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl
#align basis.coe_of_repr Basis.coe_ofRepr

/- warning: basis.injective -> Basis.injective is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) [_inst_6 : Nontrivial.{u2} R], Function.Injective.{succ u1, succ u3} ι M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b)
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u3, u1} R M _inst_1 _inst_2] (b : Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) [_inst_6 : Nontrivial.{u3} R], Function.Injective.{succ u2, succ u1} ι M (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) b)
Case conversion may be inaccurate. Consider using '#align basis.injective Basis.injectiveₓ'. -/
protected theorem injective [Nontrivial R] : Injective b :=
  b.repr.symm.Injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp
#align basis.injective Basis.injective

/- warning: basis.repr_symm_single_one -> Basis.repr_symm_single_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_symm_single_one Basis.repr_symm_single_oneₓ'. -/
theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl
#align basis.repr_symm_single_one Basis.repr_symm_single_one

/- warning: basis.repr_symm_single -> Basis.repr_symm_single is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_symm_single Basis.repr_symm_singleₓ'. -/
theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i 1) := by
      rw [Finsupp.smul_single', mul_one]
    _ = c • b i := by rw [LinearEquiv.map_smul, repr_symm_single_one]
    
#align basis.repr_symm_single Basis.repr_symm_single

/- warning: basis.repr_self -> Basis.repr_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_self Basis.repr_selfₓ'. -/
@[simp]
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _
#align basis.repr_self Basis.repr_self

/- warning: basis.repr_self_apply -> Basis.repr_self_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_self_apply Basis.repr_self_applyₓ'. -/
theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [repr_self, Finsupp.single_apply]
#align basis.repr_self_apply Basis.repr_self_apply

/- warning: basis.repr_symm_apply -> Basis.repr_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_symm_apply Basis.repr_symm_applyₓ'. -/
@[simp]
theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.total ι M R b v :=
  calc
    b.repr.symm v = b.repr.symm (v.Sum Finsupp.single) := by simp
    _ = ∑ i in v.support, b.repr.symm (Finsupp.single i (v i)) := by
      rw [Finsupp.sum, LinearEquiv.map_sum]
    _ = Finsupp.total ι M R b v := by simp [repr_symm_single, Finsupp.total_apply, Finsupp.sum]
    
#align basis.repr_symm_apply Basis.repr_symm_apply

/- warning: basis.coe_repr_symm -> Basis.coe_repr_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_repr_symm Basis.coe_repr_symmₓ'. -/
@[simp]
theorem coe_repr_symm : ↑b.repr.symm = Finsupp.total ι M R b :=
  LinearMap.ext fun v => b.repr_symm_apply v
#align basis.coe_repr_symm Basis.coe_repr_symm

/- warning: basis.repr_total -> Basis.repr_total is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_total Basis.repr_totalₓ'. -/
@[simp]
theorem repr_total (v) : b.repr (Finsupp.total _ _ _ b v) = v :=
  by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v
#align basis.repr_total Basis.repr_total

/- warning: basis.total_repr -> Basis.total_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.total_repr Basis.total_reprₓ'. -/
@[simp]
theorem total_repr : Finsupp.total _ _ _ b (b.repr x) = x :=
  by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x
#align basis.total_repr Basis.total_repr

/- warning: basis.repr_range -> Basis.repr_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_range Basis.repr_rangeₓ'. -/
theorem repr_range : (b.repr : M →ₗ[R] ι →₀ R).range = Finsupp.supported R R univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]
#align basis.repr_range Basis.repr_range

/- warning: basis.mem_span_repr_support -> Basis.mem_span_repr_support is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mem_span_repr_support Basis.mem_span_repr_supportₓ'. -/
theorem mem_span_repr_support {ι : Type _} (b : Basis ι R M) (m : M) :
    m ∈ span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_total _).2 ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩
#align basis.mem_span_repr_support Basis.mem_span_repr_support

/- warning: basis.repr_support_subset_of_mem_span -> Basis.repr_support_subset_of_mem_span is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_support_subset_of_mem_span Basis.repr_support_subset_of_mem_spanₓ'. -/
theorem repr_support_subset_of_mem_span {ι : Type _} (b : Basis ι R M) (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s :=
  by
  rcases(Finsupp.mem_span_image_iff_total _).1 hm with ⟨l, hl, hlm⟩
  rwa [← hlm, repr_total, ← Finsupp.mem_supported R l]
#align basis.repr_support_subset_of_mem_span Basis.repr_support_subset_of_mem_span

end repr

section Coord

#print Basis.coord /-
/-- `b.coord i` is the linear function giving the `i`'th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps]
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr
#align basis.coord Basis.coord
-/

/- warning: basis.forall_coord_eq_zero_iff -> Basis.forall_coord_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) {x : M}, Iff (forall (i : ι), Eq.{succ u2} R (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.coord.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b i) x) (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))))))) (Eq.{succ u3} M x (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)))))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3) {x : M}, Iff (forall (i : ι), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) x) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (LinearMap.{u3, u3, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u3} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (Basis.coord.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3 b i) x) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) x) 0 (Zero.toOfNat0.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) x) (MonoidWithZero.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) x) (Semiring.toMonoidWithZero.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) x) _inst_1))))) (Eq.{succ u2} M x (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))))
Case conversion may be inaccurate. Consider using '#align basis.forall_coord_eq_zero_iff Basis.forall_coord_eq_zero_iffₓ'. -/
theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.Coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, Finsupp.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff
#align basis.forall_coord_eq_zero_iff Basis.forall_coord_eq_zero_iff

#print Basis.sumCoords /-
/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
noncomputable def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun i => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)
#align basis.sum_coords Basis.sumCoords
-/

/- warning: basis.coe_sum_coords -> Basis.coe_sumCoords is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_sum_coords Basis.coe_sumCoordsₓ'. -/
@[simp]
theorem coe_sumCoords : (b.sumCoords : M → R) = fun m => (b.repr m).Sum fun i => id :=
  rfl
#align basis.coe_sum_coords Basis.coe_sumCoords

/- warning: basis.coe_sum_coords_eq_finsum -> Basis.coe_sumCoords_eq_finsum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} ((fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (Basis.sumCoords.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b)) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.sumCoords.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b)) (fun (m : M) => finsum.{u2, succ u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (fun (i : ι) => coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.coord.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b i) m))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3), Eq.{max (succ u3) (succ u2)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) a) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (LinearMap.{u3, u3, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u3} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (Basis.sumCoords.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3 b)) (fun (m : M) => finsum.{u3, succ u1} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) m) ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) m) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) m) (Semiring.toNonAssocSemiring.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) m) _inst_1))) (fun (i : ι) => FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (LinearMap.{u3, u3, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u3} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (Basis.coord.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3 b i) m))
Case conversion may be inaccurate. Consider using '#align basis.coe_sum_coords_eq_finsum Basis.coe_sumCoords_eq_finsumₓ'. -/
theorem coe_sumCoords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.Coord i m :=
  by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum, Finset.finite_toSet_toFinset, id.def,
    Finsupp.fun_support_eq]
#align basis.coe_sum_coords_eq_finsum Basis.coe_sumCoords_eq_finsum

/- warning: basis.coe_sum_coords_of_fintype -> Basis.coe_sumCoords_of_fintype is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) [_inst_6 : Fintype.{u1} ι], Eq.{max (succ u3) (succ u2)} ((fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (Basis.sumCoords.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b)) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.sumCoords.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b)) (Finset.sum.{max u3 u2, u1} ((fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (Basis.sumCoords.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b)) ι (Pi.addCommMonoid.{u3, u2} M (fun (ᾰ : M) => R) (fun (i : M) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (Finset.univ.{u1} ι _inst_6) (fun (i : ι) => coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.coord.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b i)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] (b : Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) [_inst_6 : Fintype.{u3} ι], Eq.{max (succ u2) (succ u1)} (forall (a : M), (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) a) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (LinearMap.{u2, u2, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.sumCoords.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3 b)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (LinearMap.{u2, u2, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) a) (LinearMap.instFunLikeLinearMap.{u2, u2, u1, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Finset.sum.{max u2 u1, u3} (LinearMap.{u2, u2, u1, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) ι (LinearMap.addCommMonoid.{u2, u2, u1, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Finset.univ.{u3} ι _inst_6) (fun (i : ι) => Basis.coord.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3 b i)))
Case conversion may be inaccurate. Consider using '#align basis.coe_sum_coords_of_fintype Basis.coe_sumCoords_of_fintypeₓ'. -/
@[simp]
theorem coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M → R) = ∑ i, b.Coord i :=
  by
  ext m
  simp only [sum_coords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id.def, Fintype.sum_apply, imp_true_iff, eq_self_iff_true, Finsupp.coe_lsum, LinearMap.coe_comp]
#align basis.coe_sum_coords_of_fintype Basis.coe_sumCoords_of_fintype

/- warning: basis.sum_coords_self_apply -> Basis.sumCoords_self_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (i : ι), Eq.{succ u2} R (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.sumCoords.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b) (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b i)) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u3, u1} R M _inst_1 _inst_2] (b : Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) (i : ι), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (a : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) a) (Basis.funLike.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) b i)) (FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (LinearMap.{u3, u3, u1, u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u1, u3} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (Basis.sumCoords.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3 b) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) b i)) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (a : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) a) (Basis.funLike.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) b i)) 1 (One.toOfNat1.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (a : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) a) (Basis.funLike.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) b i)) (Semiring.toOne.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (a : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) a) (Basis.funLike.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) b i)) _inst_1)))
Case conversion may be inaccurate. Consider using '#align basis.sum_coords_self_apply Basis.sumCoords_self_applyₓ'. -/
@[simp]
theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id.def, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]
#align basis.sum_coords_self_apply Basis.sumCoords_self_apply

/- warning: basis.dvd_coord_smul -> Basis.dvd_coord_smul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (i : ι) (m : M) (r : R), Dvd.Dvd.{u2} R (semigroupDvd.{u2} R (SemigroupWithZero.toSemigroup.{u2} R (NonUnitalSemiring.toSemigroupWithZero.{u2} R (Semiring.toNonUnitalSemiring.{u2} R _inst_1)))) r (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) (fun (_x : LinearMap.{u2, u2, u3, u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1)) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_3 (Semiring.toModule.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Basis.coord.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 b i) (SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_2 _inst_3)))) r m))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3) (i : ι) (m : M) (r : R), Dvd.dvd.{u3} R (semigroupDvd.{u3} R (SemigroupWithZero.toSemigroup.{u3} R (NonUnitalSemiring.toSemigroupWithZero.{u3} R (Semiring.toNonUnitalSemiring.{u3} R _inst_1)))) r (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (LinearMap.{u3, u3, u2, u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u3} R R M R _inst_1 _inst_1 _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (Basis.coord.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3 b i) (HSMul.hSMul.{u3, u2, u2} R M M (instHSMul.{u3, u2} R M (SMulZeroClass.toSMul.{u3, u2} R M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u2} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u2} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Module.toMulActionWithZero.{u3, u2} R M _inst_1 _inst_2 _inst_3))))) r m))
Case conversion may be inaccurate. Consider using '#align basis.dvd_coord_smul Basis.dvd_coord_smulₓ'. -/
theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.Coord i (r • m) :=
  ⟨b.Coord i m, by simp⟩
#align basis.dvd_coord_smul Basis.dvd_coord_smul

/- warning: basis.coord_repr_symm -> Basis.coord_repr_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coord_repr_symm Basis.coord_repr_symmₓ'. -/
theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι →₀ R) : b.Coord i (b.repr.symm f) = f i :=
  by simp only [repr_symm_apply, coord_apply, repr_total]
#align basis.coord_repr_symm Basis.coord_repr_symm

end Coord

section Ext

variable {R₁ : Type _} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}

variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

variable {M₁ : Type _} [AddCommMonoid M₁] [Module R₁ M₁]

/- warning: basis.ext -> Basis.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.ext Basis.extₓ'. -/
/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  by
  ext x
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  simp only [LinearMap.map_sum, LinearMap.map_smulₛₗ, h]
#align basis.ext Basis.ext

include σ'

/- warning: basis.ext' -> Basis.ext' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.ext' Basis.ext'ₓ'. -/
/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
  by
  ext x
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  simp only [LinearEquiv.map_sum, LinearEquiv.map_smulₛₗ, h]
#align basis.ext' Basis.ext'

omit σ'

/- warning: basis.ext_elem_iff -> Basis.ext_elem_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.ext_elem_iff Basis.ext_elem_iffₓ'. -/
/-- Two elements are equal iff their coordinates are equal. -/
theorem ext_elem_iff {x y : M} : x = y ↔ ∀ i, b.repr x i = b.repr y i := by
  simp only [← Finsupp.ext_iff, EmbeddingLike.apply_eq_iff_eq]
#align basis.ext_elem_iff Basis.ext_elem_iff

/- warning: basis.ext_elem -> Basis.ext_elem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.ext_elem Basis.ext_elemₓ'. -/
alias ext_elem_iff ↔ _ _root_.basis.ext_elem
#align basis.ext_elem Basis.ext_elem

/- warning: basis.repr_eq_iff -> Basis.repr_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_eq_iff Basis.repr_eq_iffₓ'. -/
theorem repr_eq_iff {b : Basis ι R M} {f : M →ₗ[R] ι →₀ R} :
    ↑b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩
#align basis.repr_eq_iff Basis.repr_eq_iff

/- warning: basis.repr_eq_iff' -> Basis.repr_eq_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_eq_iff' Basis.repr_eq_iff'ₓ'. -/
theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
    b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩
#align basis.repr_eq_iff' Basis.repr_eq_iff'

/- warning: basis.apply_eq_iff -> Basis.apply_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.apply_eq_iff Basis.apply_eq_iffₓ'. -/
theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.Injective ((b.repr_self i).trans h.symm)⟩
#align basis.apply_eq_iff Basis.apply_eq_iff

/- warning: basis.repr_apply_eq -> Basis.repr_apply_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_apply_eq Basis.repr_apply_eqₓ'. -/
/-- An unbundled version of `repr_eq_iff` -/
theorem repr_apply_eq (f : M → ι → R) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x) (f_eq : ∀ i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i :=
  by
  let f_i : M →ₗ[R] R :=
    { toFun := fun x => f x i
      map_add' := fun _ _ => by rw [hadd, Pi.add_apply]
      map_smul' := fun _ _ => by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i :=
    by
    refine' b.ext fun j => _
    show b.repr (b j) i = f (b j) i
    rw [b.repr_self, f_eq]
  calc
    b.repr x i = f_i x := by
      rw [← this]
      rfl
    _ = f x i := rfl
    
#align basis.repr_apply_eq Basis.repr_apply_eq

/- warning: basis.eq_of_repr_eq_repr -> Basis.eq_ofRepr_eq_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.eq_of_repr_eq_repr Basis.eq_ofRepr_eq_reprₓ'. -/
/-- Two bases are equal if they assign the same coordinates. -/
theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
  repr_injective <| by
    ext
    apply h
#align basis.eq_of_repr_eq_repr Basis.eq_ofRepr_eq_repr

/- warning: basis.eq_of_apply_eq -> Basis.eq_of_apply_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] {b₁ : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3} {b₂ : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3}, (forall (i : ι), Eq.{succ u3} M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b₁ i) (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b₂ i)) -> (Eq.{max (succ u1) (succ u2) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) b₁ b₂)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] {b₁ : Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3} {b₂ : Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3}, (forall (i : ι), Eq.{succ u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) b₁ i) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) b₂ i)) -> (Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) b₁ b₂)
Case conversion may be inaccurate. Consider using '#align basis.eq_of_apply_eq Basis.eq_of_apply_eqₓ'. -/
/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (∀ i, b₁ i = b₂ i) → b₁ = b₂ :=
  FunLike.ext _ _
#align basis.eq_of_apply_eq Basis.eq_of_apply_eq

end Ext

section Map

variable (f : M ≃ₗ[R] M')

#print Basis.map /-
/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
protected def map : Basis ι R M' :=
  ofRepr (f.symm.trans b.repr)
#align basis.map Basis.map
-/

/- warning: basis.map_apply -> Basis.map_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.map_apply Basis.map_applyₓ'. -/
@[simp]
theorem map_apply (i) : b.map f i = f (b i) :=
  rfl
#align basis.map_apply Basis.map_apply

end Map

section MapCoeffs

variable {R' : Type _} [Semiring R'] [Module R' M] (f : R ≃+* R')
  (h : ∀ (c) (x : M), f c • x = c • x)

include f h b

attribute [local instance] SMul.comp.isScalarTower

/- warning: basis.map_coeffs -> Basis.mapCoeffs is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.map_coeffs Basis.mapCoeffsₓ'. -/
/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `basis.algebra_map_coeffs` for the case where `f` is equal to `algebra_map`.
-/
@[simps (config := { simpRhs := true })]
def mapCoeffs : Basis ι R' M :=
  by
  letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by dsimp [(· • ·)]; rw [mul_smul, ← h, f.apply_symm_apply] }
  exact
    of_repr <|
      (b.repr.restrict_scalars R').trans <|
        Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm
#align basis.map_coeffs Basis.mapCoeffs

/- warning: basis.map_coeffs_apply -> Basis.mapCoeffs_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.map_coeffs_apply Basis.mapCoeffs_applyₓ'. -/
theorem mapCoeffs_apply (i : ι) : b.mapCoeffs f h i = b i :=
  apply_eq_iff.mpr <| by simp [f.to_add_equiv_eq_coe]
#align basis.map_coeffs_apply Basis.mapCoeffs_apply

/- warning: basis.coe_map_coeffs -> Basis.coe_mapCoeffs is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_map_coeffs Basis.coe_mapCoeffsₓ'. -/
@[simp]
theorem coe_mapCoeffs : (b.mapCoeffs f h : ι → M) = b :=
  funext <| b.mapCoeffs_apply f h
#align basis.coe_map_coeffs Basis.coe_mapCoeffs

end MapCoeffs

section Reindex

variable (b' : Basis ι' R M')

variable (e : ι ≃ ι')

#print Basis.reindex /-
/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : Basis ι' R M :=
  Basis.ofRepr (b.repr.trans (Finsupp.domLCongr e))
#align basis.reindex Basis.reindex
-/

/- warning: basis.reindex_apply -> Basis.reindex_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u2} ι ι') (i' : ι'), Eq.{succ u4} M (coeFn.{max (succ u2) (succ u3) (succ u4), max (succ u2) (succ u4)} (Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) => ι' -> M) (FunLike.hasCoeToFun.{max (succ u2) (succ u3) (succ u4), succ u2, succ u4} (Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) ι' (fun (_x : ι') => M) (Basis.funLike.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3)) (Basis.reindex.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e) i') (coeFn.{max (succ u1) (succ u3) (succ u4), max (succ u1) (succ u4)} (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u3) (succ u4), succ u1, succ u4} (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3)) b (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e) i'))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u3}} {R : Type.{u2}} {M : Type.{u4}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u2, u4} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u4} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u3} ι ι') (i' : ι'), Eq.{succ u4} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) i') (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u4), succ u3, succ u4} (Basis.{u3, u2, u4} ι' R M _inst_1 _inst_2 _inst_3) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) _x) (Basis.funLike.{u3, u2, u4} ι' R M _inst_1 _inst_2 _inst_3) (Basis.reindex.{u1, u3, u2, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e) i') (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u4), succ u1, succ u4} (Basis.{u1, u2, u4} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u1, u2, u4} ι R M _inst_1 _inst_2 _inst_3) b (FunLike.coe.{max (succ u1) (succ u3), succ u3, succ u1} (Equiv.{succ u3, succ u1} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u3} ι ι' e) i'))
Case conversion may be inaccurate. Consider using '#align basis.reindex_apply Basis.reindex_applyₓ'. -/
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show
    (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
      b.repr.symm (Finsupp.single (e.symm i') 1)
    by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
#align basis.reindex_apply Basis.reindex_apply

/- warning: basis.coe_reindex -> Basis.coe_reindex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{max (succ u2) (succ u4)} ((fun (_x : Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) => ι' -> M) (Basis.reindex.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e)) (coeFn.{max (succ u2) (succ u3) (succ u4), max (succ u2) (succ u4)} (Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) => ι' -> M) (FunLike.hasCoeToFun.{max (succ u2) (succ u3) (succ u4), succ u2, succ u4} (Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) ι' (fun (_x : ι') => M) (Basis.funLike.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3)) (Basis.reindex.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e)) (Function.comp.{succ u2, succ u1, succ u4} ι' ι M (coeFn.{max (succ u1) (succ u3) (succ u4), max (succ u1) (succ u4)} (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u3) (succ u4), succ u1, succ u4} (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3)) b) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e)))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u4}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u4} ι ι'), Eq.{max (succ u4) (succ u3)} (forall (a : ι'), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) a) (FunLike.coe.{max (max (succ u4) (succ u2)) (succ u3), succ u4, succ u3} (Basis.{u4, u2, u3} ι' R M _inst_1 _inst_2 _inst_3) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) _x) (Basis.funLike.{u4, u2, u3} ι' R M _inst_1 _inst_2 _inst_3) (Basis.reindex.{u1, u4, u2, u3} ι ι' R M _inst_1 _inst_2 _inst_3 b e)) (Function.comp.{succ u4, succ u1, succ u3} ι' ι M (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) b) (FunLike.coe.{max (succ u1) (succ u4), succ u4, succ u1} (Equiv.{succ u4, succ u1} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u4, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u4} ι ι' e)))
Case conversion may be inaccurate. Consider using '#align basis.coe_reindex Basis.coe_reindexₓ'. -/
@[simp]
theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
  funext (b.reindex_apply e)
#align basis.coe_reindex Basis.coe_reindex

/- warning: basis.repr_reindex_apply -> Basis.repr_reindex_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_reindex_apply Basis.repr_reindex_applyₓ'. -/
theorem repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
  show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp
#align basis.repr_reindex_apply Basis.repr_reindex_apply

/- warning: basis.repr_reindex -> Basis.repr_reindex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_reindex Basis.repr_reindexₓ'. -/
@[simp]
theorem repr_reindex : (b.reindex e).repr x = (b.repr x).mapDomain e :=
  FunLike.ext _ _ <| by simp [repr_reindex_apply]
#align basis.repr_reindex Basis.repr_reindex

/- warning: basis.reindex_refl -> Basis.reindex_refl is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3), Eq.{max (succ u1) (succ u2) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (Basis.reindex.{u1, u1, u2, u3} ι ι R M _inst_1 _inst_2 _inst_3 b (Equiv.refl.{succ u1} ι)) b
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] (b : Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) (Basis.reindex.{u3, u3, u2, u1} ι ι R M _inst_1 _inst_2 _inst_3 b (Equiv.refl.{succ u3} ι)) b
Case conversion may be inaccurate. Consider using '#align basis.reindex_refl Basis.reindex_reflₓ'. -/
@[simp]
theorem reindex_refl : b.reindex (Equiv.refl ι) = b :=
  eq_of_apply_eq fun i => by simp
#align basis.reindex_refl Basis.reindex_refl

/- warning: basis.range_reindex -> Basis.range_reindex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{succ u4} (Set.{u4} M) (Set.range.{u4, succ u2} M ι' (coeFn.{max (succ u2) (succ u3) (succ u4), max (succ u2) (succ u4)} (Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) => ι' -> M) (FunLike.hasCoeToFun.{max (succ u2) (succ u3) (succ u4), succ u2, succ u4} (Basis.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3) ι' (fun (_x : ι') => M) (Basis.funLike.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3)) (Basis.reindex.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e))) (Set.range.{u4, succ u1} M ι (coeFn.{max (succ u1) (succ u3) (succ u4), max (succ u1) (succ u4)} (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u3) (succ u4), succ u1, succ u4} (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3)) b))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u3}} {R : Type.{u2}} {M : Type.{u4}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u2, u4} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u4} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u3} ι ι'), Eq.{succ u4} (Set.{u4} M) (Set.range.{u4, succ u3} M ι' (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u4), succ u3, succ u4} (Basis.{u3, u2, u4} ι' R M _inst_1 _inst_2 _inst_3) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι') => M) _x) (Basis.funLike.{u3, u2, u4} ι' R M _inst_1 _inst_2 _inst_3) (Basis.reindex.{u1, u3, u2, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e))) (Set.range.{u4, succ u1} M ι (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u4), succ u1, succ u4} (Basis.{u1, u2, u4} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u1, u2, u4} ι R M _inst_1 _inst_2 _inst_3) b))
Case conversion may be inaccurate. Consider using '#align basis.range_reindex Basis.range_reindexₓ'. -/
/-- `simp` can prove this as `basis.coe_reindex` + `equiv_like.range_comp` -/
theorem range_reindex : Set.range (b.reindex e) = Set.range b := by
  rw [coe_reindex, EquivLike.range_comp]
#align basis.range_reindex Basis.range_reindex

/- warning: basis.sum_coords_reindex -> Basis.sumCoords_reindex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{max (succ u4) (succ u3)} (LinearMap.{u3, u3, u4, u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_3 (Semiring.toModule.{u3} R _inst_1)) (Basis.sumCoords.{u2, u3, u4} ι' R M _inst_1 _inst_2 _inst_3 (Basis.reindex.{u1, u2, u3, u4} ι ι' R M _inst_1 _inst_2 _inst_3 b e)) (Basis.sumCoords.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3 b)
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u4}} {M : Type.{u3}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u4, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u4, u3} ι R M _inst_1 _inst_2 _inst_3) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{max (succ u4) (succ u3)} (LinearMap.{u4, u4, u3, u4} R R _inst_1 _inst_1 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1)) M R _inst_2 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} R (Semiring.toNonAssocSemiring.{u4} R _inst_1))) _inst_3 (Semiring.toModule.{u4} R _inst_1)) (Basis.sumCoords.{u2, u4, u3} ι' R M _inst_1 _inst_2 _inst_3 (Basis.reindex.{u1, u2, u4, u3} ι ι' R M _inst_1 _inst_2 _inst_3 b e)) (Basis.sumCoords.{u1, u4, u3} ι R M _inst_1 _inst_2 _inst_3 b)
Case conversion may be inaccurate. Consider using '#align basis.sum_coords_reindex Basis.sumCoords_reindexₓ'. -/
@[simp]
theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords :=
  by
  ext x
  simp only [coe_sum_coords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl
#align basis.sum_coords_reindex Basis.sumCoords_reindex

#print Basis.reindexRange /-
/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindexRange : Basis (range b) R M :=
  haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    letI := h
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    Basis.ofRepr (Module.subsingletonEquiv R M (range b))
#align basis.reindex_range Basis.reindexRange
-/

/- warning: basis.reindex_range_self -> Basis.reindexRange_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_range_self Basis.reindexRange_selfₓ'. -/
theorem reindexRange_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i :=
  by
  by_cases htr : Nontrivial R
  · letI := htr
    simp [htr, reindex_range, reindex_apply, Equiv.apply_ofInjective_symm b.injective,
      Subtype.coe_mk]
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp htr
    letI := Module.subsingleton R M
    simp [reindex_range]
#align basis.reindex_range_self Basis.reindexRange_self

/- warning: basis.reindex_range_repr_self -> Basis.reindexRange_repr_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_range_repr_self Basis.reindexRange_repr_selfₓ'. -/
theorem reindexRange_repr_self (i : ι) :
    b.reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _
    
#align basis.reindex_range_repr_self Basis.reindexRange_repr_self

/- warning: basis.reindex_range_apply -> Basis.reindexRange_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_range_apply Basis.reindexRange_applyₓ'. -/
@[simp]
theorem reindexRange_apply (x : range b) : b.reindexRange x = x :=
  by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindex_range_self i
#align basis.reindex_range_apply Basis.reindexRange_apply

/- warning: basis.reindex_range_repr' -> Basis.reindexRange_repr' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_range_repr' Basis.reindexRange_repr'ₓ'. -/
theorem reindexRange_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
    b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i :=
  by
  nontriviality
  subst h
  refine' (b.repr_apply_eq (fun x i => b.reindex_range.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, LinearEquiv.map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp only [Pi.smul_apply, LinearEquiv.map_smul, Finsupp.coe_smul]
  · intro i
    ext j
    simp only [reindex_range_repr_self]
    refine' @Finsupp.single_apply_left _ _ _ _ (fun i => (⟨b i, _⟩ : Set.range b)) _ _ _ _
    exact fun i j h => b.injective (Subtype.mk.inj h)
#align basis.reindex_range_repr' Basis.reindexRange_repr'

/- warning: basis.reindex_range_repr -> Basis.reindexRange_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_range_repr Basis.reindexRange_reprₓ'. -/
@[simp]
theorem reindexRange_repr (x : M) (i : ι) (h := Set.mem_range_self i) :
    b.reindexRange.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindexRange_repr' _ rfl
#align basis.reindex_range_repr Basis.reindexRange_repr

section Fintype

variable [Fintype ι] [DecidableEq M]

#print Basis.reindexFinsetRange /-
/-- `b.reindex_finset_range` is a basis indexed by `finset.univ.image b`,
the finite set of basis vectors themselves. -/
def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))
#align basis.reindex_finset_range Basis.reindexFinsetRange
-/

/- warning: basis.reindex_finset_range_self -> Basis.reindexFinsetRange_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_finset_range_self Basis.reindexFinsetRange_selfₓ'. -/
theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i :=
  by
  rw [reindex_finset_range, reindex_apply, reindex_range_apply]
  rfl
#align basis.reindex_finset_range_self Basis.reindexFinsetRange_self

/- warning: basis.reindex_finset_range_apply -> Basis.reindexFinsetRange_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_finset_range_apply Basis.reindexFinsetRange_applyₓ'. -/
@[simp]
theorem reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x :=
  by
  rcases x with ⟨bi, hbi⟩
  rcases finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindex_finset_range_self i
#align basis.reindex_finset_range_apply Basis.reindexFinsetRange_apply

/- warning: basis.reindex_finset_range_repr_self -> Basis.reindexFinsetRange_repr_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_finset_range_repr_self Basis.reindexFinsetRange_repr_selfₓ'. -/
theorem reindexFinsetRange_repr_self (i : ι) :
    b.reindexFinsetRange.repr (b i) =
      Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 :=
  by
  ext ⟨bi, hbi⟩
  rw [reindex_finset_range, repr_reindex, Finsupp.mapDomain_equiv_apply, reindex_range_repr_self]
  convert Finsupp.single_apply_left ((Equiv.refl M).subtypeEquiv _).symm.Injective _ _ _
  rfl
#align basis.reindex_finset_range_repr_self Basis.reindexFinsetRange_repr_self

/- warning: basis.reindex_finset_range_repr -> Basis.reindexFinsetRange_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.reindex_finset_range_repr Basis.reindexFinsetRange_reprₓ'. -/
@[simp]
theorem reindexFinsetRange_repr (x : M) (i : ι)
    (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange.repr x ⟨b i, h⟩ = b.repr x i := by simp [reindex_finset_range]
#align basis.reindex_finset_range_repr Basis.reindexFinsetRange_repr

end Fintype

end Reindex

/- warning: basis.linear_independent -> Basis.linearIndependent is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3), LinearIndependent.{u1, u2, u3} ι R M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b) _inst_1 _inst_2 _inst_3
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] (b : Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3), LinearIndependent.{u3, u2, u1} ι R M (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) b) _inst_1 _inst_2 _inst_3
Case conversion may be inaccurate. Consider using '#align basis.linear_independent Basis.linearIndependentₓ'. -/
protected theorem linearIndependent : LinearIndependent R b :=
  linearIndependent_iff.mpr fun l hl =>
    calc
      l = b.repr (Finsupp.total _ _ _ b l) := (b.repr_total l).symm
      _ = 0 := by rw [hl, LinearEquiv.map_zero]
      
#align basis.linear_independent Basis.linearIndependent

/- warning: basis.ne_zero -> Basis.ne_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) [_inst_6 : Nontrivial.{u2} R] (i : ι), Ne.{succ u3} M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b i) (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] (b : Basis.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3) [_inst_6 : Nontrivial.{u3} R] (i : ι), Ne.{succ u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (FunLike.coe.{max (max (succ u1) (succ u3)) (succ u2), succ u1, succ u2} (Basis.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3) b i) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) 0 (Zero.toOfNat0.{u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddMonoid.toZero.{u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_2))))
Case conversion may be inaccurate. Consider using '#align basis.ne_zero Basis.ne_zeroₓ'. -/
protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=
  b.LinearIndependent.NeZero i
#align basis.ne_zero Basis.ne_zero

#print Basis.mem_span /-
protected theorem mem_span (x : M) : x ∈ span R (range b) :=
  by
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
#align basis.mem_span Basis.mem_span
-/

/- warning: basis.span_eq -> Basis.span_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3), Eq.{succ u3} (Submodule.{u2, u3} R M _inst_1 _inst_2 _inst_3) (Submodule.span.{u2, u3} R M _inst_1 _inst_2 _inst_3 (Set.range.{u3, succ u1} M ι (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (fun (_x : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3)) b))) (Top.top.{u3} (Submodule.{u2, u3} R M _inst_1 _inst_2 _inst_3) (Submodule.hasTop.{u2, u3} R M _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] (b : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3), Eq.{succ u3} (Submodule.{u2, u3} R M _inst_1 _inst_2 _inst_3) (Submodule.span.{u2, u3} R M _inst_1 _inst_2 _inst_3 (Set.range.{u3, succ u1} M ι (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) b))) (Top.top.{u3} (Submodule.{u2, u3} R M _inst_1 _inst_2 _inst_3) (Submodule.instTopSubmodule.{u2, u3} R M _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align basis.span_eq Basis.span_eqₓ'. -/
protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr fun x _ => b.mem_span x
#align basis.span_eq Basis.span_eq

/- warning: basis.index_nonempty -> Basis.index_nonempty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2], (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) -> (forall [_inst_6 : Nontrivial.{u3} M], Nonempty.{succ u1} ι)
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2], (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) -> (forall [_inst_6 : Nontrivial.{u1} M], Nonempty.{succ u3} ι)
Case conversion may be inaccurate. Consider using '#align basis.index_nonempty Basis.index_nonemptyₓ'. -/
theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι :=
  by
  obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 Ne)
  exact ⟨i⟩
#align basis.index_nonempty Basis.index_nonempty

/- warning: basis.mem_submodule_iff -> Basis.mem_submodule_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mem_submodule_iff Basis.mem_submodule_iffₓ'. -/
/-- If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basis vectors. -/
theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • b i :=
  by
  conv_lhs =>
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ←
      Finsupp.range_total]
  simpa only [@eq_comm _ x]
#align basis.mem_submodule_iff Basis.mem_submodule_iff

section Constr

variable (S : Type _) [Semiring S] [Module S M']

variable [SMulCommClass R S M']

#print Basis.constr /-
/-- Construct a linear map given the value at the basis.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr : (ι → M') ≃ₗ[S] M →ₗ[R] M'
    where
  toFun f := (Finsupp.total M' M' R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine' b.ext fun i => _
    simp
  map_add' f g := by
    refine' b.ext fun i => _
    simp
  map_smul' c f := by
    refine' b.ext fun i => _
    simp
#align basis.constr Basis.constr
-/

/- warning: basis.constr_def -> Basis.constr_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_def Basis.constr_defₓ'. -/
theorem constr_def (f : ι → M') :
    b.constr S f = Finsupp.total M' M' R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl
#align basis.constr_def Basis.constr_def

/- warning: basis.constr_apply -> Basis.constr_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_apply Basis.constr_applyₓ'. -/
theorem constr_apply (f : ι → M') (x : M) : b.constr S f x = (b.repr x).Sum fun b a => a • f b :=
  by
  simp only [constr_def, LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.total_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]
#align basis.constr_apply Basis.constr_apply

/- warning: basis.constr_basis -> Basis.constr_basis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_basis Basis.constr_basisₓ'. -/
@[simp]
theorem constr_basis (f : ι → M') (i : ι) : (b.constr S f : M → M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]
#align basis.constr_basis Basis.constr_basis

/- warning: basis.constr_eq -> Basis.constr_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_eq Basis.constr_eqₓ'. -/
theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) : b.constr S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)
#align basis.constr_eq Basis.constr_eq

/- warning: basis.constr_self -> Basis.constr_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_self Basis.constr_selfₓ'. -/
theorem constr_self (f : M →ₗ[R] M') : (b.constr S fun i => f (b i)) = f :=
  b.constr_eq S fun x => rfl
#align basis.constr_self Basis.constr_self

/- warning: basis.constr_range -> Basis.constr_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_range Basis.constr_rangeₓ'. -/
theorem constr_range [Nonempty ι] {f : ι → M'} : (b.constr S f).range = span R (range f) := by
  rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmapDomain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_total, Set.image_id]
#align basis.constr_range Basis.constr_range

/- warning: basis.constr_comp -> Basis.constr_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_comp Basis.constr_compₓ'. -/
@[simp]
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') : b.constr S (f ∘ v) = f.comp (b.constr S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply]
#align basis.constr_comp Basis.constr_comp

end Constr

section Equiv

variable (b' : Basis ι' R M') (e : ι ≃ ι')

variable [AddCommMonoid M''] [Module R M'']

#print Basis.equiv /-
/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm
#align basis.equiv Basis.equiv
-/

/- warning: basis.equiv_apply -> Basis.equiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv_apply Basis.equiv_applyₓ'. -/
@[simp]
theorem equiv_apply : b.Equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]
#align basis.equiv_apply Basis.equiv_apply

#print Basis.equiv_refl /-
@[simp]
theorem equiv_refl : b.Equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp
#align basis.equiv_refl Basis.equiv_refl
-/

/- warning: basis.equiv_symm -> Basis.equiv_symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} {M' : Type.{u5}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u5} M'] [_inst_5 : Module.{u3, u5} R M' _inst_1 _inst_4] (b : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (b' : Basis.{u2, u3, u5} ι' R M' _inst_1 _inst_4 _inst_5) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{max (succ u5) (succ u4)} (LinearEquiv.{u3, u3, u5, u4} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) M' M _inst_4 _inst_2 _inst_5 _inst_3) (LinearEquiv.symm.{u3, u3, u4, u5} R R M M' _inst_1 _inst_1 _inst_2 _inst_4 _inst_3 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (Basis.equiv.{u1, u2, u3, u4, u5} ι ι' R M M' _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 b b' e)) (Basis.equiv.{u2, u1, u3, u5, u4} ι' ι R M' M _inst_1 _inst_4 _inst_5 _inst_2 _inst_3 b' b (Equiv.symm.{succ u1, succ u2} ι ι' e))
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u1}} {R : Type.{u3}} {M : Type.{u5}} {M' : Type.{u4}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u5} M] [_inst_3 : Module.{u3, u5} R M _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u4} M'] [_inst_5 : Module.{u3, u4} R M' _inst_1 _inst_4] (b : Basis.{u2, u3, u5} ι R M _inst_1 _inst_2 _inst_3) (b' : Basis.{u1, u3, u4} ι' R M' _inst_1 _inst_4 _inst_5) (e : Equiv.{succ u2, succ u1} ι ι'), Eq.{max (succ u5) (succ u4)} (LinearEquiv.{u3, u3, u4, u5} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) M' M _inst_4 _inst_2 _inst_5 _inst_3) (LinearEquiv.symm.{u3, u3, u5, u4} R R M M' _inst_1 _inst_1 _inst_2 _inst_4 _inst_3 _inst_5 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (Basis.equiv.{u2, u1, u3, u5, u4} ι ι' R M M' _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 b b' e)) (Basis.equiv.{u1, u2, u3, u4, u5} ι' ι R M' M _inst_1 _inst_4 _inst_5 _inst_2 _inst_3 b' b (Equiv.symm.{succ u2, succ u1} ι ι' e))
Case conversion may be inaccurate. Consider using '#align basis.equiv_symm Basis.equiv_symmₓ'. -/
@[simp]
theorem equiv_symm : (b.Equiv b' e).symm = b'.Equiv b e.symm :=
  b'.ext' fun i => (b.Equiv b' e).Injective (by simp)
#align basis.equiv_symm Basis.equiv_symm

/- warning: basis.equiv_trans -> Basis.equiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv_trans Basis.equiv_transₓ'. -/
@[simp]
theorem equiv_trans {ι'' : Type _} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.Equiv b' e).trans (b'.Equiv b'' e') = b.Equiv b'' (e.trans e') :=
  b.ext' fun i => by simp
#align basis.equiv_trans Basis.equiv_trans

/- warning: basis.map_equiv -> Basis.map_equiv is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} {M' : Type.{u5}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u5} M'] [_inst_5 : Module.{u3, u5} R M' _inst_1 _inst_4] (b : Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) (b' : Basis.{u2, u3, u5} ι' R M' _inst_1 _inst_4 _inst_5) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{max (succ u1) (succ u3) (succ u5)} (Basis.{u1, u3, u5} ι R M' _inst_1 _inst_4 _inst_5) (Basis.map.{u1, u3, u4, u5} ι R M M' _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 b (Basis.equiv.{u1, u2, u3, u4, u5} ι ι' R M M' _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 b b' e)) (Basis.reindex.{u2, u1, u3, u5} ι' ι R M' _inst_1 _inst_4 _inst_5 b' (Equiv.symm.{succ u1, succ u2} ι ι' e))
but is expected to have type
  forall {ι : Type.{u5}} {ι' : Type.{u2}} {R : Type.{u4}} {M : Type.{u3}} {M' : Type.{u1}} [_inst_1 : Semiring.{u4} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u4, u3} R M _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u1} M'] [_inst_5 : Module.{u4, u1} R M' _inst_1 _inst_4] (b : Basis.{u5, u4, u3} ι R M _inst_1 _inst_2 _inst_3) (b' : Basis.{u2, u4, u1} ι' R M' _inst_1 _inst_4 _inst_5) (e : Equiv.{succ u5, succ u2} ι ι'), Eq.{max (max (succ u5) (succ u4)) (succ u1)} (Basis.{u5, u4, u1} ι R M' _inst_1 _inst_4 _inst_5) (Basis.map.{u5, u4, u3, u1} ι R M M' _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 b (Basis.equiv.{u5, u2, u4, u3, u1} ι ι' R M M' _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 b b' e)) (Basis.reindex.{u2, u5, u4, u1} ι' ι R M' _inst_1 _inst_4 _inst_5 b' (Equiv.symm.{succ u5, succ u2} ι ι' e))
Case conversion may be inaccurate. Consider using '#align basis.map_equiv Basis.map_equivₓ'. -/
@[simp]
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.Equiv b' e) = b'.reindex e.symm :=
  by
  ext i
  simp
#align basis.map_equiv Basis.map_equiv

end Equiv

section Prod

variable (b' : Basis ι' R M')

/- warning: basis.prod -> Basis.prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} {M' : Type.{u5}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u5} M'] [_inst_5 : Module.{u3, u5} R M' _inst_1 _inst_4], (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) -> (Basis.{u2, u3, u5} ι' R M' _inst_1 _inst_4 _inst_5) -> (Basis.{max u1 u2, u3, max u4 u5} (Sum.{u1, u2} ι ι') R (Prod.{u4, u5} M M') _inst_1 (Prod.addCommMonoid.{u4, u5} M M' _inst_2 _inst_4) (Prod.module.{u3, u4, u5} R M M' _inst_1 _inst_2 _inst_4 _inst_3 _inst_5))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {R : Type.{u3}} {M : Type.{u4}} {M' : Type.{u5}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u4} M] [_inst_3 : Module.{u3, u4} R M _inst_1 _inst_2] [_inst_4 : AddCommMonoid.{u5} M'] [_inst_5 : Module.{u3, u5} R M' _inst_1 _inst_4], (Basis.{u1, u3, u4} ι R M _inst_1 _inst_2 _inst_3) -> (Basis.{u2, u3, u5} ι' R M' _inst_1 _inst_4 _inst_5) -> (Basis.{max u2 u1, u3, max u5 u4} (Sum.{u1, u2} ι ι') R (Prod.{u4, u5} M M') _inst_1 (Prod.instAddCommMonoidSum.{u4, u5} M M' _inst_2 _inst_4) (Prod.module.{u3, u4, u5} R M M' _inst_1 _inst_2 _inst_4 _inst_3 _inst_5))
Case conversion may be inaccurate. Consider using '#align basis.prod Basis.prodₓ'. -/
/-- `basis.prod` maps a `ι`-indexed basis for `M` and a `ι'`-indexed basis for `M'`
to a `ι ⊕ ι'`-index basis for `M × M'`.
For the specific case of `R × R`, see also `basis.fin_two_prod`. -/
protected def prod : Basis (Sum ι ι') R (M × M') :=
  ofRepr ((b.repr.Prod b'.repr).trans (Finsupp.sumFinsuppLEquivProdFinsupp R).symm)
#align basis.prod Basis.prod

/- warning: basis.prod_repr_inl -> Basis.prod_repr_inl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_repr_inl Basis.prod_repr_inlₓ'. -/
@[simp]
theorem prod_repr_inl (x) (i) : (b.Prod b').repr x (Sum.inl i) = b.repr x.1 i :=
  rfl
#align basis.prod_repr_inl Basis.prod_repr_inl

/- warning: basis.prod_repr_inr -> Basis.prod_repr_inr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_repr_inr Basis.prod_repr_inrₓ'. -/
@[simp]
theorem prod_repr_inr (x) (i) : (b.Prod b').repr x (Sum.inr i) = b'.repr x.2 i :=
  rfl
#align basis.prod_repr_inr Basis.prod_repr_inr

/- warning: basis.prod_apply_inl_fst -> Basis.prod_apply_inl_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_apply_inl_fst Basis.prod_apply_inl_fstₓ'. -/
theorem prod_apply_inl_fst (i) : (b.Prod b' (Sum.inl i)).1 = b i :=
  b.repr.Injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.fst_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inl_injective
#align basis.prod_apply_inl_fst Basis.prod_apply_inl_fst

/- warning: basis.prod_apply_inr_fst -> Basis.prod_apply_inr_fst is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_apply_inr_fst Basis.prod_apply_inr_fstₓ'. -/
theorem prod_apply_inr_fst (i) : (b.Prod b' (Sum.inr i)).1 = 0 :=
  b.repr.Injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.fst_sumFinsuppLEquivProdFinsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inr_ne_inl
#align basis.prod_apply_inr_fst Basis.prod_apply_inr_fst

/- warning: basis.prod_apply_inl_snd -> Basis.prod_apply_inl_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_apply_inl_snd Basis.prod_apply_inl_sndₓ'. -/
theorem prod_apply_inl_snd (i) : (b.Prod b' (Sum.inl i)).2 = 0 :=
  b'.repr.Injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.snd_sumFinsuppLEquivProdFinsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inl_ne_inr
#align basis.prod_apply_inl_snd Basis.prod_apply_inl_snd

/- warning: basis.prod_apply_inr_snd -> Basis.prod_apply_inr_snd is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_apply_inr_snd Basis.prod_apply_inr_sndₓ'. -/
theorem prod_apply_inr_snd (i) : (b.Prod b' (Sum.inr i)).2 = b' i :=
  b'.repr.Injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.snd_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inr_injective
#align basis.prod_apply_inr_snd Basis.prod_apply_inr_snd

/- warning: basis.prod_apply -> Basis.prod_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.prod_apply Basis.prod_applyₓ'. -/
@[simp]
theorem prod_apply (i) :
    b.Prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, prod_apply_inl_snd, prod_apply_inr_snd, comp_app]
#align basis.prod_apply Basis.prod_apply

end Prod

section NoZeroSMulDivisors

/- warning: basis.no_zero_smul_divisors -> Basis.noZeroSMulDivisors is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] [_inst_6 : NoZeroDivisors.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))], (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) -> (NoZeroSMulDivisors.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_2 _inst_3)))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u3, u1} R M _inst_1 _inst_2] [_inst_6 : NoZeroDivisors.{u3} R (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1))], (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) -> (NoZeroSMulDivisors.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_2 _inst_3)))))
Case conversion may be inaccurate. Consider using '#align basis.no_zero_smul_divisors Basis.noZeroSMulDivisorsₓ'. -/
-- Can't be an instance because the basis can't be inferred.
protected theorem noZeroSMulDivisors [NoZeroDivisors R] (b : Basis ι R M) :
    NoZeroSMulDivisors R M :=
  ⟨fun c x hcx =>
    or_iff_not_imp_right.mpr fun hx =>
      by
      rw [← b.total_repr x, ← LinearMap.map_smul] at hcx
      have := linear_independent_iff.mp b.linear_independent (c • b.repr x) hcx
      rw [smul_eq_zero] at this
      exact this.resolve_right fun hr => hx (b.repr.map_eq_zero_iff.mp hr)⟩
#align basis.no_zero_smul_divisors Basis.noZeroSMulDivisors

/- warning: basis.smul_eq_zero -> Basis.smul_eq_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] [_inst_6 : NoZeroDivisors.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))))], (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) -> (forall {c : R} {x : M}, Iff (Eq.{succ u3} M (SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_2 _inst_3)))) c x) (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2))))))) (Or (Eq.{succ u2} R c (OfNat.ofNat.{u2} R 0 (OfNat.mk.{u2} R 0 (Zero.zero.{u2} R (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))))))) (Eq.{succ u3} M x (OfNat.ofNat.{u3} M 0 (OfNat.mk.{u3} M 0 (Zero.zero.{u3} M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_2)))))))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u3, u1} R M _inst_1 _inst_2] [_inst_6 : NoZeroDivisors.{u3} R (NonUnitalNonAssocSemiring.toMul.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1))], (Basis.{u2, u3, u1} ι R M _inst_1 _inst_2 _inst_3) -> (forall {c : R} {x : M}, Iff (Eq.{succ u1} M (HSMul.hSMul.{u3, u1, u1} R M M (instHSMul.{u3, u1} R M (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_2 _inst_3))))) c x) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2))))) (Or (Eq.{succ u3} R c (OfNat.ofNat.{u3} R 0 (Zero.toOfNat0.{u3} R (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1))))) (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align basis.smul_eq_zero Basis.smul_eq_zeroₓ'. -/
protected theorem smul_eq_zero [NoZeroDivisors R] (b : Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 :=
  @smul_eq_zero _ _ _ _ _ b.NoZeroSMulDivisors _ _
#align basis.smul_eq_zero Basis.smul_eq_zero

/- warning: eq_bot_of_rank_eq_zero -> Basis.eq_bot_of_rank_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align eq_bot_of_rank_eq_zero Basis.eq_bot_of_rank_eq_zeroₓ'. -/
theorem Basis.eq_bot_of_rank_eq_zero [NoZeroDivisors R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R (coe ∘ v : Fin m → M) → m = 0) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine' ⟨1, fun _ => ⟨x, hx⟩, _, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  cases i
  simp only [Function.const_apply, Fin.default_eq_zero, Submodule.coe_mk, Finset.univ_unique,
    Function.comp_const, Finset.sum_singleton] at sum_eq
  convert(b.smul_eq_zero.mp sum_eq).resolve_right x_ne
#align eq_bot_of_rank_eq_zero Basis.eq_bot_of_rank_eq_zero

end NoZeroSMulDivisors

section Singleton

#print Basis.singleton /-
/-- `basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type _) [Unique ι] [Semiring R] : Basis ι R R :=
  ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
#align basis.singleton Basis.singleton
-/

/- warning: basis.singleton_apply -> Basis.singleton_apply is a dubious translation:
lean 3 declaration is
  forall (ι : Type.{u1}) (R : Type.{u2}) [_inst_6 : Unique.{succ u1} ι] [_inst_7 : Semiring.{u2} R] (i : ι), Eq.{succ u2} R (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Basis.{u1, u2, u2} ι R R _inst_7 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_7))) (Semiring.toModule.{u2} R _inst_7)) (fun (_x : Basis.{u1, u2, u2} ι R R _inst_7 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_7))) (Semiring.toModule.{u2} R _inst_7)) => ι -> R) (FunLike.hasCoeToFun.{max (succ u1) (succ u2), succ u1, succ u2} (Basis.{u1, u2, u2} ι R R _inst_7 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_7))) (Semiring.toModule.{u2} R _inst_7)) ι (fun (_x : ι) => R) (Basis.funLike.{u1, u2, u2} ι R R _inst_7 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_7))) (Semiring.toModule.{u2} R _inst_7))) (Basis.singleton.{u1, u2} ι R _inst_6 _inst_7) i) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_7)))))))
but is expected to have type
  forall (ι : Type.{u2}) (R : Type.{u1}) [_inst_6 : Unique.{succ u2} ι] [_inst_7 : Semiring.{u1} R] (i : ι), Eq.{succ u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => R) i) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Basis.{u2, u1, u1} ι R R _inst_7 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_7))) (Semiring.toModule.{u1} R _inst_7)) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => R) _x) (Basis.funLike.{u2, u1, u1} ι R R _inst_7 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_7))) (Semiring.toModule.{u1} R _inst_7)) (Basis.singleton.{u2, u1} ι R _inst_6 _inst_7) i) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => R) i) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => R) i) (Semiring.toOne.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => R) i) _inst_7)))
Case conversion may be inaccurate. Consider using '#align basis.singleton_apply Basis.singleton_applyₓ'. -/
@[simp]
theorem singleton_apply (ι R : Type _) [Unique ι] [Semiring R] (i) : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr (by simp [Basis.singleton])
#align basis.singleton_apply Basis.singleton_apply

/- warning: basis.singleton_repr -> Basis.singleton_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.singleton_repr Basis.singleton_reprₓ'. -/
@[simp]
theorem singleton_repr (ι R : Type _) [Unique ι] [Semiring R] (x i) :
    (Basis.singleton ι R).repr x i = x := by simp [Basis.singleton, Unique.eq_default i]
#align basis.singleton_repr Basis.singleton_repr

/- warning: basis.basis_singleton_iff -> Basis.basis_singleton_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.basis_singleton_iff Basis.basis_singleton_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ≠ » 0) -/
theorem basis_singleton_iff {R M : Type _} [Ring R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (ι : Type _) [Unique ι] :
    Nonempty (Basis ι R M) ↔ ∃ (x : _)(_ : x ≠ 0), ∀ y : M, ∃ r : R, r • x = y :=
  by
  fconstructor
  · rintro ⟨b⟩
    refine' ⟨b default, b.linear_independent.ne_zero _, _⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
    refine'
      ⟨of_repr <|
          LinearEquiv.symm
            { toFun := fun f => f default • x
              invFun := fun y => Finsupp.single default (w y).some
              left_inv := fun f => Finsupp.unique_ext _
              right_inv := fun y => _
              map_add' := fun y z => _
              map_smul' := fun c y => _ }⟩
    · rw [Finsupp.add_apply, add_smul]
    · rw [Finsupp.smul_apply, smul_assoc]
      simp
    · refine' smul_left_injective _ nz _
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec
#align basis.basis_singleton_iff Basis.basis_singleton_iff

end Singleton

section Empty

variable (M)

#print Basis.empty /-
/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  ofRepr 0
#align basis.empty Basis.empty
-/

#print Basis.emptyUnique /-
instance emptyUnique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M)
    where
  default := Basis.empty M
  uniq := fun ⟨x⟩ => congr_arg ofRepr <| Subsingleton.elim _ _
#align basis.empty_unique Basis.emptyUnique
-/

end Empty

end Basis

section Fintype

open Basis

open Fintype

variable [Fintype ι] (b : Basis ι R M)

#print Basis.equivFun /-
/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def Basis.equivFun : M ≃ₗ[R] ι → R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := coeFn
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι →₀ R) ≃ₗ[R] ι → R)
#align basis.equiv_fun Basis.equivFun
-/

#print Module.fintypeOfFintype /-
/-- A module over a finite ring that admits a finite basis is finite. -/
def Module.fintypeOfFintype (b : Basis ι R M) [Fintype R] : Fintype M :=
  haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equiv_fun.to_equiv.symm
#align module.fintype_of_fintype Module.fintypeOfFintype
-/

/- warning: module.card_fintype -> Module.card_fintype is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] [_inst_6 : Fintype.{u1} ι], (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) -> (forall [_inst_7 : Fintype.{u2} R] [_inst_8 : Fintype.{u3} M], Eq.{1} Nat (Fintype.card.{u3} M _inst_8) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (Fintype.card.{u2} R _inst_7) (Fintype.card.{u1} ι _inst_6)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] [_inst_6 : Fintype.{u3} ι], (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) -> (forall [_inst_7 : Fintype.{u2} R] [_inst_8 : Fintype.{u1} M], Eq.{1} Nat (Fintype.card.{u1} M _inst_8) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (Fintype.card.{u2} R _inst_7) (Fintype.card.{u3} ι _inst_6)))
Case conversion may be inaccurate. Consider using '#align module.card_fintype Module.card_fintypeₓ'. -/
theorem Module.card_fintype (b : Basis ι R M) [Fintype R] [Fintype M] : card M = card R ^ card ι :=
  by
  classical exact
      calc
        card M = card (ι → R) := card_congr b.equiv_fun.to_equiv
        _ = card R ^ card ι := card_fun
        
#align module.card_fintype Module.card_fintype

/- warning: basis.equiv_fun_symm_apply -> Basis.equivFun_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv_fun_symm_apply Basis.equivFun_symm_applyₓ'. -/
/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
theorem Basis.equivFun_symm_apply (x : ι → R) : b.equivFun.symm x = ∑ i, x i • b i := by
  simp [Basis.equivFun, Finsupp.total_apply, Finsupp.sum_fintype]
#align basis.equiv_fun_symm_apply Basis.equivFun_symm_apply

/- warning: basis.equiv_fun_apply -> Basis.equivFun_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv_fun_apply Basis.equivFun_applyₓ'. -/
@[simp]
theorem Basis.equivFun_apply (u : M) : b.equivFun u = b.repr u :=
  rfl
#align basis.equiv_fun_apply Basis.equivFun_apply

/- warning: basis.map_equiv_fun -> Basis.map_equivFun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.map_equiv_fun Basis.map_equivFunₓ'. -/
@[simp]
theorem Basis.map_equivFun (f : M ≃ₗ[R] M') : (b.map f).equivFun = f.symm.trans b.equivFun :=
  rfl
#align basis.map_equiv_fun Basis.map_equivFun

/- warning: basis.sum_equiv_fun -> Basis.sum_equivFun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.sum_equiv_fun Basis.sum_equivFunₓ'. -/
theorem Basis.sum_equivFun (u : M) : (∑ i, b.equivFun u i • b i) = u :=
  by
  conv_rhs => rw [← b.total_repr u]
  simp [Finsupp.total_apply, Finsupp.sum_fintype, b.equiv_fun_apply]
#align basis.sum_equiv_fun Basis.sum_equivFun

/- warning: basis.sum_repr -> Basis.sum_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.sum_repr Basis.sum_reprₓ'. -/
theorem Basis.sum_repr (u : M) : (∑ i, b.repr u i • b i) = u :=
  b.sum_equivFun u
#align basis.sum_repr Basis.sum_repr

/- warning: basis.equiv_fun_self -> Basis.equivFun_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv_fun_self Basis.equivFun_selfₓ'. -/
@[simp]
theorem Basis.equivFun_self [DecidableEq ι] (i j : ι) :
    b.equivFun (b i) j = if i = j then 1 else 0 := by rw [b.equiv_fun_apply, b.repr_self_apply]
#align basis.equiv_fun_self Basis.equivFun_self

/- warning: basis.repr_sum_self -> Basis.repr_sum_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_sum_self Basis.repr_sum_selfₓ'. -/
theorem Basis.repr_sum_self (c : ι → R) : ⇑(b.repr (∑ i, c i • b i)) = c :=
  by
  ext j
  simp only [map_sum, LinearEquiv.map_smul, repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finset.sum_apply']
  rw [Finset.sum_eq_single j, Finsupp.single_eq_same]
  · rintro i - hi
    exact Finsupp.single_eq_of_ne hi
  · intros
    have := Finset.mem_univ j
    contradiction
#align basis.repr_sum_self Basis.repr_sum_self

#print Basis.ofEquivFun /-
/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
def Basis.ofEquivFun (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  Basis.ofRepr <| e.trans <| LinearEquiv.symm <| Finsupp.linearEquivFunOnFinite R R ι
#align basis.of_equiv_fun Basis.ofEquivFun
-/

/- warning: basis.of_equiv_fun_repr_apply -> Basis.ofEquivFun_repr_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.of_equiv_fun_repr_apply Basis.ofEquivFun_repr_applyₓ'. -/
@[simp]
theorem Basis.ofEquivFun_repr_apply (e : M ≃ₗ[R] ι → R) (x : M) (i : ι) :
    (Basis.ofEquivFun e).repr x i = e x i :=
  rfl
#align basis.of_equiv_fun_repr_apply Basis.ofEquivFun_repr_apply

/- warning: basis.coe_of_equiv_fun -> Basis.coe_ofEquivFun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_of_equiv_fun Basis.coe_ofEquivFunₓ'. -/
@[simp]
theorem Basis.coe_ofEquivFun [DecidableEq ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e : ι → M) = fun i => e.symm (Function.update 0 i 1) :=
  funext fun i =>
    e.Injective <|
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single, Finsupp.single_eq_update]
#align basis.coe_of_equiv_fun Basis.coe_ofEquivFun

/- warning: basis.of_equiv_fun_equiv_fun -> Basis.ofEquivFun_equivFun is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] [_inst_6 : Fintype.{u1} ι] (v : Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3), Eq.{max (succ u1) (succ u2) (succ u3)} (Basis.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3) (Basis.ofEquivFun.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 _inst_6 (Basis.equivFun.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 _inst_6 v)) v
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u1} M] [_inst_3 : Module.{u2, u1} R M _inst_1 _inst_2] [_inst_6 : Fintype.{u3} ι] (v : Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Basis.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3) (Basis.ofEquivFun.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3 _inst_6 (Basis.equivFun.{u3, u2, u1} ι R M _inst_1 _inst_2 _inst_3 _inst_6 v)) v
Case conversion may be inaccurate. Consider using '#align basis.of_equiv_fun_equiv_fun Basis.ofEquivFun_equivFunₓ'. -/
@[simp]
theorem Basis.ofEquivFun_equivFun (v : Basis ι R M) : Basis.ofEquivFun v.equivFun = v := by
  classical
    ext j
    simp only [Basis.equivFun_symm_apply, Basis.coe_ofEquivFun]
    simp_rw [Function.update_apply, ite_smul]
    simp only [Finset.mem_univ, if_true, Pi.zero_apply, one_smul, Finset.sum_ite_eq', zero_smul]
#align basis.of_equiv_fun_equiv_fun Basis.ofEquivFun_equivFun

/- warning: basis.equiv_fun_of_equiv_fun -> Basis.equivFun_ofEquivFun is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : Module.{u2, u3} R M _inst_1 _inst_2] [_inst_6 : Fintype.{u1} ι] (e : LinearEquiv.{u2, u2, u3, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) M (ι -> R) _inst_2 (Pi.addCommMonoid.{u1, u2} ι (fun (ᾰ : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3 (Pi.Function.module.{u1, u2, u2} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Semiring.toModule.{u2} R _inst_1))), Eq.{max (succ u3) (succ (max u1 u2))} (LinearEquiv.{u2, u2, u3, max u1 u2} R R _inst_1 _inst_1 (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)) (RingHomInvPair.ids.{u2} R _inst_1) (RingHomInvPair.ids.{u2} R _inst_1) M (ι -> R) _inst_2 (Pi.addCommMonoid.{u1, u2} ι (fun (ᾰ : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1)))) _inst_3 (Pi.Function.module.{u1, u2, u2} ι R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) (Semiring.toModule.{u2} R _inst_1))) (Basis.equivFun.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 _inst_6 (Basis.ofEquivFun.{u1, u2, u3} ι R M _inst_1 _inst_2 _inst_3 _inst_6 e)) e
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} [_inst_1 : Semiring.{u3} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : Module.{u3, u2} R M _inst_1 _inst_2] [_inst_6 : Fintype.{u1} ι] (e : LinearEquiv.{u3, u3, u2, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) M (ι -> R) _inst_2 (Pi.addCommMonoid.{u1, u3} ι (fun (ᾰ : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) _inst_3 (Pi.module.{u1, u3, u3} ι (fun (a._@.Mathlib.LinearAlgebra.Basis._hyg.12306 : ι) => R) R _inst_1 (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : ι) => Semiring.toModule.{u3} R _inst_1))), Eq.{max (max (succ u1) (succ u3)) (succ u2)} (LinearEquiv.{u3, u3, u2, max u1 u3} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) M (ι -> R) _inst_2 (Pi.addCommMonoid.{u1, u3} ι (fun (ᾰ : ι) => R) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) _inst_3 (Pi.module.{u1, u3, u3} ι (fun (a._@.Mathlib.LinearAlgebra.Basis._hyg.11185 : ι) => R) R _inst_1 (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : ι) => Semiring.toModule.{u3} R _inst_1))) (Basis.equivFun.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3 _inst_6 (Basis.ofEquivFun.{u1, u3, u2} ι R M _inst_1 _inst_2 _inst_3 _inst_6 e)) e
Case conversion may be inaccurate. Consider using '#align basis.equiv_fun_of_equiv_fun Basis.equivFun_ofEquivFunₓ'. -/
@[simp]
theorem Basis.equivFun_ofEquivFun (e : M ≃ₗ[R] ι → R) : (Basis.ofEquivFun e).equivFun = e :=
  by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]
#align basis.equiv_fun_of_equiv_fun Basis.equivFun_ofEquivFun

variable (S : Type _) [Semiring S] [Module S M']

variable [SMulCommClass R S M']

/- warning: basis.constr_apply_fintype -> Basis.constr_apply_fintype is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.constr_apply_fintype Basis.constr_apply_fintypeₓ'. -/
@[simp]
theorem Basis.constr_apply_fintype (f : ι → M') (x : M) :
    (b.constr S f : M → M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equiv_fun_apply, Finsupp.sum_fintype]
#align basis.constr_apply_fintype Basis.constr_apply_fintype

/- warning: basis.mem_submodule_iff' -> Basis.mem_submodule_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mem_submodule_iff' Basis.mem_submodule_iff'ₓ'. -/
/-- If the submodule `P` has a finite basis,
`x ∈ P` iff it is a linear combination of basis vectors. -/
theorem Basis.mem_submodule_iff' {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • b i :=
  b.mem_submodule_iff.trans <|
    Finsupp.equivFunOnFinite.exists_congr_left.trans <|
      exists_congr fun c => by simp [Finsupp.sum_fintype]
#align basis.mem_submodule_iff' Basis.mem_submodule_iff'

/- warning: basis.coord_equiv_fun_symm -> Basis.coord_equivFun_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coord_equiv_fun_symm Basis.coord_equivFun_symmₓ'. -/
theorem Basis.coord_equivFun_symm (i : ι) (f : ι → R) : b.Coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)
#align basis.coord_equiv_fun_symm Basis.coord_equivFun_symm

end Fintype

end Module

section CommSemiring

namespace Basis

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M) (b' : Basis ι' R M')

#print Basis.equiv' /-
/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
    (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { b.constr R (f ∘ b) with
    invFun := b'.constr R (g ∘ b')
    left_inv :=
      have : (b'.constr R (g ∘ b')).comp (b.constr R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ← hi', b'.constr_basis,
              Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_arg (fun h : M →ₗ[R] M => h x) this
    right_inv :=
      have : (b.constr R (f ∘ b)).comp (b'.constr R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ← hi', b.constr_basis,
              Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_arg (fun h : M' →ₗ[R] M' => h x) this }
#align basis.equiv' Basis.equiv'
-/

/- warning: basis.equiv'_apply -> Basis.equiv'_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv'_apply Basis.equiv'_applyₓ'. -/
@[simp]
theorem equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _
#align basis.equiv'_apply Basis.equiv'_apply

/- warning: basis.equiv'_symm_apply -> Basis.equiv'_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.equiv'_symm_apply Basis.equiv'_symm_applyₓ'. -/
@[simp]
theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _
#align basis.equiv'_symm_apply Basis.equiv'_symm_apply

/- warning: basis.sum_repr_mul_repr -> Basis.sum_repr_mul_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.sum_repr_mul_repr Basis.sum_repr_mul_reprₓ'. -/
theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i :=
  by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [LinearEquiv.map_sum, LinearEquiv.map_smul, Finset.sum_apply']
  refine' Finset.sum_congr rfl fun j _ => _
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]
#align basis.sum_repr_mul_repr Basis.sum_repr_mul_repr

end Basis

end CommSemiring

section Module

open LinearMap

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']

variable [Module R M] [Module R₂ M] [Module R M'] [Module R M'']

variable {c d : R} {x y : M}

variable (b : Basis ι R M)

namespace Basis

/- warning: basis.maximal -> Basis.maximal is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_10 : Nontrivial.{u2} R] (b : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6), LinearIndependent.Maximal.{u2, u3, u1} ι R (Ring.toSemiring.{u2} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) b) (Basis.linearIndependent.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 b)
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Ring.{u3} R] [_inst_3 : AddCommGroup.{u1} M] [_inst_6 : Module.{u3, u1} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3)] [_inst_10 : Nontrivial.{u3} R] (b : Basis.{u2, u3, u1} ι R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6), LinearIndependent.Maximal.{u3, u1, u2} ι R (Ring.toSemiring.{u3} R _inst_1) M (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6 (FunLike.coe.{max (max (succ u2) (succ u3)) (succ u1), succ u2, succ u1} (Basis.{u2, u3, u1} ι R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u2, u3, u1} ι R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) b) (Basis.linearIndependent.{u1, u3, u2} ι R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6 b)
Case conversion may be inaccurate. Consider using '#align basis.maximal Basis.maximalₓ'. -/
/-- Any basis is a maximal linear independent set.
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.LinearIndependent.Maximal := fun w hi h =>
  by
  -- If `range w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ range w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.total_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  have r : ∀ i, b i = u i := fun i => rfl
  simp_rw [Finsupp.total_apply, r] at e
  change
    ((b.repr x).Sum fun (i : ι) (a : R) => (fun (x : w) (r : R) => r • (x : M)) (u i) a) =
      ((⟨x, p⟩ : w) : M) at
    e
  rw [← Finsupp.sum_embDomain, ← Finsupp.total_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine' hi.total_ne_of_not_mem_support _ _ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [embedding.coe_fn_mk, Subtype.mk_eq_mk, ← r] at W
  apply q ⟨j, W⟩
#align basis.maximal Basis.maximal

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

/- warning: basis.mk -> Basis.mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} {v : ι -> M} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)], (LinearIndependent.{u1, u2, u3} ι R M v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) -> (LE.le.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Preorder.toHasLe.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (SetLike.partialOrder.{u3, u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) M (Submodule.setLike.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.hasTop.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v))) -> (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} {v : ι -> M} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)], (LinearIndependent.{u1, u2, u3} ι R M v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) -> (LE.le.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Preorder.toLE.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.completeLattice.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.instTopSubmodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v))) -> (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)
Case conversion may be inaccurate. Consider using '#align basis.mk Basis.mkₓ'. -/
/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : Basis ι R M :=
  Basis.ofRepr
    {
      hli.repr.comp
        (LinearMap.id.codRestrict _ fun h =>
          hsp Submodule.mem_top) with
      invFun := Finsupp.total _ _ _ v
      left_inv := fun x => hli.total_repr ⟨x, _⟩
      right_inv := fun x => hli.repr_eq rfl }
#align basis.mk Basis.mk

/- warning: basis.mk_repr -> Basis.mk_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mk_repr Basis.mk_reprₓ'. -/
@[simp]
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl
#align basis.mk_repr Basis.mk_repr

/- warning: basis.mk_apply -> Basis.mk_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} {v : ι -> M} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] (hli : LinearIndependent.{u1, u2, u3} ι R M v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (hsp : LE.le.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Preorder.toHasLe.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (SetLike.partialOrder.{u3, u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) M (Submodule.setLike.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.hasTop.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v))) (i : ι), Eq.{succ u3} M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Basis.mk.{u1, u2, u3} ι R M v _inst_1 _inst_3 _inst_6 hli hsp) i) (v i)
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} {M : Type.{u3}} {v : ι -> M} [_inst_1 : Ring.{u1} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] (hli : LinearIndependent.{u2, u1, u3} ι R M v (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (hsp : LE.le.{u3} (Submodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Preorder.toLE.{u3} (Submodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u3} (Submodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (OmegaCompletePartialOrder.toPartialOrder.{u3} (Submodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (CompleteLattice.instOmegaCompletePartialOrder.{u3} (Submodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.completeLattice.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))))) (Top.top.{u3} (Submodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.instTopSubmodule.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Submodule.span.{u1, u3} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u2} M ι v))) (i : ι), Eq.{succ u3} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), succ u2, succ u3} (Basis.{u2, u1, u3} ι R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u2, u1, u3} ι R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Basis.mk.{u2, u1, u3} ι R M v _inst_1 _inst_3 _inst_6 hli hsp) i) (v i)
Case conversion may be inaccurate. Consider using '#align basis.mk_apply Basis.mk_applyₓ'. -/
theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.total _ _ _ v _ = v i by simp
#align basis.mk_apply Basis.mk_apply

/- warning: basis.coe_mk -> Basis.coe_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} {v : ι -> M} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] (hli : LinearIndependent.{u1, u2, u3} ι R M v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (hsp : LE.le.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Preorder.toHasLe.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (SetLike.partialOrder.{u3, u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) M (Submodule.setLike.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.hasTop.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v))), Eq.{max (succ u1) (succ u3)} (ι -> M) (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Basis.mk.{u1, u2, u3} ι R M v _inst_1 _inst_3 _inst_6 hli hsp)) v
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u1}} {M : Type.{u2}} {v : ι -> M} [_inst_1 : Ring.{u1} R] [_inst_3 : AddCommGroup.{u2} M] [_inst_6 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] (hli : LinearIndependent.{u3, u1, u2} ι R M v (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (hsp : LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Submodule.completeLattice.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6))))) (Top.top.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Submodule.instTopSubmodule.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6)) (Submodule.span.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6 (Set.range.{u2, succ u3} M ι v))), Eq.{max (succ u3) (succ u2)} (forall (a : ι), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) a) (FunLike.coe.{max (max (succ u3) (succ u1)) (succ u2), succ u3, succ u2} (Basis.{u3, u1, u2} ι R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u1, u2} ι R M (Ring.toSemiring.{u1} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Basis.mk.{u3, u1, u2} ι R M v _inst_1 _inst_3 _inst_6 hli hsp)) v
Case conversion may be inaccurate. Consider using '#align basis.coe_mk Basis.coe_mkₓ'. -/
@[simp]
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)
#align basis.coe_mk Basis.coe_mk

variable {hli hsp}

/- warning: basis.mk_coord_apply_eq -> Basis.mk_coord_apply_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} {v : ι -> M} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] {hli : LinearIndependent.{u1, u2, u3} ι R M v (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6} {hsp : LE.le.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Preorder.toHasLe.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (SetLike.partialOrder.{u3, u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) M (Submodule.setLike.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.hasTop.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v))} (i : ι), Eq.{succ u2} R (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M R (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) _inst_6 (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (fun (_x : LinearMap.{u2, u2, u3, u2} R R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1))) M R (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) _inst_6 (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R _inst_1))) => M -> R) (LinearMap.hasCoeToFun.{u2, u2, u3, u2} R R M R (Ring.toSemiring.{u2} R _inst_1) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) _inst_6 (Semiring.toModule.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (RingHom.id.{u2} R (Semiring.toNonAssocSemiring.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (Basis.coord.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Basis.mk.{u1, u2, u3} ι R M v _inst_1 _inst_3 _inst_6 hli hsp) i) (v i)) (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R _inst_1)))))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {M : Type.{u2}} {v : ι -> M} [_inst_1 : Ring.{u3} R] [_inst_3 : AddCommGroup.{u2} M] [_inst_6 : Module.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3)] {hli : LinearIndependent.{u1, u3, u2} ι R M v (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6} {hsp : LE.le.{u2} (Submodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Preorder.toLE.{u2} (Submodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (PartialOrder.toPreorder.{u2} (Submodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Submodule.completeLattice.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6))))) (Top.top.{u2} (Submodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6) (Submodule.instTopSubmodule.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6)) (Submodule.span.{u3, u2} R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6 (Set.range.{u2, succ u1} M ι v))} (i : ι), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (v i)) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (LinearMap.{u3, u3, u2, u3} R R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_1))) M R (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_1)))) _inst_6 (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R _inst_1))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, u2, u3} R R M R (Ring.toSemiring.{u3} R _inst_1) (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_1)))) _inst_6 (Semiring.toModule.{u3} R (Ring.toSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R (Ring.toSemiring.{u3} R _inst_1)))) (Basis.coord.{u1, u3, u2} ι R M (Ring.toSemiring.{u3} R _inst_1) (AddCommGroup.toAddCommMonoid.{u2} M _inst_3) _inst_6 (Basis.mk.{u1, u3, u2} ι R M v _inst_1 _inst_3 _inst_6 hli hsp) i) (v i)) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (v i)) 1 (One.toOfNat1.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (v i)) (Semiring.toOne.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (v i)) (Ring.toSemiring.{u3} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : M) => R) (v i)) _inst_1))))
Case conversion may be inaccurate. Consider using '#align basis.mk_coord_apply_eq Basis.mk_coord_apply_eqₓ'. -/
/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).Coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]
#align basis.mk_coord_apply_eq Basis.mk_coord_apply_eq

/- warning: basis.mk_coord_apply_ne -> Basis.mk_coord_apply_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mk_coord_apply_ne Basis.mk_coord_apply_neₓ'. -/
/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).Coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]
#align basis.mk_coord_apply_ne Basis.mk_coord_apply_ne

/- warning: basis.mk_coord_apply -> Basis.mk_coord_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mk_coord_apply Basis.mk_coord_applyₓ'. -/
/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Basis.mk hli hsp).Coord i (v j) = if j = i then 1 else 0 :=
  by
  cases eq_or_ne j i
  · simp only [h, if_true, eq_self_iff_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]
#align basis.mk_coord_apply Basis.mk_coord_apply

end Mk

section Span

variable (hli : LinearIndependent R v)

#print Basis.span /-
/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : Basis ι R (span R (range v)) :=
  Basis.mk (linearIndependent_span hli) <| by
    intro x _
    have h₁ : ((coe : span R (range v) → M) '' Set.range fun i => Subtype.mk (v i) _) = range v :=
      by
      rw [← Set.range_comp]
      rfl
    have h₂ :
      map (Submodule.subtype (span R (range v))) (span R (Set.range fun i => Subtype.mk (v i) _)) =
        span R (range v) :=
      by rw [← span_image, Submodule.coeSubtype, h₁]
    have h₃ :
      (x : M) ∈
        map (Submodule.subtype (span R (range v)))
          (span R (Set.range fun i => Subtype.mk (v i) _)) :=
      by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]
#align basis.span Basis.span
-/

#print Basis.span_apply /-
protected theorem span_apply (i : ι) : (Basis.span hli i : M) = v i :=
  congr_arg (coe : span R (range v) → M) <| Basis.mk_apply (linearIndependent_span hli) _ i
#align basis.span_apply Basis.span_apply
-/

end Span

/- warning: basis.group_smul_span_eq_top -> Basis.groupSmul_span_eq_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.group_smul_span_eq_top Basis.groupSmul_span_eq_topₓ'. -/
theorem groupSmul_span_eq_top {G : Type _} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj⊢
  refine' fun p hp => hj p fun u hu => _
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • 1 : R) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • 1 : R) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this
#align basis.group_smul_span_eq_top Basis.groupSmul_span_eq_top

/- warning: basis.group_smul -> Basis.groupSmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.group_smul Basis.groupSmulₓ'. -/
/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`group_smul` provides the basis corresponding to `w • v`. -/
def groupSmul {G : Type _} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  @Basis.mk ι R M (w • v) _ _ _ (v.LinearIndependent.group_smul w)
    (groupSmul_span_eq_top v.span_eq).ge
#align basis.group_smul Basis.groupSmul

/- warning: basis.group_smul_apply -> Basis.groupSmul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.group_smul_apply Basis.groupSmul_applyₓ'. -/
theorem groupSmul_apply {G : Type _} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) :
    v.group_smul w i = (w • v : ι → M) i :=
  mk_apply (v.LinearIndependent.group_smul w) (groupSmul_span_eq_top v.span_eq).ge i
#align basis.group_smul_apply Basis.groupSmul_apply

/- warning: basis.units_smul_span_eq_top -> Basis.units_smul_span_eq_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] {v : ι -> M}, (Eq.{succ u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v)) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.hasTop.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))) -> (forall {w : ι -> (Units.{u2} R (Ring.toMonoid.{u2} R _inst_1))}, Eq.{succ u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι (SMul.smul.{max u1 u2, max u1 u3} (ι -> (Units.{u2} R (Ring.toMonoid.{u2} R _inst_1))) (ι -> M) (Pi.smul'.{u1, u2, u3} ι (fun (ᾰ : ι) => Units.{u2} R (Ring.toMonoid.{u2} R _inst_1)) (fun (ᾰ : ι) => M) (fun (i : ι) => Units.hasSmul.{u2, u3} R M (Ring.toMonoid.{u2} R _inst_1) (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))))) w v))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.hasTop.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] {v : ι -> M}, (Eq.{succ u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι v)) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.instTopSubmodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))) -> (forall {w : ι -> (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))}, Eq.{succ u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.span.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6 (Set.range.{u3, succ u1} M ι (HSMul.hSMul.{max u1 u2, max u1 u3, max u1 u3} (ι -> (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (ι -> M) (ι -> M) (instHSMul.{max u1 u2, max u1 u3} (ι -> (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (ι -> M) (Pi.smul'.{u1, u2, u3} ι (fun (a._@.Mathlib.LinearAlgebra.Basis._hyg.16114 : ι) => Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) (fun (a._@.Mathlib.LinearAlgebra.Basis._hyg.16100 : ι) => M) (fun (i : ι) => Units.instSMulUnits.{u2, u3} R M (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (SMulZeroClass.toSMul.{u2, u3} R M (NegZeroClass.toZero.{u3} M (SubNegZeroMonoid.toNegZeroClass.{u3} M (SubtractionMonoid.toSubNegZeroMonoid.{u3} M (SubtractionCommMonoid.toSubtractionMonoid.{u3} M (AddCommGroup.toDivisionAddCommMonoid.{u3} M _inst_3))))) (SMulWithZero.toSMulZeroClass.{u2, u3} R M (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u3} M (SubNegZeroMonoid.toNegZeroClass.{u3} M (SubtractionMonoid.toSubNegZeroMonoid.{u3} M (SubtractionCommMonoid.toSubtractionMonoid.{u3} M (AddCommGroup.toDivisionAddCommMonoid.{u3} M _inst_3))))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u3} M (SubNegZeroMonoid.toNegZeroClass.{u3} M (SubtractionMonoid.toSubNegZeroMonoid.{u3} M (SubtractionCommMonoid.toSubtractionMonoid.{u3} M (AddCommGroup.toDivisionAddCommMonoid.{u3} M _inst_3))))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))))))) w v))) (Top.top.{u3} (Submodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (Submodule.instTopSubmodule.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))
Case conversion may be inaccurate. Consider using '#align basis.units_smul_span_eq_top Basis.units_smul_span_eq_topₓ'. -/
theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  groupSmul_span_eq_top hv
#align basis.units_smul_span_eq_top Basis.units_smul_span_eq_top

/- warning: basis.units_smul -> Basis.unitsSMul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)], (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) -> (ι -> (Units.{u2} R (Ring.toMonoid.{u2} R _inst_1))) -> (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)], (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) -> (ι -> (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) -> (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)
Case conversion may be inaccurate. Consider using '#align basis.units_smul Basis.unitsSMulₓ'. -/
/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `smul_of_is_unit`
provides the basis corresponding to `w • v`. -/
def unitsSMul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  @Basis.mk ι R M (w • v) _ _ _ (v.LinearIndependent.units_smul w)
    (units_smul_span_eq_top v.span_eq).ge
#align basis.units_smul Basis.unitsSMul

/- warning: basis.units_smul_apply -> Basis.unitsSMul_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] {v : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6} {w : ι -> (Units.{u2} R (Ring.toMonoid.{u2} R _inst_1))} (i : ι), Eq.{succ u3} M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Basis.unitsSMul.{u1, u2, u3} ι R M _inst_1 _inst_3 _inst_6 v w) i) (SMul.smul.{u2, u3} (Units.{u2} R (Ring.toMonoid.{u2} R _inst_1)) M (Units.hasSmul.{u2, u3} R M (Ring.toMonoid.{u2} R _inst_1) (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))))) (w i) (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) v i))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u1} M] [_inst_6 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3)] {v : Basis.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6} {w : ι -> (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))} (i : ι), Eq.{succ u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) (Basis.unitsSMul.{u3, u2, u1} ι R M _inst_1 _inst_3 _inst_6 v w) i) (HSMul.hSMul.{u2, u1, u1} (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (instHSMul.{u2, u1} (Units.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)))) ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (Units.instSMulUnits.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (SMulZeroClass.toSMul.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (NegZeroClass.toZero.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubNegZeroMonoid.toNegZeroClass.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionMonoid.toSubNegZeroMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionCommMonoid.toSubtractionMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommGroup.toDivisionAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubNegZeroMonoid.toNegZeroClass.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionMonoid.toSubNegZeroMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionCommMonoid.toSubtractionMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommGroup.toDivisionAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubNegZeroMonoid.toNegZeroClass.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionMonoid.toSubNegZeroMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionCommMonoid.toSubtractionMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommGroup.toDivisionAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3))))) (Module.toMulActionWithZero.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3) _inst_6)))))) (w i) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) v i))
Case conversion may be inaccurate. Consider using '#align basis.units_smul_apply Basis.unitsSMul_applyₓ'. -/
theorem unitsSMul_apply {v : Basis ι R M} {w : ι → Rˣ} (i : ι) : v.units_smul w i = w i • v i :=
  mk_apply (v.LinearIndependent.units_smul w) (units_smul_span_eq_top v.span_eq).ge i
#align basis.units_smul_apply Basis.unitsSMul_apply

/- warning: basis.coord_units_smul -> Basis.coord_unitsSMul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coord_units_smul Basis.coord_unitsSMulₓ'. -/
@[simp]
theorem coord_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (e.units_smul w).Coord i = (w i)⁻¹ • e.Coord i := by
  classical
    apply e.ext
    intro j
    trans ((e.units_smul w).Coord i) ((w j)⁻¹ • (e.units_smul w) j)
    · congr
      simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      SMulHomClass.map_smul, Finsupp.single_apply]
    split_ifs with h h
    · simp [h]
    · simp
#align basis.coord_units_smul Basis.coord_unitsSMul

/- warning: basis.repr_units_smul -> Basis.repr_unitsSMul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.repr_units_smul Basis.repr_unitsSMulₓ'. -/
@[simp]
theorem repr_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.units_smul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)
#align basis.repr_units_smul Basis.repr_unitsSMul

/- warning: basis.is_unit_smul -> Basis.isUnitSMul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)], (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) -> (forall {w : ι -> R}, (forall (i : ι), IsUnit.{u2} R (Ring.toMonoid.{u2} R _inst_1) (w i)) -> (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)], (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) -> (forall {w : ι -> R}, (forall (i : ι), IsUnit.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (w i)) -> (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6))
Case conversion may be inaccurate. Consider using '#align basis.is_unit_smul Basis.isUnitSMulₓ'. -/
/-- A version of `smul_of_units` that uses `is_unit`. -/
def isUnitSMul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).Unit
#align basis.is_unit_smul Basis.isUnitSMul

/- warning: basis.is_unit_smul_apply -> Basis.isUnitSMul_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u3} M] [_inst_6 : Module.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] {v : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6} {w : ι -> R} (hw : forall (i : ι), IsUnit.{u2} R (Ring.toMonoid.{u2} R _inst_1) (w i)) (i : ι), Eq.{succ u3} M (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) (Basis.isUnitSMul.{u1, u2, u3} ι R M _inst_1 _inst_3 _inst_6 v (fun (i : ι) => w i) hw) i) (SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)))) (Module.toMulActionWithZero.{u2, u3} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)))) (w i) (coeFn.{max (succ u1) (succ u2) (succ u3), max (succ u1) (succ u3)} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) (fun (_x : Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) => ι -> M) (FunLike.hasCoeToFun.{max (succ u1) (succ u2) (succ u3), succ u1, succ u3} (Basis.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6) ι (fun (_x : ι) => M) (Basis.funLike.{u1, u2, u3} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3) _inst_6)) v i))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : Ring.{u2} R] [_inst_3 : AddCommGroup.{u1} M] [_inst_6 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3)] {v : Basis.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6} {w : ι -> R} (hw : forall (i : ι), IsUnit.{u2} R (MonoidWithZero.toMonoid.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (w i)) (i : ι), Eq.{succ u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) (Basis.isUnitSMul.{u3, u2, u1} ι R M _inst_1 _inst_3 _inst_6 v (fun (i : ι) => w i) hw) i) (HSMul.hSMul.{u2, u1, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (instHSMul.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SMulZeroClass.toSMul.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (NegZeroClass.toZero.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubNegZeroMonoid.toNegZeroClass.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionMonoid.toSubNegZeroMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionCommMonoid.toSubtractionMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommGroup.toDivisionAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3))))) (SMulWithZero.toSMulZeroClass.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (MonoidWithZero.toZero.{u2} R (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1))) (NegZeroClass.toZero.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubNegZeroMonoid.toNegZeroClass.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionMonoid.toSubNegZeroMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionCommMonoid.toSubtractionMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommGroup.toDivisionAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3))))) (MulActionWithZero.toSMulWithZero.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (Semiring.toMonoidWithZero.{u2} R (Ring.toSemiring.{u2} R _inst_1)) (NegZeroClass.toZero.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubNegZeroMonoid.toNegZeroClass.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionMonoid.toSubNegZeroMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (SubtractionCommMonoid.toSubtractionMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (AddCommGroup.toDivisionAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3))))) (Module.toMulActionWithZero.{u2, u1} R ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) i) _inst_3) _inst_6))))) (w i) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u3, succ u1} (Basis.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => M) _x) (Basis.funLike.{u3, u2, u1} ι R M (Ring.toSemiring.{u2} R _inst_1) (AddCommGroup.toAddCommMonoid.{u1} M _inst_3) _inst_6) v i))
Case conversion may be inaccurate. Consider using '#align basis.is_unit_smul_apply Basis.isUnitSMul_applyₓ'. -/
theorem isUnitSMul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i :=
  unitsSMul_apply i
#align basis.is_unit_smul_apply Basis.isUnitSMul_apply

section Fin

/- warning: basis.mk_fin_cons -> Basis.mkFinCons is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mk_fin_cons Basis.mkFinConsₓ'. -/
/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : Submodule.span R (Set.range (N.Subtype ∘ b)) = N := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  @Basis.mk _ _ _ (Fin.cons y (N.Subtype ∘ b) : Fin (n + 1) → M) _ _ _
    ((b.LinearIndependent.map' N.Subtype (Submodule.ker_subtype _)).fin_cons' _ _ <|
      by
      rintro c ⟨x, hx⟩ hc
      rw [span_b] at hx
      exact hli c x hx hc)
    fun x _ => by
    rw [Fin.range_cons, Submodule.mem_span_insert', span_b]
    exact hsp x
#align basis.mk_fin_cons Basis.mkFinCons

/- warning: basis.coe_mk_fin_cons -> Basis.coe_mkFinCons is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_mk_fin_cons Basis.coe_mkFinConsₓ'. -/
@[simp]
theorem coe_mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y (coe ∘ b) :=
  coe_mk _ _
#align basis.coe_mk_fin_cons Basis.coe_mkFinCons

/- warning: basis.mk_fin_cons_of_le -> Basis.mkFinConsOfLe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mk_fin_cons_of_le Basis.mkFinConsOfLeₓ'. -/
/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `fin.cons y b`. -/
noncomputable def mkFinConsOfLe {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg coe hx)) fun z => hsp z z.2
#align basis.mk_fin_cons_of_le Basis.mkFinConsOfLe

/- warning: basis.coe_mk_fin_cons_of_le -> Basis.coe_mkFinConsOfLe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_mk_fin_cons_of_le Basis.coe_mkFinConsOfLeₓ'. -/
@[simp]
theorem coe_mkFinConsOfLe {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinConsOfLe y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.ofLe hNO ∘ b) :=
  coe_mkFinCons _ _ _ _
#align basis.coe_mk_fin_cons_of_le Basis.coe_mkFinConsOfLe

/- warning: basis.fin_two_prod -> Basis.finTwoProd is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_10 : Semiring.{u1} R], Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))
but is expected to have type
  forall (R : Type.{u1}) [_inst_10 : Semiring.{u1} R], Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Prod.{u1, u1} R R) _inst_10 (Prod.instAddCommMonoidSum.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))
Case conversion may be inaccurate. Consider using '#align basis.fin_two_prod Basis.finTwoProdₓ'. -/
/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
protected def finTwoProd (R : Type _) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm
#align basis.fin_two_prod Basis.finTwoProd

/- warning: basis.fin_two_prod_zero -> Basis.finTwoProd_zero is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_10 : Semiring.{u1} R], Eq.{succ u1} (Prod.{u1, u1} R R) (coeFn.{succ u1, succ u1} (Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (fun (_x : Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) => (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Prod.{u1, u1} R R)) (FunLike.hasCoeToFun.{succ u1, 1, succ u1} (Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (_x : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Prod.{u1, u1} R R) (Basis.funLike.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10)))) (Basis.finTwoProd.{u1} R _inst_10) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (Prod.mk.{u1, u1} R R (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))))))) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_10 : Semiring.{u1} R], Eq.{succ u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Prod.{u1, u1} R R) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (FunLike.coe.{succ u1, 1, succ u1} (Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Prod.{u1, u1} R R) _inst_10 (Prod.instAddCommMonoidSum.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (_x : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Prod.{u1, u1} R R) _x) (Basis.funLike.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Prod.{u1, u1} R R) _inst_10 (Prod.instAddCommMonoidSum.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (Basis.finTwoProd.{u1} R _inst_10) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Prod.mk.{u1, u1} R R (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_10))) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_10)))))
Case conversion may be inaccurate. Consider using '#align basis.fin_two_prod_zero Basis.finTwoProd_zeroₓ'. -/
@[simp]
theorem finTwoProd_zero (R : Type _) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd]
#align basis.fin_two_prod_zero Basis.finTwoProd_zero

/- warning: basis.fin_two_prod_one -> Basis.finTwoProd_one is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_10 : Semiring.{u1} R], Eq.{succ u1} (Prod.{u1, u1} R R) (coeFn.{succ u1, succ u1} (Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (fun (_x : Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) => (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (Prod.{u1, u1} R R)) (FunLike.hasCoeToFun.{succ u1, 1, succ u1} (Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (_x : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => Prod.{u1, u1} R R) (Basis.funLike.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) R (Prod.{u1, u1} R R) _inst_10 (Prod.addCommMonoid.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10)))) (Basis.finTwoProd.{u1} R _inst_10) (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) (CharZero.NeZero.two.{0} Nat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} Nat (NonAssocSemiring.toAddCommMonoidWithOne.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (StrictOrderedSemiring.to_charZero.{0} Nat Nat.strictOrderedSemiring))))))) (Prod.mk.{u1, u1} R R (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))))))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))))))))
but is expected to have type
  forall (R : Type.{u1}) [_inst_10 : Semiring.{u1} R], Eq.{succ u1} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Prod.{u1, u1} R R) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (FunLike.coe.{succ u1, 1, succ u1} (Basis.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Prod.{u1, u1} R R) _inst_10 (Prod.instAddCommMonoidSum.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (_x : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => Prod.{u1, u1} R R) _x) (Basis.funLike.{0, u1, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) R (Prod.{u1, u1} R R) _inst_10 (Prod.instAddCommMonoidSum.{u1, u1} R R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10)))) (Prod.module.{u1, u1, u1} R R R _inst_10 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_10))) (Semiring.toModule.{u1} R _inst_10) (Semiring.toModule.{u1} R _inst_10))) (Basis.finTwoProd.{u1} R _inst_10) (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Prod.mk.{u1, u1} R R (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_10)))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R _inst_10))))
Case conversion may be inaccurate. Consider using '#align basis.fin_two_prod_one Basis.finTwoProd_oneₓ'. -/
@[simp]
theorem finTwoProd_one (R : Type _) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd]
#align basis.fin_two_prod_one Basis.finTwoProd_one

/- warning: basis.coe_fin_two_prod_repr -> Basis.coe_finTwoProd_repr is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_fin_two_prod_repr Basis.coe_finTwoProd_reprₓ'. -/
@[simp]
theorem coe_finTwoProd_repr {R : Type _} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl
#align basis.coe_fin_two_prod_repr Basis.coe_finTwoProd_repr

end Fin

end Basis

end Module

section Induction

variable [Ring R] [IsDomain R]

variable [AddCommGroup M] [Module R M] {b : ι → M}

/- warning: submodule.induction_on_rank_aux -> Submodule.inductionOnRankAux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.induction_on_rank_aux Submodule.inductionOnRankAuxₓ'. -/
/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M → Sort _)
    (ih :
      ∀ N : Submodule R M,
        (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (n : ℕ) (N : Submodule R M)
    (rank_le : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R (coe ∘ v : Fin m → M) → m ≤ n) :
    P N := by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N N_le x x_mem x_ortho
    exfalso
    simpa using x_ortho 1 0 N.zero_mem
  induction' n with n rank_ih generalizing N
  · suffices N = ⊥ by rwa [this]
    apply Basis.eq_bot_of_rank_eq_zero b _ fun m v hv => le_zero_iff.mp (rank_le v hv)
  apply ih
  intro N' N'_le x x_mem x_ortho
  apply rank_ih
  intro m v hli
  refine' nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) _)
  convert hli.fin_cons' x _ _
  · ext i
    refine' Fin.cases _ _ i <;> simp
  · intro c y hcy
    refine' x_ortho c y (submodule.span_le.mpr _ y.2) hcy
    rintro _ ⟨z, rfl⟩
    exact (v z).2
#align submodule.induction_on_rank_aux Submodule.inductionOnRankAux

end Induction

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

include K

open Submodule

namespace Basis

section ExistsBasis

#print Basis.extend /-
/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : LinearIndependent K (coe : s → V)) : Basis _ K V :=
  Basis.mk
    (@LinearIndependent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linearIndependent_extend _))
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))
#align basis.extend Basis.extend
-/

/- warning: basis.extend_apply_self -> Basis.extend_apply_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.extend_apply_self Basis.extend_apply_selfₓ'. -/
theorem extend_apply_self (hs : LinearIndependent K (coe : s → V)) (x : hs.extend _) :
    Basis.extend hs x = x :=
  Basis.mk_apply _ _ _
#align basis.extend_apply_self Basis.extend_apply_self

/- warning: basis.coe_extend -> Basis.coe_extend is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.coe_extend Basis.coe_extendₓ'. -/
@[simp]
theorem coe_extend (hs : LinearIndependent K (coe : s → V)) : ⇑(Basis.extend hs) = coe :=
  funext (extend_apply_self hs)
#align basis.coe_extend Basis.coe_extend

/- warning: basis.range_extend -> Basis.range_extend is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.range_extend Basis.range_extendₓ'. -/
theorem range_extend (hs : LinearIndependent K (coe : s → V)) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend, Subtype.range_coe_subtype, set_of_mem_eq]
#align basis.range_extend Basis.range_extend

/- warning: basis.sum_extend -> Basis.sumExtend is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u2}} {K : Type.{u3}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u3} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u3, u1} K V (Ring.toSemiring.{u3} K (DivisionRing.toRing.{u3} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {v : ι -> V} (hs : LinearIndependent.{u2, u3, u1} ι K V v (Ring.toSemiring.{u3} K (DivisionRing.toRing.{u3} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4), Basis.{max u2 u1, u3, u1} (Sum.{u2, u1} ι (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (SDiff.sdiff.{u1} (Set.{u1} V) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} V) (Set.booleanAlgebra.{u1} V)) (LinearIndependent.extend.{u1, u3} K V _inst_1 _inst_2 _inst_4 (Set.range.{u1, succ u2} V ι v) (Set.univ.{u1} V) (Basis.sumExtend._proof_1.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_4 v hs) (Basis.sumExtend._proof_2.{u1, u2} ι V v)) (Set.range.{u1, succ u2} V ι v)))) K V (Ring.toSemiring.{u3} K (DivisionRing.toRing.{u3} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4
but is expected to have type
  forall {ι : Type.{u2}} {K : Type.{u3}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u3} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u3, u1} K V (DivisionSemiring.toSemiring.{u3} K (DivisionRing.toDivisionSemiring.{u3} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {v : ι -> V} (hs : LinearIndependent.{u2, u3, u1} ι K V v (DivisionSemiring.toSemiring.{u3} K (DivisionRing.toDivisionSemiring.{u3} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4), Basis.{max u1 u2, u3, u1} (Sum.{u2, u1} ι (Set.Elem.{u1} V (Basis.sumExtendIndex.{u1, u2, u3} ι K V _inst_1 _inst_2 _inst_4 v hs))) K V (DivisionSemiring.toSemiring.{u3} K (DivisionRing.toDivisionSemiring.{u3} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4
Case conversion may be inaccurate. Consider using '#align basis.sum_extend Basis.sumExtendₓ'. -/
/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (Sum ι _) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.Injective
  let b := hs.to_subtype_range.extend (subset_univ (Set.range v))
  (Basis.extend hs.to_subtype_range).reindex <|
    Equiv.symm <|
      calc
        Sum ι (b \ s : Set V) ≃ Sum s (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· ∈ s)
          Equiv.Set.sumDiffSubset (hs.to_subtype_range.subset_extend _)
        
#align basis.sum_extend Basis.sumExtend

/- warning: basis.subset_extend -> Basis.subset_extend is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {s : Set.{u1} V} (hs : LinearIndependent.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) s) K V ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) s) V (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) s) V (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) s) V (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) s) V (coeSubtype.{succ u1} V (fun (x : V) => Membership.Mem.{u1, u1} V (Set.{u1} V) (Set.hasMem.{u1} V) x s)))))) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4), HasSubset.Subset.{u1} (Set.{u1} V) (Set.hasSubset.{u1} V) s (LinearIndependent.extend.{u1, u2} K V _inst_1 _inst_2 _inst_4 s (Set.univ.{u1} V) hs (Set.subset_univ.{u1} V s))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {s : Set.{u2} V} (hs : LinearIndependent.{u2, u1, u2} (Subtype.{succ u2} V (fun (x : V) => Membership.mem.{u2, u2} V (Set.{u2} V) (Set.instMembershipSet.{u2} V) x s)) K V (Subtype.val.{succ u2} V (fun (x : V) => Membership.mem.{u2, u2} V (Set.{u2} V) (Set.instMembershipSet.{u2} V) x s)) (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4), HasSubset.Subset.{u2} (Set.{u2} V) (Set.instHasSubsetSet.{u2} V) s (LinearIndependent.extend.{u2, u1} K V _inst_1 _inst_2 _inst_4 s (Set.univ.{u2} V) hs (Set.subset_univ.{u2} V s))
Case conversion may be inaccurate. Consider using '#align basis.subset_extend Basis.subset_extendₓ'. -/
theorem subset_extend {s : Set V} (hs : LinearIndependent K (coe : s → V)) :
    s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _
#align basis.subset_extend Basis.subset_extend

section

variable (K V)

#print Basis.ofVectorSpaceIndex /-
/-- A set used to index `basis.of_vector_space`. -/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linearIndependent_empty K V).extend (subset_univ _)
#align basis.of_vector_space_index Basis.ofVectorSpaceIndex
-/

#print Basis.ofVectorSpace /-
/-- Each vector space has a basis. -/
noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linearIndependent_empty K V)
#align basis.of_vector_space Basis.ofVectorSpace
-/

/- warning: basis.of_vector_space_apply_self -> Basis.ofVectorSpace_apply_self is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u2}) (V : Type.{u1}) [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)), Eq.{succ u1} V (coeFn.{max (succ u2) (succ u1), succ u1} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (fun (_x : Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) -> V) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u1} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) (fun (_x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) => V) (Basis.funLike.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4)) (Basis.ofVectorSpace.{u1, u2} K V _inst_1 _inst_2 _inst_4) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (coeSubtype.{succ u1} V (fun (x : V) => Membership.Mem.{u1, u1} V (Set.{u1} V) (Set.hasMem.{u1} V) x (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)))))) x)
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (x : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)), Eq.{succ u2} ((fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => V) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u2} (Basis.{u2, u1, u2} (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) (fun (_x : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => V) _x) (Basis.funLike.{u2, u1, u2} (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Basis.ofVectorSpace.{u2, u1} K V _inst_1 _inst_2 _inst_4) x) (Subtype.val.{succ u2} V (fun (x : V) => Membership.mem.{u2, u2} V (Set.{u2} V) (Set.instMembershipSet.{u2} V) x (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) x)
Case conversion may be inaccurate. Consider using '#align basis.of_vector_space_apply_self Basis.ofVectorSpace_apply_selfₓ'. -/
theorem ofVectorSpace_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V x = x :=
  Basis.mk_apply _ _ _
#align basis.of_vector_space_apply_self Basis.ofVectorSpace_apply_self

/- warning: basis.coe_of_vector_space -> Basis.coe_ofVectorSpace is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u2}) (V : Type.{u1}) [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)], Eq.{succ u1} ((coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) -> V) (coeFn.{max (succ u2) (succ u1), succ u1} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (fun (_x : Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) -> V) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u1} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) (fun (_x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) => V) (Basis.funLike.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4)) (Basis.ofVectorSpace.{u1, u2} K V _inst_1 _inst_2 _inst_4)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (coeSubtype.{succ u1} V (fun (x : V) => Membership.Mem.{u1, u1} V (Set.{u1} V) (Set.hasMem.{u1} V) x (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)))))))
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Eq.{succ u2} (forall (a : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => V) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u2} (Basis.{u2, u1, u2} (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) (fun (_x : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => V) _x) (Basis.funLike.{u2, u1, u2} (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Basis.ofVectorSpace.{u2, u1} K V _inst_1 _inst_2 _inst_4)) (Subtype.val.{succ u2} V (fun (x : V) => Membership.mem.{u2, u2} V (Set.{u2} V) (Set.instMembershipSet.{u2} V) x (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)))
Case conversion may be inaccurate. Consider using '#align basis.coe_of_vector_space Basis.coe_ofVectorSpaceₓ'. -/
@[simp]
theorem coe_ofVectorSpace : ⇑(ofVectorSpace K V) = coe :=
  funext fun x => ofVectorSpace_apply_self K V x
#align basis.coe_of_vector_space Basis.coe_ofVectorSpace

/- warning: basis.of_vector_space_index.linear_independent -> Basis.ofVectorSpaceIndex.linearIndependent is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u2}) (V : Type.{u1}) [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)], LinearIndependent.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) V (coeSubtype.{succ u1} V (fun (x : V) => Membership.Mem.{u1, u1} V (Set.{u1} V) (Set.hasMem.{u1} V) x (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4))))))) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], LinearIndependent.{u2, u1, u2} (Subtype.{succ u2} V (fun (x : V) => Membership.mem.{u2, u2} V (Set.{u2} V) (Set.instMembershipSet.{u2} V) x (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4))) K V (Subtype.val.{succ u2} V (fun (x : V) => Membership.mem.{u2, u2} V (Set.{u2} V) (Set.instMembershipSet.{u2} V) x (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4))) (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4
Case conversion may be inaccurate. Consider using '#align basis.of_vector_space_index.linear_independent Basis.ofVectorSpaceIndex.linearIndependentₓ'. -/
theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K (coe : ofVectorSpaceIndex K V → V) :=
  by
  convert(of_vector_space K V).LinearIndependent
  ext x
  rw [of_vector_space_apply_self]
#align basis.of_vector_space_index.linear_independent Basis.ofVectorSpaceIndex.linearIndependent

/- warning: basis.range_of_vector_space -> Basis.range_ofVectorSpace is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u2}) (V : Type.{u1}) [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)], Eq.{succ u1} (Set.{u1} V) (Set.range.{u1, succ u1} V (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) (coeFn.{max (succ u2) (succ u1), succ u1} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (fun (_x : Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) -> V) (FunLike.hasCoeToFun.{max (succ u2) (succ u1), succ u1, succ u1} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) (fun (_x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) => V) (Basis.funLike.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4)) (Basis.ofVectorSpace.{u1, u2} K V _inst_1 _inst_2 _inst_4))) (Basis.ofVectorSpaceIndex.{u1, u2} K V _inst_1 _inst_2 _inst_4)
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Eq.{succ u2} (Set.{u2} V) (Set.range.{u2, succ u2} V (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u2} (Basis.{u2, u1, u2} (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) (fun (_x : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) => V) _x) (Basis.funLike.{u2, u1, u2} (Set.Elem.{u2} V (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Basis.ofVectorSpace.{u2, u1} K V _inst_1 _inst_2 _inst_4))) (Basis.ofVectorSpaceIndex.{u2, u1} K V _inst_1 _inst_2 _inst_4)
Case conversion may be inaccurate. Consider using '#align basis.range_of_vector_space Basis.range_ofVectorSpaceₓ'. -/
theorem range_ofVectorSpace : range (ofVectorSpace K V) = ofVectorSpaceIndex K V :=
  range_extend _
#align basis.range_of_vector_space Basis.range_ofVectorSpace

/- warning: basis.exists_basis -> Basis.exists_basis is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u2}) (V : Type.{u1}) [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)], Exists.{succ u1} (Set.{u1} V) (fun (s : Set.{u1} V) => Nonempty.{max (succ u2) (succ u1)} (Basis.{u1, u2, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} V) Type.{u1} (Set.hasCoeToSort.{u1} V) s) K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4))
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Exists.{succ u2} (Set.{u2} V) (fun (s : Set.{u2} V) => Nonempty.{max (succ u2) (succ u1)} (Basis.{u2, u1, u2} (Set.Elem.{u2} V s) K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4))
Case conversion may be inaccurate. Consider using '#align basis.exists_basis Basis.exists_basisₓ'. -/
theorem exists_basis : ∃ s : Set V, Nonempty (Basis s K V) :=
  ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩
#align basis.exists_basis Basis.exists_basis

end

end ExistsBasis

end Basis

open Fintype

variable (K V)

/- warning: vector_space.card_fintype -> VectorSpace.card_fintype is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u2}) (V : Type.{u1}) [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] [_inst_6 : Fintype.{u2} K] [_inst_7 : Fintype.{u1} V], Exists.{1} Nat (fun (n : Nat) => Eq.{1} Nat (Fintype.card.{u1} V _inst_7) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) (Fintype.card.{u2} K _inst_6) n))
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_6 : Fintype.{u1} K] [_inst_7 : Fintype.{u2} V], Exists.{1} Nat (fun (n : Nat) => Eq.{1} Nat (Fintype.card.{u2} V _inst_7) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (Fintype.card.{u1} K _inst_6) n))
Case conversion may be inaccurate. Consider using '#align vector_space.card_fintype VectorSpace.card_fintypeₓ'. -/
theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : ∃ n : ℕ, card V = card K ^ n := by
  classical exact
      ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩
#align vector_space.card_fintype VectorSpace.card_fintype

section AtomsOfSubmoduleLattice

variable {K V}

/- warning: nonzero_span_atom -> nonzero_span_atom is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (v : V), (Ne.{succ u1} V v (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2))))))))) -> (IsAtom.{u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (SetLike.partialOrder.{u1, u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) V (Submodule.setLike.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4))) (Submodule.orderBot.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (Submodule.span.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4 (Singleton.singleton.{u1, u1} V (Set.{u1} V) (Set.hasSingleton.{u1} V) v)))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V), (Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) -> (IsAtom.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Submodule.completeLattice.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4)))) (Submodule.instOrderBotSubmoduleToLEToPreorderInstPartialOrderSetLike.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Submodule.span.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4 (Singleton.singleton.{u2, u2} V (Set.{u2} V) (Set.instSingletonSet.{u2} V) v)))
Case conversion may be inaccurate. Consider using '#align nonzero_span_atom nonzero_span_atomₓ'. -/
/-- For a module over a division ring, the span of a nonzero element is an atom of the
lattice of submodules. -/
theorem nonzero_span_atom (v : V) (hv : v ≠ 0) : IsAtom (span K {v} : Submodule K V) :=
  by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra
    apply hT.2
    change span K {v} ≤ T
    simp_rw [span_singleton_le_iff_mem, ← Ne.def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    cases' mem_span_singleton.1 (hT.1 hs) with a ha
    have h : a ≠ 0 := by
      intro h
      rw [h, zero_smul] at ha
      exact hz ha.symm
    apply_fun fun x => a⁻¹ • x  at ha
    simp_rw [← mul_smul, inv_mul_cancel h, one_smul, ha] at *
    exact smul_mem T _ hs
#align nonzero_span_atom nonzero_span_atom

/- warning: atom_iff_nonzero_span -> atom_iff_nonzero_span is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (W : Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4), Iff (IsAtom.{u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (SetLike.partialOrder.{u1, u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) V (Submodule.setLike.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4))) (Submodule.orderBot.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) W) (Exists.{succ u1} V (fun (v : V) => Exists.{0} (Ne.{succ u1} V v (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2))))))))) (fun (hv : Ne.{succ u1} V v (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (AddCommGroup.toAddGroup.{u1} V _inst_2))))))))) => Eq.{succ u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) W (Submodule.span.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4 (Singleton.singleton.{u1, u1} V (Set.{u1} V) (Set.hasSingleton.{u1} V) v)))))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (W : Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4), Iff (IsAtom.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Submodule.completeLattice.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4)))) (Submodule.instOrderBotSubmoduleToLEToPreorderInstPartialOrderSetLike.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) W) (Exists.{succ u2} V (fun (v : V) => Exists.{0} (Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) (fun (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) => Eq.{succ u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) W (Submodule.span.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4 (Singleton.singleton.{u2, u2} V (Set.{u2} V) (Set.instSingletonSet.{u2} V) v)))))
Case conversion may be inaccurate. Consider using '#align atom_iff_nonzero_span atom_iff_nonzero_spanₓ'. -/
/-- The atoms of the lattice of submodules of a module over a division ring are the
submodules equal to the span of a nonzero element of the module. -/
theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ ∃ (v : V)(hv : v ≠ 0), W = span K {v} :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · cases' h with hbot h
    rcases(Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine' ⟨v, ⟨hv, _⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm HEq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv
#align atom_iff_nonzero_span atom_iff_nonzero_span

/-- The lattice of submodules of a module over a division ring is atomistic. -/
instance : IsAtomistic (Submodule K V)
    where eq_sSup_atoms := by
    intro W
    use { T : Submodule K V | ∃ (v : V)(hv : v ∈ W)(hz : v ≠ 0), T = span K {v} }
    refine' ⟨submodule_eq_Sup_le_nonzero_spans W, _⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩; exact nonzero_span_atom w hw

end AtomsOfSubmoduleLattice

variable {K V}

/- warning: linear_map.exists_left_inverse_of_injective -> LinearMap.exists_leftInverse_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.exists_left_inverse_of_injective LinearMap.exists_leftInverse_of_injectiveₓ'. -/
theorem LinearMap.exists_leftInverse_of_injective (f : V →ₗ[K] V') (hf_inj : f.ker = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id :=
  by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linear_independent.to_subtype_range
  have : LinearIndependent K (fun x => x : f '' B → V') :=
    by
    have h₁ : LinearIndependent K fun x : ↥(⇑f '' range (Basis.ofVectorSpace _ _)) => ↑x :=
      @LinearIndependent.image_subtype _ _ _ _ _ _ _ _ _ f hB₀ (show Disjoint _ _ by simp [hf_inj])
    rwa [Basis.range_ofVectorSpace K V] at h₁
  let C := this.extend (subset_univ _)
  have BC := this.subset_extend (subset_univ _)
  let hC := Basis.extend this
  haveI : Inhabited V := ⟨0⟩
  refine' ⟨hC.constr ℕ (C.restrict (inv_fun f)), hB.ext fun b => _⟩
  rw [image_subset_iff] at BC
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ :=
    by
    change f b = Basis.extend this _
    rw [Basis.extend_apply_self, Subtype.coe_mk]
  dsimp [hB]
  rw [Basis.ofVectorSpace_apply_self, fb_eq, hC.constr_basis]
  exact left_inverse_inv_fun (LinearMap.ker_eq_bot.1 hf_inj) _
#align linear_map.exists_left_inverse_of_injective LinearMap.exists_leftInverse_of_injective

/- warning: submodule.exists_is_compl -> Submodule.exists_isCompl is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_4 : Module.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (p : Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4), Exists.{succ u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (fun (q : Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) => IsCompl.{u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (SetLike.partialOrder.{u1, u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) V (Submodule.setLike.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4)) (CompleteLattice.toBoundedOrder.{u1} (Submodule.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4) (Submodule.completeLattice.{u2, u1} K V (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_4)) p q)
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_4 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (p : Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4), Exists.{succ u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (fun (q : Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) => IsCompl.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Submodule.completeLattice.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4))) (CompleteLattice.toBoundedOrder.{u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4) (Submodule.completeLattice.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_4)) p q)
Case conversion may be inaccurate. Consider using '#align submodule.exists_is_compl Submodule.exists_isComplₓ'. -/
theorem Submodule.exists_isCompl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  let ⟨f, hf⟩ := p.Subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.ker, LinearMap.isCompl_of_proj <| LinearMap.ext_iff.1 hf⟩
#align submodule.exists_is_compl Submodule.exists_isCompl

#print Module.Submodule.complementedLattice /-
instance Module.Submodule.complementedLattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_isCompl⟩
#align module.submodule.complemented_lattice Module.Submodule.complementedLattice
-/

/- warning: linear_map.exists_right_inverse_of_surjective -> LinearMap.exists_rightInverse_of_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.exists_right_inverse_of_surjective LinearMap.exists_rightInverse_of_surjectiveₓ'. -/
theorem LinearMap.exists_rightInverse_of_surjective (f : V →ₗ[K] V') (hf_surj : f.range = ⊤) :
    ∃ g : V' →ₗ[K] V, f.comp g = LinearMap.id :=
  by
  let C := Basis.ofVectorSpaceIndex K V'
  let hC := Basis.ofVectorSpace K V'
  haveI : Inhabited V := ⟨0⟩
  use hC.constr ℕ (C.restrict (inv_fun f))
  refine' hC.ext fun c => _
  rw [LinearMap.comp_apply, hC.constr_basis]
  simp [right_inverse_inv_fun (LinearMap.range_eq_top.1 hf_surj) c]
#align linear_map.exists_right_inverse_of_surjective LinearMap.exists_rightInverse_of_surjective

/- warning: linear_map.exists_extend -> LinearMap.exists_extend is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.exists_extend LinearMap.exists_extendₓ'. -/
/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.Subtype = f :=
  let ⟨g, hg⟩ := p.Subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩
#align linear_map.exists_extend LinearMap.exists_extend

open Submodule LinearMap

/- warning: submodule.exists_le_ker_of_lt_top -> Submodule.exists_le_ker_of_lt_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.exists_le_ker_of_lt_top Submodule.exists_le_ker_of_lt_topₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (f «expr ≠ » (0 : «expr →ₗ[ ] »(V, K, K))) -/
/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    ∃ (f : _)(_ : f ≠ (0 : V →ₗ[K] K)), p ≤ ker f :=
  by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩; clear hp
  rcases(LinearPMap.supSpanSingleton ⟨p, 0⟩ v (1 : K) hpv).toFun.exists_extend with ⟨f, hf⟩
  refine' ⟨f, _, _⟩
  · rintro rfl
    rw [LinearMap.zero_comp] at hf
    have := LinearPMap.supSpanSingleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1
    simpa using (LinearMap.congr_fun hf _).trans this
  · refine' fun x hx => mem_ker.2 _
    have := LinearPMap.supSpanSingleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0
    simpa using (LinearMap.congr_fun hf _).trans this
#align submodule.exists_le_ker_of_lt_top Submodule.exists_le_ker_of_lt_top

/- warning: quotient_prod_linear_equiv -> quotient_prod_linearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align quotient_prod_linear_equiv quotient_prod_linearEquivₓ'. -/
theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_isCompl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).Prod (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)
#align quotient_prod_linear_equiv quotient_prod_linearEquiv

end DivisionRing

section RestrictScalars

variable {S : Type _} [CommRing R] [Ring S] [Nontrivial S] [AddCommGroup M]

variable [Algebra R S] [Module S M] [Module R M]

variable [IsScalarTower R S M] [NoZeroSMulDivisors R S] (b : Basis ι S M)

variable (R)

open Submodule

/- warning: basis.restrict_scalars -> Basis.restrictScalars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.restrict_scalars Basis.restrictScalarsₓ'. -/
/-- Let `b` be a `S`-basis of `M`. Let `R` be a comm_ring such that `algebra R S` with no zero
smul divisors, then the submodule of `M` spanned by `b` over `R` admits `b` as a `R`-basis. -/
noncomputable def Basis.restrictScalars : Basis ι R (span R (Set.range b)) :=
  Basis.span (b.LinearIndependent.restrictScalars (smul_left_injective R one_ne_zero))
#align basis.restrict_scalars Basis.restrictScalars

/- warning: basis.restrict_scalars_apply -> Basis.restrictScalars_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.restrict_scalars_apply Basis.restrictScalars_applyₓ'. -/
@[simp]
theorem Basis.restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Basis.restrictScalars, Basis.span_apply]
#align basis.restrict_scalars_apply Basis.restrictScalars_apply

/- warning: basis.restrict_scalars_repr_apply -> Basis.restrictScalars_repr_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.restrict_scalars_repr_apply Basis.restrictScalars_repr_applyₓ'. -/
@[simp]
theorem Basis.restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i :=
  by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrict_scalars R).repr.toLinearMap =
      ((b.repr : M →ₗ[S] ι →₀ S).restrictScalars R).domRestrict _
    by exact Finsupp.congr_fun (LinearMap.congr_fun this m) i
  refine' Basis.ext (b.restrict_scalars R) fun _ => _
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply, LinearEquiv.coe_coe,
    Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]
#align basis.restrict_scalars_repr_apply Basis.restrictScalars_repr_apply

/- warning: basis.mem_span_iff_repr_mem -> Basis.mem_span_iff_repr_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.mem_span_iff_repr_mem Basis.mem_span_iff_repr_memₓ'. -/
/-- Let `b` be a `S`-basis of `M`. Then `m : M` lies in the `R`-module spanned by `b` iff all the
coordinates of `m` on the basis `b` are in `R` (see `basis.mem_span` for the case `R = S`). -/
theorem Basis.mem_span_iff_repr_mem (m : M) :
    m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S) :=
  by
  refine'
    ⟨fun hm i => ⟨(b.restrict_scalars R).repr ⟨m, hm⟩ i, b.restrict_scalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => _⟩
  rw [← b.total_repr m, Finsupp.total_apply S _]
  refine' sum_mem fun i _ => _
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))
#align basis.mem_span_iff_repr_mem Basis.mem_span_iff_repr_mem

end RestrictScalars

