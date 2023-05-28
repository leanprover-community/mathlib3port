/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module linear_algebra.invariant_basis_number
! leanprover-community/mathlib commit c085f3044fe585c575e322bfab45b3633c48d820
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Quotient
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Invariant basis number property

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

It is also useful to consider two stronger conditions, namely the rank condition,
that a surjective linear map `(fin n → R) →ₗ[R] (fin m → R)` implies `m ≤ n` and
the strong rank condition, that an injective linear map `(fin n → R) →ₗ[R] (fin m → R)`
implies `n ≤ m`.

The strong rank condition implies the rank condition, and the rank condition implies
the invariant basis number property.

## Main definitions

`strong_rank_condition R` is a type class stating that `R` satisfies the strong rank condition.
`rank_condition R` is a type class stating that `R` satisfies the rank condition.
`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial left-noetherian ring satisfies the strong rank condition,
(and so in particular every division ring or field),
and then use this to show every nontrivial commutative ring has the invariant basis number property.

More generally, every commutative ring satisfies the strong rank condition. This is proved in
`linear_algebra/free_module/strong_rank_condition`. We keep
`invariant_basis_number_of_nontrivial_of_comm_ring` here since it imports fewer files.

## Future work

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or providing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number
* https://mathoverflow.net/a/2574/

## Tags

free module, rank, invariant basis number, IBN

-/


noncomputable section

open Classical BigOperators

open Function

universe u v w

section

variable (R : Type u) [Semiring R]

#print StrongRankCondition /-
/-- We say that `R` satisfies the strong rank condition if `(fin n → R) →ₗ[R] (fin m → R)` injective
    implies `n ≤ m`. -/
@[mk_iff]
class StrongRankCondition : Prop where
  le_of_fin_injective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Injective f → n ≤ m
#align strong_rank_condition StrongRankCondition
-/

/- warning: le_of_fin_injective -> le_of_fin_injective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R _inst_1] {n : Nat} {m : Nat} (f : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))), (Function.Injective.{succ u1, succ u1} ((Fin n) -> R) ((Fin m) -> R) (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) => ((Fin n) -> R) -> (Fin m) -> R) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R ((Fin n) -> R) ((Fin m) -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (LE.le.{0} Nat Nat.hasLe n m)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R _inst_1] {n : Nat} {m : Nat} (f : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{0, u1, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.88 : Fin n) => R) R _inst_1 (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{0, u1, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.92 : Fin m) => R) R _inst_1 (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin m) => Semiring.toModule.{u1} R _inst_1))), (Function.Injective.{succ u1, succ u1} ((Fin n) -> R) ((Fin m) -> R) (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.88 : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.92 : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{0, u1, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.88 : Fin n) => R) R _inst_1 (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{0, u1, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.92 : Fin m) => R) R _inst_1 (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin m) => Semiring.toModule.{u1} R _inst_1))) ((Fin n) -> R) (fun (_x : (Fin n) -> R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : (Fin n) -> R) => (Fin m) -> R) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R ((Fin n) -> R) ((Fin m) -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{0, u1, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.88 : Fin n) => R) R _inst_1 (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{0, u1, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.92 : Fin m) => R) R _inst_1 (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin m) => Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (LE.le.{0} Nat instLENat n m)
Case conversion may be inaccurate. Consider using '#align le_of_fin_injective le_of_fin_injectiveₓ'. -/
theorem le_of_fin_injective [StrongRankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Injective f → n ≤ m :=
  StrongRankCondition.le_of_fin_injective f
#align le_of_fin_injective le_of_fin_injective

/- warning: strong_rank_condition_iff_succ -> strongRankCondition_iff_succ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align strong_rank_condition_iff_succ strongRankCondition_iff_succₓ'. -/
/-- A ring satisfies the strong rank condition if and only if, for all `n : ℕ`, any linear map
`(fin (n + 1) → R) →ₗ[R] (fin n → R)` is not injective. -/
theorem strongRankCondition_iff_succ :
    StrongRankCondition R ↔
      ∀ (n : ℕ) (f : (Fin (n + 1) → R) →ₗ[R] Fin n → R), ¬Function.Injective f :=
  by
  refine' ⟨fun h n => fun f hf => _, fun h => ⟨fun n m f hf => _⟩⟩
  · letI : StrongRankCondition R := h
    exact Nat.not_succ_le_self n (le_of_fin_injective R f hf)
  · by_contra H
    exact
      h m (f.comp (Function.ExtendByZero.linearMap R (Fin.castLE (not_le.1 H))))
        (hf.comp (Function.extend_injective (RelEmbedding.injective _) 0))
#align strong_rank_condition_iff_succ strongRankCondition_iff_succ

/- warning: card_le_of_injective -> card_le_of_injective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : StrongRankCondition.{u1} R _inst_1] {α : Type.{u2}} {β : Type.{u3}} [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u3} β] (f : LinearMap.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))), (Function.Injective.{max (succ u2) (succ u1), max (succ u3) (succ u1)} (α -> R) (β -> R) (coeFn.{max (succ (max u2 u1)) (succ (max u3 u1)), max (succ (max u2 u1)) (succ (max u3 u1))} (LinearMap.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) => (α -> R) -> β -> R) (LinearMap.hasCoeToFun.{u1, u1, max u2 u1, max u3 u1} R R (α -> R) (β -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u2} α _inst_3) (Fintype.card.{u3} β _inst_4))
but is expected to have type
  forall (R : Type.{u3}) [_inst_1 : Semiring.{u3} R] [_inst_2 : StrongRankCondition.{u3} R _inst_1] {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u1} β] (f : LinearMap.{u3, u3, max u3 u2, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u3} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.283 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.286 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1))), (Function.Injective.{max (succ u3) (succ u2), max (succ u3) (succ u1)} (α -> R) (β -> R) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), max (succ u3) (succ u2), max (succ u3) (succ u1)} (LinearMap.{u3, u3, max u3 u2, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.283 : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.286 : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.283 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.286 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1))) (α -> R) (fun (_x : α -> R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : α -> R) => β -> R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, max u3 u2, max u3 u1} R R (α -> R) (β -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.283 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.286 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) f)) -> (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_3) (Fintype.card.{u1} β _inst_4))
Case conversion may be inaccurate. Consider using '#align card_le_of_injective card_le_of_injectiveₓ'. -/
theorem card_le_of_injective [StrongRankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Injective f) : Fintype.card α ≤ Fintype.card β :=
  by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_injective R ((Q.symm.to_linear_map.comp f).comp P.to_linear_map)
      (((LinearEquiv.symm Q).Injective.comp i).comp (LinearEquiv.injective P))
#align card_le_of_injective card_le_of_injective

/- warning: card_le_of_injective' -> card_le_of_injective' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align card_le_of_injective' card_le_of_injective'ₓ'. -/
theorem card_le_of_injective' [StrongRankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Injective f) : Fintype.card α ≤ Fintype.card β :=
  by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_injective R ((P.to_linear_map.comp f).comp Q.to_linear_map)
      ((P.injective.comp i).comp Q.injective)
#align card_le_of_injective' card_le_of_injective'

#print RankCondition /-
/-- We say that `R` satisfies the rank condition if `(fin n → R) →ₗ[R] (fin m → R)` surjective
    implies `m ≤ n`. -/
class RankCondition : Prop where
  le_of_fin_surjective : ∀ {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R), Surjective f → m ≤ n
#align rank_condition RankCondition
-/

/- warning: le_of_fin_surjective -> le_of_fin_surjective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : RankCondition.{u1} R _inst_1] {n : Nat} {m : Nat} (f : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))), (Function.Surjective.{succ u1, succ u1} ((Fin n) -> R) ((Fin m) -> R) (coeFn.{succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) => ((Fin n) -> R) -> (Fin m) -> R) (LinearMap.hasCoeToFun.{u1, u1, u1, u1} R R ((Fin n) -> R) ((Fin m) -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{0, u1, u1} (Fin n) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{0, u1, u1} (Fin m) R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (LE.le.{0} Nat Nat.hasLe m n)
but is expected to have type
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : RankCondition.{u1} R _inst_1] {n : Nat} {m : Nat} (f : LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{0, u1, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.546 : Fin n) => R) R _inst_1 (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{0, u1, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.550 : Fin m) => R) R _inst_1 (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin m) => Semiring.toModule.{u1} R _inst_1))), (Function.Surjective.{succ u1, succ u1} ((Fin n) -> R) ((Fin m) -> R) (FunLike.coe.{succ u1, succ u1, succ u1} (LinearMap.{u1, u1, u1, u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) ((Fin n) -> R) ((Fin m) -> R) (Pi.addCommMonoid.{0, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.546 : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.550 : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{0, u1, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.546 : Fin n) => R) R _inst_1 (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{0, u1, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.550 : Fin m) => R) R _inst_1 (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin m) => Semiring.toModule.{u1} R _inst_1))) ((Fin n) -> R) (fun (_x : (Fin n) -> R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : (Fin n) -> R) => (Fin m) -> R) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u1} R R ((Fin n) -> R) ((Fin m) -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{0, u1} (Fin n) (fun (ᾰ : Fin n) => R) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{0, u1} (Fin m) (fun (ᾰ : Fin m) => R) (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.module.{0, u1, u1} (Fin n) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.546 : Fin n) => R) R _inst_1 (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin n) => Semiring.toModule.{u1} R _inst_1)) (Pi.module.{0, u1, u1} (Fin m) (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.550 : Fin m) => R) R _inst_1 (fun (i : Fin m) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (i : Fin m) => Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (LE.le.{0} Nat instLENat m n)
Case conversion may be inaccurate. Consider using '#align le_of_fin_surjective le_of_fin_surjectiveₓ'. -/
theorem le_of_fin_surjective [RankCondition R] {n m : ℕ} (f : (Fin n → R) →ₗ[R] Fin m → R) :
    Surjective f → m ≤ n :=
  RankCondition.le_of_fin_surjective f
#align le_of_fin_surjective le_of_fin_surjective

/- warning: card_le_of_surjective -> card_le_of_surjective is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : RankCondition.{u1} R _inst_1] {α : Type.{u2}} {β : Type.{u3}} [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u3} β] (f : LinearMap.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))), (Function.Surjective.{max (succ u2) (succ u1), max (succ u3) (succ u1)} (α -> R) (β -> R) (coeFn.{max (succ (max u2 u1)) (succ (max u3 u1)), max (succ (max u2 u1)) (succ (max u3 u1))} (LinearMap.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) (fun (_x : LinearMap.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) => (α -> R) -> β -> R) (LinearMap.hasCoeToFun.{u1, u1, max u2 u1, max u3 u1} R R (α -> R) (β -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f)) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u3} β _inst_4) (Fintype.card.{u2} α _inst_3))
but is expected to have type
  forall (R : Type.{u3}) [_inst_1 : Semiring.{u3} R] [_inst_2 : RankCondition.{u3} R _inst_1] {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u1} β] (f : LinearMap.{u3, u3, max u3 u2, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u3} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.591 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.594 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1))), (Function.Surjective.{max (succ u3) (succ u2), max (succ u3) (succ u1)} (α -> R) (β -> R) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), max (succ u3) (succ u2), max (succ u3) (succ u1)} (LinearMap.{u3, u3, max u3 u2, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.591 : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.594 : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.591 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.594 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1))) (α -> R) (fun (_x : α -> R) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : α -> R) => β -> R) _x) (LinearMap.instFunLikeLinearMap.{u3, u3, max u3 u2, max u3 u1} R R (α -> R) (β -> R) _inst_1 _inst_1 (Pi.addCommMonoid.{u2, u3} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.591 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.594 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) f)) -> (LE.le.{0} Nat instLENat (Fintype.card.{u1} β _inst_4) (Fintype.card.{u2} α _inst_3))
Case conversion may be inaccurate. Consider using '#align card_le_of_surjective card_le_of_surjectiveₓ'. -/
theorem card_le_of_surjective [RankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α → R) →ₗ[R] β → R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α :=
  by
  let P := LinearEquiv.funCongrLeft R R (Fintype.equivFin α)
  let Q := LinearEquiv.funCongrLeft R R (Fintype.equivFin β)
  exact
    le_of_fin_surjective R ((Q.symm.to_linear_map.comp f).comp P.to_linear_map)
      (((LinearEquiv.symm Q).Surjective.comp i).comp (LinearEquiv.surjective P))
#align card_le_of_surjective card_le_of_surjective

/- warning: card_le_of_surjective' -> card_le_of_surjective' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align card_le_of_surjective' card_le_of_surjective'ₓ'. -/
theorem card_le_of_surjective' [RankCondition R] {α β : Type _} [Fintype α] [Fintype β]
    (f : (α →₀ R) →ₗ[R] β →₀ R) (i : Surjective f) : Fintype.card β ≤ Fintype.card α :=
  by
  let P := Finsupp.linearEquivFunOnFinite R R β
  let Q := (Finsupp.linearEquivFunOnFinite R R α).symm
  exact
    card_le_of_surjective R ((P.to_linear_map.comp f).comp Q.to_linear_map)
      ((P.surjective.comp i).comp Q.surjective)
#align card_le_of_surjective' card_le_of_surjective'

#print rankCondition_of_strongRankCondition /-
/-- By the universal property for free modules, any surjective map `(fin n → R) →ₗ[R] (fin m → R)`
has an injective splitting `(fin m → R) →ₗ[R] (fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
instance (priority := 100) rankCondition_of_strongRankCondition [StrongRankCondition R] :
    RankCondition R
    where le_of_fin_surjective n m f s :=
    le_of_fin_injective R _ (f.splittingOfFunOnFintypeSurjective_injective s)
#align rank_condition_of_strong_rank_condition rankCondition_of_strongRankCondition
-/

#print InvariantBasisNumber /-
/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class InvariantBasisNumber : Prop where
  eq_of_fin_equiv : ∀ {n m : ℕ}, ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m
#align invariant_basis_number InvariantBasisNumber
-/

#print invariantBasisNumber_of_rankCondition /-
instance (priority := 100) invariantBasisNumber_of_rankCondition [RankCondition R] :
    InvariantBasisNumber R
    where eq_of_fin_equiv n m e :=
    le_antisymm (le_of_fin_surjective R e.symm.toLinearMap e.symm.Surjective)
      (le_of_fin_surjective R e.toLinearMap e.Surjective)
#align invariant_basis_number_of_rank_condition invariantBasisNumber_of_rankCondition
-/

end

section

variable (R : Type u) [Semiring R] [InvariantBasisNumber R]

#print eq_of_fin_equiv /-
theorem eq_of_fin_equiv {n m : ℕ} : ((Fin n → R) ≃ₗ[R] Fin m → R) → n = m :=
  InvariantBasisNumber.eq_of_fin_equiv
#align eq_of_fin_equiv eq_of_fin_equiv
-/

/- warning: card_eq_of_lequiv -> card_eq_of_linearEquiv is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) [_inst_1 : Semiring.{u1} R] [_inst_2 : InvariantBasisNumber.{u1} R _inst_1] {α : Type.{u2}} {β : Type.{u3}} [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u3} β], (LinearEquiv.{u1, u1, max u2 u1, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHomInvPair.ids.{u1} R _inst_1) (RingHomInvPair.ids.{u1} R _inst_1) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u1} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.addCommMonoid.{u3, u1} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (Pi.Function.module.{u2, u1, u1} α R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1)) (Pi.Function.module.{u3, u1, u1} β R R _inst_1 (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Semiring.toModule.{u1} R _inst_1))) -> (Eq.{1} Nat (Fintype.card.{u2} α _inst_3) (Fintype.card.{u3} β _inst_4))
but is expected to have type
  forall (R : Type.{u3}) [_inst_1 : Semiring.{u3} R] [_inst_2 : InvariantBasisNumber.{u3} R _inst_1] {α : Type.{u2}} {β : Type.{u1}} [_inst_3 : Fintype.{u2} α] [_inst_4 : Fintype.{u1} β], (LinearEquiv.{u3, u3, max u3 u2, max u3 u1} R R _inst_1 _inst_1 (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHom.id.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)) (RingHomInvPair.ids.{u3} R _inst_1) (RingHomInvPair.ids.{u3} R _inst_1) (α -> R) (β -> R) (Pi.addCommMonoid.{u2, u3} α (fun (ᾰ : α) => R) (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.addCommMonoid.{u1, u3} β (fun (ᾰ : β) => R) (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1)))) (Pi.module.{u2, u3, u3} α (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.970 : α) => R) R _inst_1 (fun (i : α) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : α) => Semiring.toModule.{u3} R _inst_1)) (Pi.module.{u1, u3, u3} β (fun (a._@.Mathlib.LinearAlgebra.InvariantBasisNumber._hyg.973 : β) => R) R _inst_1 (fun (i : β) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) (fun (i : β) => Semiring.toModule.{u3} R _inst_1))) -> (Eq.{1} Nat (Fintype.card.{u2} α _inst_3) (Fintype.card.{u1} β _inst_4))
Case conversion may be inaccurate. Consider using '#align card_eq_of_lequiv card_eq_of_linearEquivₓ'. -/
theorem card_eq_of_linearEquiv {α β : Type _} [Fintype α] [Fintype β] (f : (α → R) ≃ₗ[R] β → R) :
    Fintype.card α = Fintype.card β :=
  eq_of_fin_equiv R
    ((LinearEquiv.funCongrLeft R R (Fintype.equivFin α)).trans f ≪≫ₗ
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin β)).symm)
#align card_eq_of_lequiv card_eq_of_linearEquiv

#print nontrivial_of_invariantBasisNumber /-
theorem nontrivial_of_invariantBasisNumber : Nontrivial R :=
  by
  by_contra h
  refine' zero_ne_one (eq_of_fin_equiv R _)
  haveI := not_nontrivial_iff_subsingleton.1 h
  haveI : Subsingleton (Fin 1 → R) := ⟨fun a b => funext fun x => Subsingleton.elim _ _⟩
  refine' { .. } <;> first |· intros ; exact 0|tidy
#align nontrivial_of_invariant_basis_number nontrivial_of_invariantBasisNumber
-/

end

section

variable (R : Type u) [Ring R] [Nontrivial R] [IsNoetherianRing R]

#print IsNoetherianRing.strongRankCondition /-
-- Note this includes fields,
-- and we use this below to show any commutative ring has invariant basis number.
/-- Any nontrivial noetherian ring satisfies the strong rank condition.

An injective map `((fin n ⊕ fin (1 + m)) → R) →ₗ[R] (fin n → R)` for some left-noetherian `R`
would force `fin (1 + m) → R ≃ₗ punit` (via `is_noetherian.equiv_punit_of_prod_injective`),
which is not the case!
-/
instance (priority := 100) IsNoetherianRing.strongRankCondition : StrongRankCondition R :=
  by
  fconstructor
  intro m n f i
  by_contra h
  rw [not_le, ← Nat.add_one_le_iff, le_iff_exists_add] at h
  obtain ⟨m, rfl⟩ := h
  let e : Fin (n + 1 + m) ≃ Sum (Fin n) (Fin (1 + m)) :=
    (finCongr (add_assoc _ _ _)).trans fin_sum_fin_equiv.symm
  let f' :=
    f.comp
      ((LinearEquiv.sumArrowLequivProdArrow _ _ R R).symm.trans
          (LinearEquiv.funCongrLeft R R e)).toLinearMap
  have i' : injective f' := i.comp (LinearEquiv.injective _)
  apply @zero_ne_one (Fin (1 + m) → R) _ _
  apply (IsNoetherian.equivPunitOfProdInjective f' i').Injective
  ext
#align noetherian_ring_strong_rank_condition IsNoetherianRing.strongRankCondition
-/

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `ideal.pi_quot_equiv` and is located in the file `ring_theory/ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/


section

variable {R : Type u} [CommRing R] (I : Ideal R) {ι : Type v} [Fintype ι] {ι' : Type w}

/- warning: induced_map clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align induced_map [anonymous]ₓ'. -/
#print [anonymous] /-
/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
private def [anonymous] (I : Ideal R) (e : (ι → R) →ₗ[R] ι' → R) :
    (ι → R) ⧸ I.pi ι → (ι' → R) ⧸ I.pi ι' := fun x =>
  Quotient.liftOn' x (fun y => Ideal.Quotient.mk _ (e y))
    (by
      refine' fun a b hab => Ideal.Quotient.eq.2 fun h => _
      rw [Submodule.quotientRel_r_def] at hab
      rw [← LinearMap.map_sub]
      exact Ideal.map_pi _ _ hab e h)
-/

/- warning: induced_equiv clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align induced_equiv [anonymous]ₓ'. -/
#print [anonymous] /-
/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def [anonymous] [Fintype ι'] (I : Ideal R) (e : (ι → R) ≃ₗ[R] ι' → R) :
    ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] (ι' → R) ⧸ I.pi ι' :=
  by
  refine'
    { toFun := [anonymous] I e
      invFun := [anonymous] I e.symm.. }
  all_goals
    first |rintro ⟨a⟩ ⟨b⟩|rintro ⟨a⟩
    convert_to Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    congr
    simp only [map_add, LinearEquiv.coe_coe, LinearEquiv.map_smulₛₗ, RingHom.id_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
-/

end

section

attribute [local instance] Ideal.Quotient.field

#print invariantBasisNumber_of_nontrivial_of_commRing /-
/-- Nontrivial commutative rings have the invariant basis number property.

In fact, any nontrivial commutative ring satisfies the strong rank condition, see
`comm_ring_strong_rank_condition`. We prove this instance separately to avoid dependency on
`linear_algebra.charpoly.basic`. -/
instance (priority := 100) invariantBasisNumber_of_nontrivial_of_commRing {R : Type u} [CommRing R]
    [Nontrivial R] : InvariantBasisNumber R :=
  ⟨fun n m e =>
    let ⟨I, hI⟩ := Ideal.exists_maximal R
    eq_of_fin_equiv (R ⧸ I)
      ((Ideal.piQuotEquiv _ _).symm ≪≫ₗ ([anonymous] _ e ≪≫ₗ Ideal.piQuotEquiv _ _))⟩
#align invariant_basis_number_of_nontrivial_of_comm_ring invariantBasisNumber_of_nontrivial_of_commRing
-/

end

