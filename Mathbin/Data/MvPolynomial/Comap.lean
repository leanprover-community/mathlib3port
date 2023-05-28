/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.mv_polynomial.comap
! leanprover-community/mathlib commit 932872382355f00112641d305ba0619305dc8642
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.MvPolynomial.Rename

/-!
# `comap` operation on `mv_polynomial`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `comap` function on `mv_polynomial`.

`mv_polynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[comm_semiring R]` (the coefficients)

-/


namespace MvPolynomial

variable {σ : Type _} {τ : Type _} {υ : Type _} {R : Type _} [CommSemiring R]

#print MvPolynomial.comap /-
/-- Given an algebra hom `f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R`
and a variable evaluation `v : τ → R`,
`comap f v` produces a variable evaluation `σ → R`.
-/
noncomputable def comap (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) : (τ → R) → σ → R :=
  fun x i => aeval x (f (X i))
#align mv_polynomial.comap MvPolynomial.comap
-/

/- warning: mv_polynomial.comap_apply -> MvPolynomial.comap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_apply MvPolynomial.comap_applyₓ'. -/
@[simp]
theorem comap_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (x : τ → R) (i : σ) :
    comap f x i = aeval x (f (X i)) :=
  rfl
#align mv_polynomial.comap_apply MvPolynomial.comap_apply

/- warning: mv_polynomial.comap_id_apply -> MvPolynomial.comap_id_apply is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (x : σ -> R), Eq.{max (succ u1) (succ u2)} (σ -> R) (MvPolynomial.comap.{u1, u1, u2} σ σ R _inst_1 (AlgHom.id.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1))) x) x
but is expected to have type
  forall {σ : Type.{u2}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] (x : σ -> R), Eq.{max (succ u2) (succ u1)} (σ -> R) (MvPolynomial.comap.{u2, u2, u1} σ σ R _inst_1 (AlgHom.id.{u1, max u1 u2} R (MvPolynomial.{u2, u1} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1))) x) x
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_id_apply MvPolynomial.comap_id_applyₓ'. -/
@[simp]
theorem comap_id_apply (x : σ → R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x := by funext i;
  simp only [comap, AlgHom.id_apply, id.def, aeval_X]
#align mv_polynomial.comap_id_apply MvPolynomial.comap_id_apply

variable (σ R)

/- warning: mv_polynomial.comap_id -> MvPolynomial.comap_id is a dubious translation:
lean 3 declaration is
  forall (σ : Type.{u1}) (R : Type.{u2}) [_inst_1 : CommSemiring.{u2} R], Eq.{max (succ u1) (succ u2)} ((σ -> R) -> σ -> R) (MvPolynomial.comap.{u1, u1, u2} σ σ R _inst_1 (AlgHom.id.{u2, max u1 u2} R (MvPolynomial.{u1, u2} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u2} (MvPolynomial.{u1, u2} σ R _inst_1) (MvPolynomial.commSemiring.{u2, u1} R σ _inst_1)) (MvPolynomial.algebra.{u2, u2, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u2} R _inst_1)))) (id.{max (succ u1) (succ u2)} (σ -> R))
but is expected to have type
  forall (σ : Type.{u2}) (R : Type.{u1}) [_inst_1 : CommSemiring.{u1} R], Eq.{max (succ u2) (succ u1)} ((σ -> R) -> σ -> R) (MvPolynomial.comap.{u2, u2, u1} σ σ R _inst_1 (AlgHom.id.{u1, max u1 u2} R (MvPolynomial.{u2, u1} σ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u1} (MvPolynomial.{u2, u1} σ R _inst_1) (MvPolynomial.commSemiring.{u1, u2} R σ _inst_1)) (MvPolynomial.algebra.{u1, u1, u2} R R σ _inst_1 _inst_1 (Algebra.id.{u1} R _inst_1)))) (id.{max (succ u2) (succ u1)} (σ -> R))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_id MvPolynomial.comap_idₓ'. -/
theorem comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id := by funext x;
  exact comap_id_apply x
#align mv_polynomial.comap_id MvPolynomial.comap_id

variable {σ R}

/- warning: mv_polynomial.comap_comp_apply -> MvPolynomial.comap_comp_apply is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {τ : Type.{u2}} {υ : Type.{u3}} {R : Type.{u4}} [_inst_1 : CommSemiring.{u4} R] (f : AlgHom.{u4, max u1 u4, max u2 u4} R (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (g : AlgHom.{u4, max u2 u4, max u3 u4} R (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u3, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (x : υ -> R), Eq.{max (succ u1) (succ u4)} (σ -> R) (MvPolynomial.comap.{u1, u3, u4} σ υ R _inst_1 (AlgHom.comp.{u4, max u1 u4, max u2 u4, max u3 u4} R (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u3, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) g f) x) (MvPolynomial.comap.{u1, u2, u4} σ τ R _inst_1 f (MvPolynomial.comap.{u2, u3, u4} τ υ R _inst_1 g x))
but is expected to have type
  forall {σ : Type.{u3}} {τ : Type.{u2}} {υ : Type.{u1}} {R : Type.{u4}} [_inst_1 : CommSemiring.{u4} R] (f : AlgHom.{u4, max u4 u3, max u4 u2} R (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (g : AlgHom.{u4, max u4 u2, max u4 u1} R (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u1, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (x : υ -> R), Eq.{max (succ u3) (succ u4)} (σ -> R) (MvPolynomial.comap.{u3, u1, u4} σ υ R _inst_1 (AlgHom.comp.{u4, max u4 u3, max u2 u4, max u1 u4} R (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u1, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) g f) x) (MvPolynomial.comap.{u3, u2, u4} σ τ R _inst_1 f (MvPolynomial.comap.{u2, u1, u4} τ υ R _inst_1 g x))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_comp_apply MvPolynomial.comap_comp_applyₓ'. -/
theorem comap_comp_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) (x : υ → R) :
    comap (g.comp f) x = comap f (comap g x) :=
  by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂_hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [comap, aeval_eq_eval₂_hom, map_eval₂_hom, AlgHom.comp_apply]
    refine' eval₂_hom_congr _ rfl rfl
    ext r; apply aeval_C
#align mv_polynomial.comap_comp_apply MvPolynomial.comap_comp_apply

/- warning: mv_polynomial.comap_comp -> MvPolynomial.comap_comp is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {τ : Type.{u2}} {υ : Type.{u3}} {R : Type.{u4}} [_inst_1 : CommSemiring.{u4} R] (f : AlgHom.{u4, max u1 u4, max u2 u4} R (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (g : AlgHom.{u4, max u2 u4, max u3 u4} R (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u3, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))), Eq.{max (max (succ u3) (succ u4)) (succ u1) (succ u4)} ((υ -> R) -> σ -> R) (MvPolynomial.comap.{u1, u3, u4} σ υ R _inst_1 (AlgHom.comp.{u4, max u1 u4, max u2 u4, max u3 u4} R (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u3, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) g f)) (Function.comp.{max (succ u3) (succ u4), max (succ u2) (succ u4), max (succ u1) (succ u4)} (υ -> R) (τ -> R) (σ -> R) (MvPolynomial.comap.{u1, u2, u4} σ τ R _inst_1 f) (MvPolynomial.comap.{u2, u3, u4} τ υ R _inst_1 g))
but is expected to have type
  forall {σ : Type.{u3}} {τ : Type.{u2}} {υ : Type.{u1}} {R : Type.{u4}} [_inst_1 : CommSemiring.{u4} R] (f : AlgHom.{u4, max u4 u3, max u4 u2} R (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))) (g : AlgHom.{u4, max u4 u2, max u4 u1} R (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u1, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1))), Eq.{max (max (succ u3) (succ u1)) (succ u4)} ((υ -> R) -> σ -> R) (MvPolynomial.comap.{u3, u1, u4} σ υ R _inst_1 (AlgHom.comp.{u4, max u4 u3, max u2 u4, max u1 u4} R (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.{u1, u4} υ R _inst_1) _inst_1 (CommSemiring.toSemiring.{max u3 u4} (MvPolynomial.{u3, u4} σ R _inst_1) (MvPolynomial.commSemiring.{u4, u3} R σ _inst_1)) (CommSemiring.toSemiring.{max u2 u4} (MvPolynomial.{u2, u4} τ R _inst_1) (MvPolynomial.commSemiring.{u4, u2} R τ _inst_1)) (CommSemiring.toSemiring.{max u1 u4} (MvPolynomial.{u1, u4} υ R _inst_1) (MvPolynomial.commSemiring.{u4, u1} R υ _inst_1)) (MvPolynomial.algebra.{u4, u4, u3} R R σ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u2} R R τ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) (MvPolynomial.algebra.{u4, u4, u1} R R υ _inst_1 _inst_1 (Algebra.id.{u4} R _inst_1)) g f)) (Function.comp.{max (succ u4) (succ u1), max (succ u4) (succ u2), max (succ u4) (succ u3)} (υ -> R) (τ -> R) (σ -> R) (MvPolynomial.comap.{u3, u2, u4} σ τ R _inst_1 f) (MvPolynomial.comap.{u2, u1, u4} τ υ R _inst_1 g))
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_comp MvPolynomial.comap_compₓ'. -/
theorem comap_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) : comap (g.comp f) = comap f ∘ comap g := by
  funext x; exact comap_comp_apply _ _ _
#align mv_polynomial.comap_comp MvPolynomial.comap_comp

#print MvPolynomial.comap_eq_id_of_eq_id /-
theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (hf : ∀ φ, f φ = φ)
    (x : σ → R) : comap f x = x := by convert comap_id_apply x; ext1 φ; rw [hf, AlgHom.id_apply]
#align mv_polynomial.comap_eq_id_of_eq_id MvPolynomial.comap_eq_id_of_eq_id
-/

/- warning: mv_polynomial.comap_rename -> MvPolynomial.comap_rename is a dubious translation:
lean 3 declaration is
  forall {σ : Type.{u1}} {τ : Type.{u2}} {R : Type.{u3}} [_inst_1 : CommSemiring.{u3} R] (f : σ -> τ) (x : τ -> R), Eq.{max (succ u1) (succ u3)} (σ -> R) (MvPolynomial.comap.{u1, u2, u3} σ τ R _inst_1 (MvPolynomial.rename.{u1, u2, u3} σ τ R _inst_1 f) x) (Function.comp.{succ u1, succ u2, succ u3} σ τ R x f)
but is expected to have type
  forall {σ : Type.{u3}} {τ : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] (f : σ -> τ) (x : τ -> R), Eq.{max (succ u3) (succ u2)} (σ -> R) (MvPolynomial.comap.{u3, u1, u2} σ τ R _inst_1 (MvPolynomial.rename.{u3, u1, u2} σ τ R _inst_1 f) x) (Function.comp.{succ u3, succ u1, succ u2} σ τ R x f)
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_rename MvPolynomial.comap_renameₓ'. -/
theorem comap_rename (f : σ → τ) (x : τ → R) : comap (rename f) x = x ∘ f := by ext i;
  simp only [rename_X, comap_apply, aeval_X]
#align mv_polynomial.comap_rename MvPolynomial.comap_rename

#print MvPolynomial.comapEquiv /-
/-- If two polynomial types over the same coefficient ring `R` are equivalent,
there is a bijection between the types of functions from their variable types to `R`.
-/
noncomputable def comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ → R) ≃ (σ → R)
    where
  toFun := comap f
  invFun := comap f.symm
  left_inv := by
    intro x; rw [← comap_comp_apply]; apply comap_eq_id_of_eq_id; intro
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
  right_inv := by
    intro x; rw [← comap_comp_apply]; apply comap_eq_id_of_eq_id; intro
    simp only [AlgHom.id_apply, AlgEquiv.symm_comp]
#align mv_polynomial.comap_equiv MvPolynomial.comapEquiv
-/

/- warning: mv_polynomial.comap_equiv_coe -> MvPolynomial.comapEquiv_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_equiv_coe MvPolynomial.comapEquiv_coeₓ'. -/
@[simp]
theorem comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    (comapEquiv f : (τ → R) → σ → R) = comap f :=
  rfl
#align mv_polynomial.comap_equiv_coe MvPolynomial.comapEquiv_coe

/- warning: mv_polynomial.comap_equiv_symm_coe -> MvPolynomial.comapEquiv_symm_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align mv_polynomial.comap_equiv_symm_coe MvPolynomial.comapEquiv_symm_coeₓ'. -/
@[simp]
theorem comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((comapEquiv f).symm : (σ → R) → τ → R) = comap f.symm :=
  rfl
#align mv_polynomial.comap_equiv_symm_coe MvPolynomial.comapEquiv_symm_coe

end MvPolynomial

