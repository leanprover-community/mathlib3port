/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module linear_algebra.affine_space.basis
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.AffineSpace.Independent
import Mathbin.LinearAlgebra.Basis

/-!
# Affine bases and barycentric coordinates

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

 * `affine_basis`: a structure representing an affine basis of an affine space.
 * `affine_basis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
 * `affine_basis.coord_apply_eq`: the behaviour of `affine_basis.coord i` on `p i`.
 * `affine_basis.coord_apply_ne`: the behaviour of `affine_basis.coord i` on `p j` when `j ≠ i`.
 * `affine_basis.coord_apply`: the behaviour of `affine_basis.coord i` on `p j` for general `j`.
 * `affine_basis.coord_apply_combination`: the characterisation of `affine_basis.coord i` in terms
    of affine combinations, i.e., `affine_basis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

 * Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/


open Affine BigOperators

open Set

universe u₁ u₂ u₃ u₄

#print AffineBasis /-
/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
@[protect_proj]
structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [affine_space V P] [Ring k] [Module k V] where
  toFun : ι → P
  ind' : AffineIndependent k to_fun
  tot' : affineSpan k (range to_fun) = ⊤
#align affine_basis AffineBasis
-/

variable {ι ι' k V P : Type _} [AddCommGroup V] [affine_space V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
instance : Inhabited (AffineBasis PUnit k PUnit) :=
  ⟨⟨id, affineIndependent_of_subsingleton k id, by simp⟩⟩

include V

#print AffineBasis.funLike /-
instance funLike : FunLike (AffineBasis ι k P) ι fun _ => P
    where
  coe := AffineBasis.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
#align affine_basis.fun_like AffineBasis.funLike
-/

/- warning: affine_basis.ext -> AffineBasis.ext is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] {b₁ : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4} {b₂ : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4}, (Eq.{max (succ u1) (succ u4)} ((fun (_x : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) b₁) (coeFn.{max (succ u1) (succ u4), max (succ u1) (succ u4)} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) (FunLike.hasCoeToFun.{max (succ u1) (succ u4), succ u1, succ u4} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => P) (AffineBasis.funLike.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4)) b₁) (coeFn.{max (succ u1) (succ u4), max (succ u1) (succ u4)} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) (FunLike.hasCoeToFun.{max (succ u1) (succ u4), succ u1, succ u4} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => P) (AffineBasis.funLike.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4)) b₂)) -> (Eq.{max (succ u1) (succ u4)} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b₁ b₂)
but is expected to have type
  forall {ι : Type.{u4}} {k : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddCommGroup.{u2} V] [_inst_2 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u2} V _inst_1)] {b₁ : AffineBasis.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4} {b₂ : AffineBasis.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4}, (Eq.{max (succ u4) (succ u1)} (forall (a : ι), (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) a) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (AffineBasis.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) _x) (AffineBasis.funLike.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b₁) (FunLike.coe.{max (succ u4) (succ u1), succ u4, succ u1} (AffineBasis.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) _x) (AffineBasis.funLike.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b₂)) -> (Eq.{max (succ u4) (succ u1)} (AffineBasis.{u4, u3, u2, u1} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b₁ b₂)
Case conversion may be inaccurate. Consider using '#align affine_basis.ext AffineBasis.extₓ'. -/
@[ext]
theorem ext {b₁ b₂ : AffineBasis ι k P} (h : (b₁ : ι → P) = b₂) : b₁ = b₂ :=
  FunLike.coe_injective h
#align affine_basis.ext AffineBasis.ext

/- warning: affine_basis.ind -> AffineBasis.ind is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4), AffineIndependent.{u2, u3, u4, u1} k V P _inst_3 _inst_1 _inst_4 _inst_2 ι (coeFn.{max (succ u1) (succ u4), max (succ u1) (succ u4)} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) (FunLike.hasCoeToFun.{max (succ u1) (succ u4), succ u1, succ u4} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => P) (AffineBasis.funLike.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4)) b)
but is expected to have type
  forall {ι : Type.{u1}} {k : Type.{u4}} {V : Type.{u3}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u2} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u4} k] [_inst_4 : Module.{u4, u3} k V (Ring.toSemiring.{u4} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u4, u3, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4), AffineIndependent.{u4, u3, u2, u1} k V P _inst_3 _inst_1 _inst_4 _inst_2 ι (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (AffineBasis.{u1, u4, u3, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) _x) (AffineBasis.funLike.{u1, u4, u3, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b)
Case conversion may be inaccurate. Consider using '#align affine_basis.ind AffineBasis.indₓ'. -/
theorem ind : AffineIndependent k b :=
  b.ind'
#align affine_basis.ind AffineBasis.ind

/- warning: affine_basis.tot -> AffineBasis.tot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ u4} (AffineSubspace.{u2, u3, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2) (affineSpan.{u2, u3, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2 (Set.range.{u4, succ u1} P ι (coeFn.{max (succ u1) (succ u4), max (succ u1) (succ u4)} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) (FunLike.hasCoeToFun.{max (succ u1) (succ u4), succ u1, succ u4} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => P) (AffineBasis.funLike.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4)) b))) (Top.top.{u4} (AffineSubspace.{u2, u3, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2) (CompleteLattice.toHasTop.{u4} (AffineSubspace.{u2, u3, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2) (AffineSubspace.completeLattice.{u2, u3, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2)))
but is expected to have type
  forall {ι : Type.{u1}} {k : Type.{u3}} {V : Type.{u2}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u2} V] [_inst_2 : AddTorsor.{u2, u4} V P (AddCommGroup.toAddGroup.{u2} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u2} V _inst_1)] (b : AffineBasis.{u1, u3, u2, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{succ u4} (AffineSubspace.{u3, u2, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2) (affineSpan.{u3, u2, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2 (Set.range.{u4, succ u1} P ι (FunLike.coe.{max (succ u1) (succ u4), succ u1, succ u4} (AffineBasis.{u1, u3, u2, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) _x) (AffineBasis.funLike.{u1, u3, u2, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b))) (Top.top.{u4} (AffineSubspace.{u3, u2, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2) (CompleteLattice.toTop.{u4} (AffineSubspace.{u3, u2, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2) (AffineSubspace.instCompleteLatticeAffineSubspace.{u3, u2, u4} k V P _inst_3 _inst_1 _inst_4 _inst_2)))
Case conversion may be inaccurate. Consider using '#align affine_basis.tot AffineBasis.totₓ'. -/
theorem tot : affineSpan k (range b) = ⊤ :=
  b.tot'
#align affine_basis.tot AffineBasis.tot

include b

#print AffineBasis.nonempty /-
protected theorem nonempty : Nonempty ι :=
  not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot
#align affine_basis.nonempty AffineBasis.nonempty
-/

#print AffineBasis.reindex /-
/-- Composition of an affine basis and an equivalence of index types. -/
def reindex (e : ι ≃ ι') : AffineBasis ι' k P :=
  ⟨b ∘ e.symm, b.ind.comp_embedding e.symm.toEmbedding,
    by
    rw [e.symm.surjective.range_comp]
    exact b.3⟩
#align affine_basis.reindex AffineBasis.reindex
-/

/- warning: affine_basis.coe_reindex -> AffineBasis.coe_reindex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {k : Type.{u3}} {V : Type.{u4}} {P : Type.{u5}} [_inst_1 : AddCommGroup.{u4} V] [_inst_2 : AddTorsor.{u4, u5} V P (AddCommGroup.toAddGroup.{u4} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u4} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u4} V _inst_1)] (b : AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (e : Equiv.{succ u1, succ u2} ι ι'), Eq.{max (succ u2) (succ u5)} (ι' -> P) (coeFn.{max (succ u2) (succ u5), max (succ u2) (succ u5)} (AffineBasis.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι' -> P) (FunLike.hasCoeToFun.{max (succ u2) (succ u5), succ u2, succ u5} (AffineBasis.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) ι' (fun (_x : ι') => P) (AffineBasis.funLike.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4)) (AffineBasis.reindex.{u1, u2, u3, u4, u5} ι ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 b e)) (Function.comp.{succ u2, succ u1, succ u5} ι' ι P (coeFn.{max (succ u1) (succ u5), max (succ u1) (succ u5)} (AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) (FunLike.hasCoeToFun.{max (succ u1) (succ u5), succ u1, succ u5} (AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => P) (AffineBasis.funLike.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4)) b) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e)))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u5}} {k : Type.{u3}} {V : Type.{u2}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u2} V] [_inst_2 : AddTorsor.{u2, u4} V P (AddCommGroup.toAddGroup.{u2} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u2} V _inst_1)] (b : AffineBasis.{u1, u3, u2, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (e : Equiv.{succ u1, succ u5} ι ι'), Eq.{max (succ u5) (succ u4)} (forall (a : ι'), (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι') => P) a) (FunLike.coe.{max (succ u5) (succ u4), succ u5, succ u4} (AffineBasis.{u5, u3, u2, u4} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι') => P) _x) (AffineBasis.funLike.{u5, u3, u2, u4} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineBasis.reindex.{u1, u5, u3, u2, u4} ι ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 b e)) (Function.comp.{succ u5, succ u1, succ u4} ι' ι P (FunLike.coe.{max (succ u1) (succ u4), succ u1, succ u4} (AffineBasis.{u1, u3, u2, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) _x) (AffineBasis.funLike.{u1, u3, u2, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b) (FunLike.coe.{max (succ u1) (succ u5), succ u5, succ u1} (Equiv.{succ u5, succ u1} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u5, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u5} ι ι' e)))
Case conversion may be inaccurate. Consider using '#align affine_basis.coe_reindex AffineBasis.coe_reindexₓ'. -/
@[simp, norm_cast]
theorem coe_reindex : ⇑(b.reindex e) = b ∘ e.symm :=
  rfl
#align affine_basis.coe_reindex AffineBasis.coe_reindex

/- warning: affine_basis.reindex_apply -> AffineBasis.reindex_apply is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {k : Type.{u3}} {V : Type.{u4}} {P : Type.{u5}} [_inst_1 : AddCommGroup.{u4} V] [_inst_2 : AddTorsor.{u4, u5} V P (AddCommGroup.toAddGroup.{u4} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u4} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u4} V _inst_1)] (b : AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (e : Equiv.{succ u1, succ u2} ι ι') (i' : ι'), Eq.{succ u5} P (coeFn.{max (succ u2) (succ u5), max (succ u2) (succ u5)} (AffineBasis.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι' -> P) (FunLike.hasCoeToFun.{max (succ u2) (succ u5), succ u2, succ u5} (AffineBasis.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) ι' (fun (_x : ι') => P) (AffineBasis.funLike.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4)) (AffineBasis.reindex.{u1, u2, u3, u4, u5} ι ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 b e) i') (coeFn.{max (succ u1) (succ u5), max (succ u1) (succ u5)} (AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (fun (_x : AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) => ι -> P) (FunLike.hasCoeToFun.{max (succ u1) (succ u5), succ u1, succ u5} (AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => P) (AffineBasis.funLike.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4)) b (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e) i'))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u4}} {k : Type.{u3}} {V : Type.{u2}} {P : Type.{u5}} [_inst_1 : AddCommGroup.{u2} V] [_inst_2 : AddTorsor.{u2, u5} V P (AddCommGroup.toAddGroup.{u2} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u2} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u2} V _inst_1)] (b : AffineBasis.{u1, u3, u2, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (e : Equiv.{succ u1, succ u4} ι ι') (i' : ι'), Eq.{succ u5} ((fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι') => P) i') (FunLike.coe.{max (succ u4) (succ u5), succ u4, succ u5} (AffineBasis.{u4, u3, u2, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) ι' (fun (_x : ι') => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι') => P) _x) (AffineBasis.funLike.{u4, u3, u2, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineBasis.reindex.{u1, u4, u3, u2, u5} ι ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 b e) i') (FunLike.coe.{max (succ u1) (succ u5), succ u1, succ u5} (AffineBasis.{u1, u3, u2, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) ι (fun (_x : ι) => (fun (x._@.Mathlib.LinearAlgebra.AffineSpace.Basis._hyg.252 : ι) => P) _x) (AffineBasis.funLike.{u1, u3, u2, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) b (FunLike.coe.{max (succ u1) (succ u4), succ u4, succ u1} (Equiv.{succ u4, succ u1} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u4, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u4} ι ι' e) i'))
Case conversion may be inaccurate. Consider using '#align affine_basis.reindex_apply AffineBasis.reindex_applyₓ'. -/
@[simp]
theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  rfl
#align affine_basis.reindex_apply AffineBasis.reindex_apply

/- warning: affine_basis.reindex_refl -> AffineBasis.reindex_refl is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{max (succ u1) (succ u4)} (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineBasis.reindex.{u1, u1, u2, u3, u4} ι ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b (Equiv.refl.{succ u1} ι)) b
but is expected to have type
  forall {ι : Type.{u4}} {k : Type.{u2}} {V : Type.{u1}} {P : Type.{u3}} [_inst_1 : AddCommGroup.{u1} V] [_inst_2 : AddTorsor.{u1, u3} V P (AddCommGroup.toAddGroup.{u1} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u1} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u1} V _inst_1)] (b : AffineBasis.{u4, u2, u1, u3} ι k V P _inst_1 _inst_2 _inst_3 _inst_4), Eq.{max (succ u4) (succ u3)} (AffineBasis.{u4, u2, u1, u3} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (AffineBasis.reindex.{u4, u4, u2, u1, u3} ι ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b (Equiv.refl.{succ u4} ι)) b
Case conversion may be inaccurate. Consider using '#align affine_basis.reindex_refl AffineBasis.reindex_reflₓ'. -/
@[simp]
theorem reindex_refl : b.reindex (Equiv.refl _) = b :=
  ext rfl
#align affine_basis.reindex_refl AffineBasis.reindex_refl

#print AffineBasis.basisOf /-
/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis corresponding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `b j -ᵥ b i`. (See `basis_of_apply`.) -/
noncomputable def basisOf (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affineIndependent_iff_linearIndependent_vsub k b i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x ≠ i } => b ↑j -ᵥ b i) = vectorSpan k (range b)
        by
        rw [this, ← direction_affineSpan, b.tot, AffineSubspace.direction_top]
        exact le_rfl
      conv_rhs => rw [← image_univ]
      rw [vectorSpan_image_eq_span_vsub_set_right_ne k b (mem_univ i)]
      congr
      ext v
      simp)
#align affine_basis.basis_of AffineBasis.basisOf
-/

/- warning: affine_basis.basis_of_apply -> AffineBasis.basisOf_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.basis_of_apply AffineBasis.basisOf_applyₓ'. -/
@[simp]
theorem basisOf_apply (i : ι) (j : { j : ι // j ≠ i }) : b.basisOf i j = b ↑j -ᵥ b i := by
  simp [basis_of]
#align affine_basis.basis_of_apply AffineBasis.basisOf_apply

/- warning: affine_basis.basis_of_reindex -> AffineBasis.basisOf_reindex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.basis_of_reindex AffineBasis.basisOf_reindexₓ'. -/
@[simp]
theorem basisOf_reindex (i : ι') :
    (b.reindex e).basisOf i =
      (b.basisOf <| e.symm i).reindex (e.subtypeEquiv fun _ => e.eq_symm_apply.Not) :=
  by
  ext j
  simp
#align affine_basis.basis_of_reindex AffineBasis.basisOf_reindex

/- warning: affine_basis.coord -> AffineBasis.coord is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)], (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) -> ι -> (AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3)))))
but is expected to have type
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)], (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) -> ι -> (AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u2} k _inst_3) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (Ring.toAddGroupWithOne.{u2} k _inst_3))))
Case conversion may be inaccurate. Consider using '#align affine_basis.coord AffineBasis.coordₓ'. -/
/-- The `i`th barycentric coordinate of a point. -/
noncomputable def coord (i : ι) : P →ᵃ[k] k
    where
  toFun q := 1 - (b.basisOf i).sumCoords (q -ᵥ b i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc, LinearMap.map_add, vadd_eq_add, LinearMap.neg_apply,
      sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg]
#align affine_basis.coord AffineBasis.coord

/- warning: affine_basis.linear_eq_sum_coords -> AffineBasis.linear_eq_sumCoords is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (i : ι), Eq.{max (succ u3) (succ u2)} (LinearMap.{u2, u2, u3, u2} k k (Ring.toSemiring.{u2} k _inst_3) (Ring.toSemiring.{u2} k _inst_3) (RingHom.id.{u2} k (Semiring.toNonAssocSemiring.{u2} k (Ring.toSemiring.{u2} k _inst_3))) V k (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) (AddCommGroup.toAddCommMonoid.{u2} k (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3)))) _inst_4 (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3))) (AffineMap.linear.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3)))) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) (Neg.neg.{max u3 u2} (LinearMap.{u2, u2, u3, u2} k k (Ring.toSemiring.{u2} k _inst_3) (Ring.toSemiring.{u2} k _inst_3) (RingHom.id.{u2} k (Semiring.toNonAssocSemiring.{u2} k (Ring.toSemiring.{u2} k _inst_3))) V k (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) (AddCommGroup.toAddCommMonoid.{u2} k (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3)))) _inst_4 (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3))) (LinearMap.hasNeg.{u2, u2, u3, u2} k k V k (Ring.toSemiring.{u2} k _inst_3) (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) _inst_4 (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (RingHom.id.{u2} k (Semiring.toNonAssocSemiring.{u2} k (Ring.toSemiring.{u2} k _inst_3)))) (Basis.sumCoords.{u1, u2, u3} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) _inst_4 (AffineBasis.basisOf.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)))
but is expected to have type
  forall {ι : Type.{u1}} {k : Type.{u4}} {V : Type.{u3}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u2} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u4} k] [_inst_4 : Module.{u4, u3} k V (Ring.toSemiring.{u4} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u4, u3, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (i : ι), Eq.{max (succ u4) (succ u3)} (LinearMap.{u4, u4, u3, u4} k k (Ring.toSemiring.{u4} k _inst_3) (Ring.toSemiring.{u4} k _inst_3) (RingHom.id.{u4} k (Semiring.toNonAssocSemiring.{u4} k (Ring.toSemiring.{u4} k _inst_3))) V k (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) (AddCommGroup.toAddCommMonoid.{u4} k (Ring.toAddCommGroup.{u4} k _inst_3)) _inst_4 (Semiring.toModule.{u4} k (Ring.toSemiring.{u4} k _inst_3))) (AffineMap.linear.{u4, u3, u2, u4, u4} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u4} k _inst_3) (Semiring.toModule.{u4} k (Ring.toSemiring.{u4} k _inst_3)) (addGroupIsAddTorsor.{u4} k (AddGroupWithOne.toAddGroup.{u4} k (Ring.toAddGroupWithOne.{u4} k _inst_3))) (AffineBasis.coord.{u1, u4, u3, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) (Neg.neg.{max u4 u3} (LinearMap.{u4, u4, u3, u4} k k (Ring.toSemiring.{u4} k _inst_3) (Ring.toSemiring.{u4} k _inst_3) (RingHom.id.{u4} k (Semiring.toNonAssocSemiring.{u4} k (Ring.toSemiring.{u4} k _inst_3))) V k (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u4} k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u4} k (Semiring.toNonAssocSemiring.{u4} k (Ring.toSemiring.{u4} k _inst_3)))) _inst_4 (Semiring.toModule.{u4} k (Ring.toSemiring.{u4} k _inst_3))) (LinearMap.instNegLinearMapToAddCommMonoid.{u4, u4, u3, u4} k k V k (Ring.toSemiring.{u4} k _inst_3) (Ring.toSemiring.{u4} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) (Ring.toAddCommGroup.{u4} k _inst_3) _inst_4 (Semiring.toModule.{u4} k (Ring.toSemiring.{u4} k _inst_3)) (RingHom.id.{u4} k (Semiring.toNonAssocSemiring.{u4} k (Ring.toSemiring.{u4} k _inst_3)))) (Basis.sumCoords.{u1, u4, u3} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) k V (Ring.toSemiring.{u4} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1) _inst_4 (AffineBasis.basisOf.{u1, u4, u3, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)))
Case conversion may be inaccurate. Consider using '#align affine_basis.linear_eq_sum_coords AffineBasis.linear_eq_sumCoordsₓ'. -/
@[simp]
theorem linear_eq_sumCoords (i : ι) : (b.Coord i).linear = -(b.basisOf i).sumCoords :=
  rfl
#align affine_basis.linear_eq_sum_coords AffineBasis.linear_eq_sumCoords

/- warning: affine_basis.coord_reindex -> AffineBasis.coord_reindex is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {k : Type.{u3}} {V : Type.{u4}} {P : Type.{u5}} [_inst_1 : AddCommGroup.{u4} V] [_inst_2 : AddTorsor.{u4, u5} V P (AddCommGroup.toAddGroup.{u4} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u4} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u4} V _inst_1)] (b : AffineBasis.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (e : Equiv.{succ u1, succ u2} ι ι') (i : ι'), Eq.{max (succ u4) (succ u5) (succ u3)} (AffineMap.{u3, u4, u5, u3, u3} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u3} k (NonAssocRing.toNonUnitalNonAssocRing.{u3} k (Ring.toNonAssocRing.{u3} k _inst_3))) (Semiring.toModule.{u3} k (Ring.toSemiring.{u3} k _inst_3)) (addGroupIsAddTorsor.{u3} k (AddGroupWithOne.toAddGroup.{u3} k (AddCommGroupWithOne.toAddGroupWithOne.{u3} k (Ring.toAddCommGroupWithOne.{u3} k _inst_3))))) (AffineBasis.coord.{u2, u3, u4, u5} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 (AffineBasis.reindex.{u1, u2, u3, u4, u5} ι ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 b e) i) (AffineBasis.coord.{u1, u3, u4, u5} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} ι' ι) (fun (_x : Equiv.{succ u2, succ u1} ι' ι) => ι' -> ι) (Equiv.hasCoeToFun.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e) i))
but is expected to have type
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {k : Type.{u5}} {V : Type.{u4}} {P : Type.{u3}} [_inst_1 : AddCommGroup.{u4} V] [_inst_2 : AddTorsor.{u4, u3} V P (AddCommGroup.toAddGroup.{u4} V _inst_1)] [_inst_3 : Ring.{u5} k] [_inst_4 : Module.{u5, u4} k V (Ring.toSemiring.{u5} k _inst_3) (AddCommGroup.toAddCommMonoid.{u4} V _inst_1)] (b : AffineBasis.{u1, u5, u4, u3} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) (e : Equiv.{succ u1, succ u2} ι ι') (i : ι'), Eq.{max (max (succ u5) (succ u4)) (succ u3)} (AffineMap.{u5, u4, u3, u5, u5} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u5} k _inst_3) (Semiring.toModule.{u5} k (Ring.toSemiring.{u5} k _inst_3)) (addGroupIsAddTorsor.{u5} k (AddGroupWithOne.toAddGroup.{u5} k (Ring.toAddGroupWithOne.{u5} k _inst_3)))) (AffineBasis.coord.{u2, u5, u4, u3} ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 (AffineBasis.reindex.{u1, u2, u5, u4, u3} ι ι' k V P _inst_1 _inst_2 _inst_3 _inst_4 b e) i) (AffineBasis.coord.{u1, u5, u4, u3} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (Equiv.{succ u2, succ u1} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : ι') => ι) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} ι' ι) (Equiv.symm.{succ u1, succ u2} ι ι' e) i))
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_reindex AffineBasis.coord_reindexₓ'. -/
@[simp]
theorem coord_reindex (i : ι') : (b.reindex e).Coord i = b.Coord (e.symm i) :=
  by
  ext
  classical simp [AffineBasis.coord]
#align affine_basis.coord_reindex AffineBasis.coord_reindex

/- warning: affine_basis.coord_apply_eq -> AffineBasis.coord_apply_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_apply_eq AffineBasis.coord_apply_eqₓ'. -/
@[simp]
theorem coord_apply_eq (i : ι) : b.Coord i (b i) = 1 := by
  simp only [coord, Basis.coe_sumCoords, LinearEquiv.map_zero, LinearEquiv.coe_coe, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]
#align affine_basis.coord_apply_eq AffineBasis.coord_apply_eq

/- warning: affine_basis.coord_apply_ne -> AffineBasis.coord_apply_ne is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_apply_ne AffineBasis.coord_apply_neₓ'. -/
@[simp]
theorem coord_apply_ne (h : i ≠ j) : b.Coord i (b j) = 0 := by
  rw [coord, AffineMap.coe_mk, ← Subtype.coe_mk j h.symm, ← b.basis_of_apply,
    Basis.sumCoords_self_apply, sub_self]
#align affine_basis.coord_apply_ne AffineBasis.coord_apply_ne

/- warning: affine_basis.coord_apply -> AffineBasis.coord_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_apply AffineBasis.coord_applyₓ'. -/
theorem coord_apply [DecidableEq ι] (i j : ι) : b.Coord i (b j) = if i = j then 1 else 0 := by
  cases eq_or_ne i j <;> simp [h]
#align affine_basis.coord_apply AffineBasis.coord_apply

/- warning: affine_basis.coord_apply_combination_of_mem -> AffineBasis.coord_apply_combination_of_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_apply_combination_of_mem AffineBasis.coord_apply_combination_of_memₓ'. -/
@[simp]
theorem coord_apply_combination_of_mem (hi : i ∈ s) {w : ι → k} (hw : s.Sum w = 1) :
    b.Coord i (s.affineCombination k b w) = w i := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affine_combination b w hw]
#align affine_basis.coord_apply_combination_of_mem AffineBasis.coord_apply_combination_of_mem

/- warning: affine_basis.coord_apply_combination_of_not_mem -> AffineBasis.coord_apply_combination_of_not_mem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_apply_combination_of_not_mem AffineBasis.coord_apply_combination_of_not_memₓ'. -/
@[simp]
theorem coord_apply_combination_of_not_mem (hi : i ∉ s) {w : ι → k} (hw : s.Sum w = 1) :
    b.Coord i (s.affineCombination k b w) = 0 := by
  classical simp only [coord_apply, hi, Finset.affineCombination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affine_combination b w hw]
#align affine_basis.coord_apply_combination_of_not_mem AffineBasis.coord_apply_combination_of_not_mem

/- warning: affine_basis.sum_coord_apply_eq_one -> AffineBasis.sum_coord_apply_eq_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.sum_coord_apply_eq_one AffineBasis.sum_coord_apply_eq_oneₓ'. -/
@[simp]
theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : (∑ i, b.Coord i q) = 1 :=
  by
  have hq : q ∈ affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  convert hw
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
#align affine_basis.sum_coord_apply_eq_one AffineBasis.sum_coord_apply_eq_one

/- warning: affine_basis.affine_combination_coord_eq_self -> AffineBasis.affineCombination_coord_eq_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.affine_combination_coord_eq_self AffineBasis.affineCombination_coord_eq_selfₓ'. -/
@[simp]
theorem affineCombination_coord_eq_self [Fintype ι] (q : P) :
    (Finset.univ.affineCombination k b fun i => b.Coord i q) = q :=
  by
  have hq : q ∈ affineSpan k (range b) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
#align affine_basis.affine_combination_coord_eq_self AffineBasis.affineCombination_coord_eq_self

/- warning: affine_basis.linear_combination_coord_eq_self -> AffineBasis.linear_combination_coord_eq_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.linear_combination_coord_eq_self AffineBasis.linear_combination_coord_eq_selfₓ'. -/
/-- A variant of `affine_basis.affine_combination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp]
theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    (∑ i, b.Coord i v • b i) = v :=
  by
  have hb := b.affine_combination_coord_eq_self v
  rwa [finset.univ.affine_combination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb
#align affine_basis.linear_combination_coord_eq_self AffineBasis.linear_combination_coord_eq_self

/- warning: affine_basis.ext_elem -> AffineBasis.ext_elem is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.ext_elem AffineBasis.ext_elemₓ'. -/
theorem ext_elem [Finite ι] {q₁ q₂ : P} (h : ∀ i, b.Coord i q₁ = b.Coord i q₂) : q₁ = q₂ :=
  by
  cases nonempty_fintype ι
  rw [← b.affine_combination_coord_eq_self q₁, ← b.affine_combination_coord_eq_self q₂]
  simp only [h]
#align affine_basis.ext_elem AffineBasis.ext_elem

/- warning: affine_basis.coe_coord_of_subsingleton_eq_one -> AffineBasis.coe_coord_of_subsingleton_eq_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) [_inst_5 : Subsingleton.{succ u1} ι] (i : ι), Eq.{max (succ u4) (succ u2)} ((fun (_x : AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) => P -> k) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) (coeFn.{max (succ u3) (succ u4) (succ u2), max (succ u4) (succ u2)} (AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) (fun (_x : AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) => P -> k) (AffineMap.hasCoeToFun.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) (OfNat.ofNat.{max u4 u2} ((fun (_x : AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) => P -> k) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) 1 (OfNat.mk.{max u4 u2} ((fun (_x : AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) => P -> k) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) 1 (One.one.{max u4 u2} ((fun (_x : AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) => P -> k) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) (Pi.instOne.{u4, u2} P (fun (ᾰ : P) => k) (fun (i : P) => AddMonoidWithOne.toOne.{u2} k (AddGroupWithOne.toAddMonoidWithOne.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))))))
but is expected to have type
  forall {ι : Type.{u4}} {k : Type.{u3}} {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u1} V] [_inst_2 : AddTorsor.{u1, u2} V P (AddCommGroup.toAddGroup.{u1} V _inst_1)] [_inst_3 : Ring.{u3} k] [_inst_4 : Module.{u3, u1} k V (Ring.toSemiring.{u3} k _inst_3) (AddCommGroup.toAddCommMonoid.{u1} V _inst_1)] (b : AffineBasis.{u4, u3, u1, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) [_inst_5 : Subsingleton.{succ u4} ι] (i : ι), Eq.{max (succ u3) (succ u2)} (forall (a : P), (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) a) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u2, succ u3} (AffineMap.{u3, u1, u2, u3, u3} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u3} k _inst_3) (Semiring.toModule.{u3} k (Ring.toSemiring.{u3} k _inst_3)) (addGroupIsAddTorsor.{u3} k (AddGroupWithOne.toAddGroup.{u3} k (Ring.toAddGroupWithOne.{u3} k _inst_3)))) P (fun (_x : P) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) _x) (AffineMap.funLike.{u3, u1, u2, u3, u3} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u3} k _inst_3) (Semiring.toModule.{u3} k (Ring.toSemiring.{u3} k _inst_3)) (addGroupIsAddTorsor.{u3} k (AddGroupWithOne.toAddGroup.{u3} k (Ring.toAddGroupWithOne.{u3} k _inst_3)))) (AffineBasis.coord.{u4, u3, u1, u2} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i)) (OfNat.ofNat.{max u3 u2} (forall (a : P), (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) a) 1 (One.toOfNat1.{max u3 u2} (forall (a : P), (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) a) (Pi.instOne.{u2, u3} P (fun (a : P) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) a) (fun (i : P) => Semiring.toOne.{u3} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) i) (Ring.toSemiring.{u3} ((fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) i) _inst_3)))))
Case conversion may be inaccurate. Consider using '#align affine_basis.coe_coord_of_subsingleton_eq_one AffineBasis.coe_coord_of_subsingleton_eq_oneₓ'. -/
@[simp]
theorem coe_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) : (b.Coord i : P → k) = 1 :=
  by
  ext q
  have hp : (range b).Subsingleton := by
    rw [← image_univ]
    apply subsingleton.image
    apply subsingleton_of_subsingleton
  haveI := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i ∈ s := by simp
  have hw : s.sum (Function.const ι (1 : k)) = 1 := by simp
  have hq : q = s.affine_combination k b (Function.const ι (1 : k)) := by simp
  rw [Pi.one_apply, hq, b.coord_apply_combination_of_mem hi hw]
#align affine_basis.coe_coord_of_subsingleton_eq_one AffineBasis.coe_coord_of_subsingleton_eq_one

/- warning: affine_basis.surjective_coord -> AffineBasis.surjective_coord is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)] (b : AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) [_inst_5 : Nontrivial.{u1} ι] (i : ι), Function.Surjective.{succ u4, succ u2} P k (coeFn.{max (succ u3) (succ u4) (succ u2), max (succ u4) (succ u2)} (AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) (fun (_x : AffineMap.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) => P -> k) (AffineMap.hasCoeToFun.{u2, u3, u4, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3))) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))) (AffineBasis.coord.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i))
but is expected to have type
  forall {ι : Type.{u4}} {k : Type.{u2}} {V : Type.{u1}} {P : Type.{u3}} [_inst_1 : AddCommGroup.{u1} V] [_inst_2 : AddTorsor.{u1, u3} V P (AddCommGroup.toAddGroup.{u1} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u1} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u1} V _inst_1)] (b : AffineBasis.{u4, u2, u1, u3} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) [_inst_5 : Nontrivial.{u4} ι] (i : ι), Function.Surjective.{succ u3, succ u2} P k (FunLike.coe.{max (max (succ u1) (succ u3)) (succ u2), succ u3, succ u2} (AffineMap.{u2, u1, u3, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u2} k _inst_3) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (Ring.toAddGroupWithOne.{u2} k _inst_3)))) P (fun (_x : P) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : P) => k) _x) (AffineMap.funLike.{u2, u1, u3, u2, u2} k V P k k _inst_3 _inst_1 _inst_4 _inst_2 (Ring.toAddCommGroup.{u2} k _inst_3) (Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3)) (addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (Ring.toAddGroupWithOne.{u2} k _inst_3)))) (AffineBasis.coord.{u4, u2, u1, u3} ι k V P _inst_1 _inst_2 _inst_3 _inst_4 b i))
Case conversion may be inaccurate. Consider using '#align affine_basis.surjective_coord AffineBasis.surjective_coordₓ'. -/
theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.Coord i := by
  classical
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i ∈ s := by simp
    have hj : j ∈ s := by simp
    let w : ι → k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [hij, Finset.sum_ite, Finset.filter_insert, Finset.filter_eq']
    use s.affine_combination k b w
    simp [b.coord_apply_combination_of_mem hi hw]
#align affine_basis.surjective_coord AffineBasis.surjective_coord

/- warning: affine_basis.coords -> AffineBasis.coords is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)], (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) -> (AffineMap.{u2, u3, u4, max u1 u2, max u1 u2} k V P (ι -> k) (ι -> k) _inst_3 _inst_1 _inst_4 _inst_2 (Pi.addCommGroup.{u1, u2} ι (fun (i : ι) => k) (fun (i : ι) => NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3)))) (Pi.module.{u1, u2, u2} ι (fun (i : ι) => k) k (Ring.toSemiring.{u2} k _inst_3) (fun (i : ι) => AddCommGroup.toAddCommMonoid.{u2} k (NonUnitalNonAssocRing.toAddCommGroup.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3)))) (fun (i : ι) => Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3))) (Pi.addTorsor.{u1, u2, u2} ι (fun (i : ι) => k) (fun (i : ι) => AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))) (fun (ᾰ : ι) => k) (fun (i : ι) => addGroupIsAddTorsor.{u2} k (AddGroupWithOne.toAddGroup.{u2} k (AddCommGroupWithOne.toAddGroupWithOne.{u2} k (Ring.toAddCommGroupWithOne.{u2} k _inst_3))))))
but is expected to have type
  forall {ι : Type.{u1}} {k : Type.{u2}} {V : Type.{u3}} {P : Type.{u4}} [_inst_1 : AddCommGroup.{u3} V] [_inst_2 : AddTorsor.{u3, u4} V P (AddCommGroup.toAddGroup.{u3} V _inst_1)] [_inst_3 : Ring.{u2} k] [_inst_4 : Module.{u2, u3} k V (Ring.toSemiring.{u2} k _inst_3) (AddCommGroup.toAddCommMonoid.{u3} V _inst_1)], (AffineBasis.{u1, u2, u3, u4} ι k V P _inst_1 _inst_2 _inst_3 _inst_4) -> (AffineMap.{u2, u3, u4, max u1 u2, max u1 u2} k V P (ι -> k) (ι -> k) _inst_3 _inst_1 _inst_4 _inst_2 (Pi.addCommGroup.{u1, u2} ι (fun (i : ι) => k) (fun (i : ι) => Ring.toAddCommGroup.{u2} k _inst_3)) (Pi.module.{u1, u2, u2} ι (fun (i : ι) => k) k (Ring.toSemiring.{u2} k _inst_3) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} k (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} k (NonAssocRing.toNonUnitalNonAssocRing.{u2} k (Ring.toNonAssocRing.{u2} k _inst_3)))) (fun (i : ι) => Semiring.toModule.{u2} k (Ring.toSemiring.{u2} k _inst_3))) (Finset.instAddTorsorForAllAddGroupToAddGroupToAddGroupWithOne.{u2, u1} k _inst_3 ι))
Case conversion may be inaccurate. Consider using '#align affine_basis.coords AffineBasis.coordsₓ'. -/
/-- Barycentric coordinates as an affine map. -/
noncomputable def coords : P →ᵃ[k] ι → k
    where
  toFun q i := b.Coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by
        ext i
        simp only [LinearMap.map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by
        ext i
        simpa only [LinearMap.map_smul, Pi.smul_apply, smul_neg] }
  map_vadd' p v := by
    ext i
    simp only [linear_eq_sum_coords, LinearMap.coe_mk, LinearMap.neg_apply, Pi.vadd_apply',
      AffineMap.map_vadd]
#align affine_basis.coords AffineBasis.coords

/- warning: affine_basis.coords_apply -> AffineBasis.coords_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coords_apply AffineBasis.coords_applyₓ'. -/
@[simp]
theorem coords_apply (q : P) (i : ι) : b.coords q i = b.Coord i q :=
  rfl
#align affine_basis.coords_apply AffineBasis.coords_apply

end Ring

section DivisionRing

variable [DivisionRing k] [Module k V]

include V

/- warning: affine_basis.coord_apply_centroid -> AffineBasis.coord_apply_centroid is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.coord_apply_centroid AffineBasis.coord_apply_centroidₓ'. -/
@[simp]
theorem coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
    (hi : i ∈ s) : b.Coord i (s.centroid k b) = (s.card : k)⁻¹ := by
  rw [Finset.centroid,
    b.coord_apply_combination_of_mem hi (s.sum_centroid_weights_eq_one_of_nonempty _ ⟨i, hi⟩),
    Finset.centroidWeights]
#align affine_basis.coord_apply_centroid AffineBasis.coord_apply_centroid

/- warning: affine_basis.exists_affine_subbasis -> AffineBasis.exists_affine_subbasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.exists_affine_subbasis AffineBasis.exists_affine_subbasisₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (s «expr ⊆ » t) -/
theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    ∃ (s : _)(_ : s ⊆ t)(b : AffineBasis (↥s) k P), ⇑b = coe :=
  by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affineIndependent k V t
  refine' ⟨s, hst, ⟨coe, h_ind, _⟩, rfl⟩
  rw [Subtype.range_coe, h_tot, ht]
#align affine_basis.exists_affine_subbasis AffineBasis.exists_affine_subbasis

variable (k V P)

/- warning: affine_basis.exists_affine_basis -> AffineBasis.exists_affineBasis is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_basis.exists_affine_basis AffineBasis.exists_affineBasisₓ'. -/
theorem exists_affineBasis : ∃ (s : Set P)(b : AffineBasis (↥s) k P), ⇑b = coe :=
  let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩
#align affine_basis.exists_affine_basis AffineBasis.exists_affineBasis

end DivisionRing

end AffineBasis

