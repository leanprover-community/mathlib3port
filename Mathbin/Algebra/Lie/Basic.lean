/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module algebra.lie.basic
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Equiv
import Mathbin.Data.Bracket
import Mathbin.LinearAlgebra.Basic
import Mathbin.Tactic.NoncommRing

/-!
# Lie algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `lie_ring`
  * `lie_algebra`
  * `lie_ring_module`
  * `lie_module`
  * `lie_hom`
  * `lie_equiv`
  * `lie_module_hom`
  * `lie_module_equiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tags

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/


universe u v w w₁ w₂

open Function

#print LieRing /-
/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. -/
@[protect_proj]
class LieRing (L : Type v) extends AddCommGroup L, Bracket L L where
  add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  lie_self : ∀ x : L, ⁅x, x⁆ = 0
  leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
#align lie_ring LieRing
-/

#print LieAlgebra /-
/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[protect_proj]
class LieAlgebra (R : Type u) (L : Type v) [CommRing R] [LieRing L] extends Module R L where
  lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆
#align lie_algebra LieAlgebra
-/

#print LieRingModule /-
/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `lie_module`.) -/
@[protect_proj]
class LieRingModule (L : Type v) (M : Type w) [LieRing L] [AddCommGroup M] extends Bracket L M where
  add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
#align lie_ring_module LieRingModule
-/

#print LieModule /-
/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
@[protect_proj]
class LieModule (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] where
  smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
  lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆
#align lie_module LieModule
-/

section BasicProperties

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

/- warning: add_lie -> add_lie is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (HAdd.hAdd.{u1, u1, u1} L L L (instHAdd.{u1} L (AddZeroClass.toHasAdd.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))) x y) m) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (HAdd.hAdd.{u1, u1, u1} L L L (instHAdd.{u1} L (AddZeroClass.toAdd.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))) x y) m) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m))
Case conversion may be inaccurate. Consider using '#align add_lie add_lieₓ'. -/
@[simp]
theorem add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ :=
  LieRingModule.add_lie x y m
#align add_lie add_lie

/- warning: lie_add -> lie_add is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M) (n : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) m n)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x n))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M) (n : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) m n)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x n))
Case conversion may be inaccurate. Consider using '#align lie_add lie_addₓ'. -/
@[simp]
theorem lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ :=
  LieRingModule.lie_add x m n
#align lie_add lie_add

#print smul_lie /-
@[simp]
theorem smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ :=
  LieModule.smul_lie t x m
#align smul_lie smul_lie
-/

#print lie_smul /-
@[simp]
theorem lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ :=
  LieModule.lie_smul t x m
#align lie_smul lie_smul
-/

/- warning: leibniz_lie -> leibniz_lie is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (Bracket.bracket.{u1, u1} L L (LieRing.toHasBracket.{u1} L _inst_2) x y) m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m)))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (Bracket.bracket.{u1, u1} L L (LieRing.toBracket.{u1} L _inst_2) x y) m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m)))
Case conversion may be inaccurate. Consider using '#align leibniz_lie leibniz_lieₓ'. -/
theorem leibniz_lie : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ :=
  LieRingModule.leibniz_lie x y m
#align leibniz_lie leibniz_lie

/- warning: lie_zero -> lie_zero is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))))))))) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))))))))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4)))))))) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4)))))))
Case conversion may be inaccurate. Consider using '#align lie_zero lie_zeroₓ'. -/
@[simp]
theorem lie_zero : ⁅x, 0⁆ = (0 : M) :=
  (AddMonoidHom.mk' _ (lie_add x)).map_zero
#align lie_zero lie_zero

/- warning: zero_lie -> zero_lie is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (OfNat.ofNat.{u1} L 0 (OfNat.mk.{u1} L 0 (Zero.zero.{u1} L (AddZeroClass.toHasZero.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))))) m) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (SubNegMonoid.toAddMonoid.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))))))))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (OfNat.ofNat.{u1} L 0 (Zero.toOfNat0.{u1} L (NegZeroClass.toZero.{u1} L (SubNegZeroMonoid.toNegZeroClass.{u1} L (SubtractionMonoid.toSubNegZeroMonoid.{u1} L (SubtractionCommMonoid.toSubtractionMonoid.{u1} L (AddCommGroup.toDivisionAddCommMonoid.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))))))) m) (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (NegZeroClass.toZero.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4)))))))
Case conversion may be inaccurate. Consider using '#align zero_lie zero_lieₓ'. -/
@[simp]
theorem zero_lie : ⁅(0 : L), m⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero
#align zero_lie zero_lie

/- warning: lie_self -> lie_self is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L] (x : L), Eq.{succ u1} L (Bracket.bracket.{u1, u1} L L (LieRing.toHasBracket.{u1} L _inst_2) x x) (OfNat.ofNat.{u1} L 0 (OfNat.mk.{u1} L 0 (Zero.zero.{u1} L (AddZeroClass.toHasZero.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))))))))
but is expected to have type
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L] (x : L), Eq.{succ u1} L (Bracket.bracket.{u1, u1} L L (LieRing.toBracket.{u1} L _inst_2) x x) (OfNat.ofNat.{u1} L 0 (Zero.toOfNat0.{u1} L (NegZeroClass.toZero.{u1} L (SubNegZeroMonoid.toNegZeroClass.{u1} L (SubtractionMonoid.toSubNegZeroMonoid.{u1} L (SubtractionCommMonoid.toSubtractionMonoid.{u1} L (AddCommGroup.toDivisionAddCommMonoid.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lie_self lie_selfₓ'. -/
@[simp]
theorem lie_self : ⁅x, x⁆ = 0 :=
  LieRing.lie_self x
#align lie_self lie_self

#print lieRingSelfModule /-
instance lieRingSelfModule : LieRingModule L L :=
  { (inferInstance : LieRing L) with }
#align lie_ring_self_module lieRingSelfModule
-/

/- warning: lie_skew -> lie_skew is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L] (x : L) (y : L), Eq.{succ u1} L (Neg.neg.{u1} L (SubNegMonoid.toHasNeg.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))) (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) y x)) (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x y)
but is expected to have type
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L] (x : L) (y : L), Eq.{succ u1} L (Neg.neg.{u1} L (NegZeroClass.toNeg.{u1} L (SubNegZeroMonoid.toNegZeroClass.{u1} L (SubtractionMonoid.toSubNegZeroMonoid.{u1} L (SubtractionCommMonoid.toSubtractionMonoid.{u1} L (AddCommGroup.toDivisionAddCommMonoid.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))))) (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) y x)) (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x y)
Case conversion may be inaccurate. Consider using '#align lie_skew lie_skewₓ'. -/
@[simp]
theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ :=
  by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h
#align lie_skew lie_skew

#print lieAlgebraSelfModule /-
/-- Every Lie algebra is a module over itself. -/
instance lieAlgebraSelfModule : LieModule R L L
    where
  smul_lie t x m := by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
  lie_smul := by apply LieAlgebra.lie_smul
#align lie_algebra_self_module lieAlgebraSelfModule
-/

/- warning: neg_lie -> neg_lie is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (Neg.neg.{u1} L (SubNegMonoid.toHasNeg.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))) x) m) (Neg.neg.{u2} M (SubNegMonoid.toHasNeg.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (Neg.neg.{u1} L (NegZeroClass.toNeg.{u1} L (SubNegZeroMonoid.toNegZeroClass.{u1} L (SubtractionMonoid.toSubNegZeroMonoid.{u1} L (SubtractionCommMonoid.toSubtractionMonoid.{u1} L (AddCommGroup.toDivisionAddCommMonoid.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))))) x) m) (Neg.neg.{u2} M (NegZeroClass.toNeg.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m))
Case conversion may be inaccurate. Consider using '#align neg_lie neg_lieₓ'. -/
@[simp]
theorem neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ :=
  by
  rw [← sub_eq_zero, sub_neg_eq_add, ← add_lie]
  simp
#align neg_lie neg_lie

/- warning: lie_neg -> lie_neg is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (Neg.neg.{u2} M (SubNegMonoid.toHasNeg.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) m)) (Neg.neg.{u2} M (SubNegMonoid.toHasNeg.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (Neg.neg.{u2} M (NegZeroClass.toNeg.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) m)) (Neg.neg.{u2} M (NegZeroClass.toNeg.{u2} M (SubNegZeroMonoid.toNegZeroClass.{u2} M (SubtractionMonoid.toSubNegZeroMonoid.{u2} M (SubtractionCommMonoid.toSubtractionMonoid.{u2} M (AddCommGroup.toDivisionAddCommMonoid.{u2} M _inst_4))))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m))
Case conversion may be inaccurate. Consider using '#align lie_neg lie_negₓ'. -/
@[simp]
theorem lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ :=
  by
  rw [← sub_eq_zero, sub_neg_eq_add, ← lie_add]
  simp
#align lie_neg lie_neg

/- warning: sub_lie -> sub_lie is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (HSub.hSub.{u1, u1, u1} L L L (instHSub.{u1} L (SubNegMonoid.toHasSub.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))) x y) m) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (HSub.hSub.{u1, u1, u1} L L L (instHSub.{u1} L (SubNegMonoid.toSub.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))) x y) m) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m))
Case conversion may be inaccurate. Consider using '#align sub_lie sub_lieₓ'. -/
@[simp]
theorem sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by simp [sub_eq_add_neg]
#align sub_lie sub_lie

/- warning: lie_sub -> lie_sub is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M) (n : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) m n)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x n))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (m : M) (n : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) m n)) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x n))
Case conversion may be inaccurate. Consider using '#align lie_sub lie_subₓ'. -/
@[simp]
theorem lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by simp [sub_eq_add_neg]
#align lie_sub lie_sub

#print nsmul_lie /-
@[simp]
theorem nsmul_lie (n : ℕ) : ⁅n • x, m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul ⟨fun x : L => ⁅x, m⁆, zero_lie m, fun _ _ => add_lie _ _ _⟩ _ _
#align nsmul_lie nsmul_lie
-/

#print lie_nsmul /-
@[simp]
theorem lie_nsmul (n : ℕ) : ⁅x, n • m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul ⟨fun m : M => ⁅x, m⁆, lie_zero x, fun _ _ => lie_add _ _ _⟩ _ _
#align lie_nsmul lie_nsmul
-/

#print zsmul_lie /-
@[simp]
theorem zsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul ⟨fun x : L => ⁅x, m⁆, zero_lie m, fun _ _ => add_lie _ _ _⟩ _ _
#align zsmul_lie zsmul_lie
-/

#print lie_zsmul /-
@[simp]
theorem lie_zsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul ⟨fun m : M => ⁅x, m⁆, lie_zero x, fun _ _ => lie_add _ _ _⟩ _ _
#align lie_zsmul lie_zsmul
-/

/- warning: lie_lie -> lie_lie is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x y) m) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toHasSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m)) (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y (Bracket.bracket.{u1, u2} L M (LieRingModule.toHasBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m)))
but is expected to have type
  forall {L : Type.{u1}} {M : Type.{u2}} [_inst_2 : LieRing.{u1} L] [_inst_4 : AddCommGroup.{u2} M] [_inst_6 : LieRingModule.{u1, u2} L M _inst_2 _inst_4] (x : L) (y : L) (m : M), Eq.{succ u2} M (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x y) m) (HSub.hSub.{u2, u2, u2} M M M (instHSub.{u2} M (SubNegMonoid.toSub.{u2} M (AddGroup.toSubNegMonoid.{u2} M (AddCommGroup.toAddGroup.{u2} M _inst_4)))) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y m)) (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) y (Bracket.bracket.{u1, u2} L M (LieRingModule.toBracket.{u1, u2} L M _inst_2 _inst_4 _inst_6) x m)))
Case conversion may be inaccurate. Consider using '#align lie_lie lie_lieₓ'. -/
@[simp]
theorem lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by rw [leibniz_lie, add_sub_cancel]
#align lie_lie lie_lie

/- warning: lie_jacobi -> lie_jacobi is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L] (x : L) (y : L) (z : L), Eq.{succ u1} L (HAdd.hAdd.{u1, u1, u1} L L L (instHAdd.{u1} L (AddZeroClass.toHasAdd.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))) (HAdd.hAdd.{u1, u1, u1} L L L (instHAdd.{u1} L (AddZeroClass.toHasAdd.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))) (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) y z)) (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) y (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) z x))) (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) z (Bracket.bracket.{u1, u1} L L (LieRingModule.toHasBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x y))) (OfNat.ofNat.{u1} L 0 (OfNat.mk.{u1} L 0 (Zero.zero.{u1} L (AddZeroClass.toHasZero.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2)))))))))
but is expected to have type
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L] (x : L) (y : L) (z : L), Eq.{succ u1} L (HAdd.hAdd.{u1, u1, u1} L L L (instHAdd.{u1} L (AddZeroClass.toAdd.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))) (HAdd.hAdd.{u1, u1, u1} L L L (instHAdd.{u1} L (AddZeroClass.toAdd.{u1} L (AddMonoid.toAddZeroClass.{u1} L (SubNegMonoid.toAddMonoid.{u1} L (AddGroup.toSubNegMonoid.{u1} L (AddCommGroup.toAddGroup.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))) (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) y z)) (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) y (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) z x))) (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) z (Bracket.bracket.{u1, u1} L L (LieRingModule.toBracket.{u1, u1} L L _inst_2 (LieRing.toAddCommGroup.{u1} L _inst_2) (lieRingSelfModule.{u1} L _inst_2)) x y))) (OfNat.ofNat.{u1} L 0 (Zero.toOfNat0.{u1} L (NegZeroClass.toZero.{u1} L (SubNegZeroMonoid.toNegZeroClass.{u1} L (SubtractionMonoid.toSubNegZeroMonoid.{u1} L (SubtractionCommMonoid.toSubtractionMonoid.{u1} L (AddCommGroup.toDivisionAddCommMonoid.{u1} L (LieRing.toAddCommGroup.{u1} L _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align lie_jacobi lie_jacobiₓ'. -/
theorem lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 :=
  by
  rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie]
  abel
#align lie_jacobi lie_jacobi

/- warning: lie_ring.int_lie_algebra -> LieRing.intLieAlgebra is a dubious translation:
lean 3 declaration is
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L], LieAlgebra.{0, u1} Int L Int.commRing _inst_2
but is expected to have type
  forall {L : Type.{u1}} [_inst_2 : LieRing.{u1} L], LieAlgebra.{0, u1} Int L Int.instCommRingInt _inst_2
Case conversion may be inaccurate. Consider using '#align lie_ring.int_lie_algebra LieRing.intLieAlgebraₓ'. -/
instance LieRing.intLieAlgebra : LieAlgebra ℤ L where lie_smul n x y := lie_zsmul x y n
#align lie_ring.int_lie_algebra LieRing.intLieAlgebra

instance : LieRingModule L (M →ₗ[R] N)
    where
  bracket x f :=
    { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, LinearMap.map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, LinearMap.map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, LinearMap.coe_mk, LinearMap.add_apply, LinearMap.map_add]
    abel
  lie_add x f g := by
    ext n
    simp only [LinearMap.coe_mk, lie_add, LinearMap.add_apply]
    abel
  leibniz_lie x y f := by
    ext n
    simp only [lie_lie, LinearMap.coe_mk, LinearMap.map_sub, LinearMap.add_apply, lie_sub]
    abel

/- warning: lie_hom.lie_apply -> LieHom.lie_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_hom.lie_apply LieHom.lie_applyₓ'. -/
@[simp]
theorem LieHom.lie_apply (f : M →ₗ[R] N) (x : L) (m : M) : ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
  rfl
#align lie_hom.lie_apply LieHom.lie_apply

instance : LieModule R L (M →ₗ[R] N)
    where
  smul_lie t x f := by
    ext n
    simp only [smul_sub, smul_lie, LinearMap.smul_apply, LieHom.lie_apply, LinearMap.map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, LinearMap.smul_apply, LieHom.lie_apply, lie_smul]

end BasicProperties

#print LieHom /-
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure LieHom (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ[R] L' where
  map_lie' : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆
#align lie_hom LieHom
-/

attribute [nolint doc_blame] LieHom.toLinearMap

-- mathport name: «expr →ₗ⁅ ⁆ »
notation:25 L " →ₗ⁅" R:25 "⁆ " L':0 => LieHom R L L'

namespace LieHom

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R]

variable [LieRing L₁] [LieAlgebra R L₁]

variable [LieRing L₂] [LieAlgebra R L₂]

variable [LieRing L₃] [LieAlgebra R L₃]

instance : Coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) :=
  ⟨LieHom.toLinearMap⟩

/-- see Note [function coercion] -/
instance : CoeFun (L₁ →ₗ⁅R⁆ L₂) fun _ => L₁ → L₂ :=
  ⟨fun f => f.toLinearMap.toFun⟩

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂ :=
  h
#align lie_hom.simps.apply LieHom.Simps.apply

initialize_simps_projections LieHom (to_linear_map_to_fun → apply)

/- warning: lie_hom.coe_to_linear_map -> LieHom.coe_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_to_linear_map LieHom.coe_toLinearMapₓ'. -/
@[simp, norm_cast]
theorem coe_toLinearMap (f : L₁ →ₗ⁅R⁆ L₂) : ((f : L₁ →ₗ[R] L₂) : L₁ → L₂) = f :=
  rfl
#align lie_hom.coe_to_linear_map LieHom.coe_toLinearMap

/- warning: lie_hom.to_fun_eq_coe -> LieHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{max (succ u2) (succ u3)} (L₁ -> L₂) (LinearMap.toFun.{u1, u1, u2, u3} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) L₁ L₂ (AddCommGroup.toAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4)) (LieAlgebra.toModule.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3) (LieAlgebra.toModule.{u1, u3} R L₂ _inst_1 _inst_4 _inst_5) (LieHom.toLinearMap.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 f)) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{max (succ u2) (succ u3)} (L₁ -> L₂) (AddHom.toFun.{u2, u3} L₁ L₂ (AddZeroClass.toAdd.{u2} L₁ (AddMonoid.toAddZeroClass.{u2} L₁ (AddCommMonoid.toAddMonoid.{u2} L₁ (AddCommGroup.toAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))) (AddZeroClass.toAdd.{u3} L₂ (AddMonoid.toAddZeroClass.{u3} L₂ (AddCommMonoid.toAddMonoid.{u3} L₂ (AddCommGroup.toAddCommMonoid.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4))))) (LinearMap.toAddHom.{u1, u1, u2, u3} R R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) L₁ L₂ (AddCommGroup.toAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4)) (LieAlgebra.toModule.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3) (LieAlgebra.toModule.{u1, u3} R L₂ _inst_1 _inst_4 _inst_5) (LieHom.toLinearMap.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 f))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (f : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) f) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f)
Case conversion may be inaccurate. Consider using '#align lie_hom.to_fun_eq_coe LieHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (f : L₁ →ₗ⁅R⁆ L₂) : f.toFun = ⇑f :=
  rfl
#align lie_hom.to_fun_eq_coe LieHom.toFun_eq_coe

/- warning: lie_hom.map_smul -> LieHom.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_hom.map_smul LieHom.map_smulₓ'. -/
@[simp]
theorem map_smul (f : L₁ →ₗ⁅R⁆ L₂) (c : R) (x : L₁) : f (c • x) = c • f x :=
  LinearMap.map_smul (f : L₁ →ₗ[R] L₂) c x
#align lie_hom.map_smul LieHom.map_smul

/- warning: lie_hom.map_add -> LieHom.map_add is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁) (y : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (HAdd.hAdd.{u2, u2, u2} L₁ L₁ L₁ (instHAdd.{u2} L₁ (AddZeroClass.toHasAdd.{u2} L₁ (AddMonoid.toAddZeroClass.{u2} L₁ (SubNegMonoid.toAddMonoid.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))) x y)) (HAdd.hAdd.{u3, u3, u3} L₂ L₂ L₂ (instHAdd.{u3} L₂ (AddZeroClass.toHasAdd.{u3} L₂ (AddMonoid.toAddZeroClass.{u3} L₂ (SubNegMonoid.toAddMonoid.{u3} L₂ (AddGroup.toSubNegMonoid.{u3} L₂ (AddCommGroup.toAddGroup.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4))))))) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f y))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁) (y : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (HAdd.hAdd.{u2, u2, u2} L₁ L₁ L₁ (instHAdd.{u2} L₁ (AddZeroClass.toAdd.{u2} L₁ (AddMonoid.toAddZeroClass.{u2} L₁ (SubNegMonoid.toAddMonoid.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))) x y)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (HAdd.hAdd.{u2, u2, u2} L₁ L₁ L₁ (instHAdd.{u2} L₁ (AddZeroClass.toAdd.{u2} L₁ (AddMonoid.toAddZeroClass.{u2} L₁ (SubNegMonoid.toAddMonoid.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))) x y)) (HAdd.hAdd.{u3, u3, u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) y) ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (instHAdd.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddZeroClass.toAdd.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddMonoid.toAddZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubNegMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddGroup.toSubNegMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddCommGroup.toAddGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) _inst_4))))))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f y))
Case conversion may be inaccurate. Consider using '#align lie_hom.map_add LieHom.map_addₓ'. -/
@[simp]
theorem map_add (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x + y) = f x + f y :=
  LinearMap.map_add (f : L₁ →ₗ[R] L₂) x y
#align lie_hom.map_add LieHom.map_add

/- warning: lie_hom.map_sub -> LieHom.map_sub is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁) (y : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (HSub.hSub.{u2, u2, u2} L₁ L₁ L₁ (instHSub.{u2} L₁ (SubNegMonoid.toHasSub.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))) x y)) (HSub.hSub.{u3, u3, u3} L₂ L₂ L₂ (instHSub.{u3} L₂ (SubNegMonoid.toHasSub.{u3} L₂ (AddGroup.toSubNegMonoid.{u3} L₂ (AddCommGroup.toAddGroup.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4))))) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f y))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁) (y : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (HSub.hSub.{u2, u2, u2} L₁ L₁ L₁ (instHSub.{u2} L₁ (SubNegMonoid.toSub.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))) x y)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (HSub.hSub.{u2, u2, u2} L₁ L₁ L₁ (instHSub.{u2} L₁ (SubNegMonoid.toSub.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))) x y)) (HSub.hSub.{u3, u3, u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) y) ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (instHSub.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubNegMonoid.toSub.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddGroup.toSubNegMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddCommGroup.toAddGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) _inst_4))))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f y))
Case conversion may be inaccurate. Consider using '#align lie_hom.map_sub LieHom.map_subₓ'. -/
@[simp]
theorem map_sub (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x - y) = f x - f y :=
  LinearMap.map_sub (f : L₁ →ₗ[R] L₂) x y
#align lie_hom.map_sub LieHom.map_sub

/- warning: lie_hom.map_neg -> LieHom.map_neg is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (Neg.neg.{u2} L₁ (SubNegMonoid.toHasNeg.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2)))) x)) (Neg.neg.{u3} L₂ (SubNegMonoid.toHasNeg.{u3} L₂ (AddGroup.toSubNegMonoid.{u3} L₂ (AddCommGroup.toAddGroup.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4)))) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (Neg.neg.{u2} L₁ (NegZeroClass.toNeg.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2)))))) x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (Neg.neg.{u2} L₁ (NegZeroClass.toNeg.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2)))))) x)) (Neg.neg.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (NegZeroClass.toNeg.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubNegZeroMonoid.toNegZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubtractionMonoid.toSubNegZeroMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubtractionCommMonoid.toSubtractionMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddCommGroup.toDivisionAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) _inst_4)))))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x))
Case conversion may be inaccurate. Consider using '#align lie_hom.map_neg LieHom.map_negₓ'. -/
@[simp]
theorem map_neg (f : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f (-x) = -f x :=
  LinearMap.map_neg (f : L₁ →ₗ[R] L₂) x
#align lie_hom.map_neg LieHom.map_neg

/- warning: lie_hom.map_lie -> LieHom.map_lie is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁) (y : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (Bracket.bracket.{u2, u2} L₁ L₁ (LieRingModule.toHasBracket.{u2, u2} L₁ L₁ _inst_2 (LieRing.toAddCommGroup.{u2} L₁ _inst_2) (lieRingSelfModule.{u2} L₁ _inst_2)) x y)) (Bracket.bracket.{u3, u3} L₂ L₂ (LieRingModule.toHasBracket.{u3, u3} L₂ L₂ _inst_4 (LieRing.toAddCommGroup.{u3} L₂ _inst_4) (lieRingSelfModule.{u3} L₂ _inst_4)) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f y))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (x : L₁) (y : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (Bracket.bracket.{u2, u2} L₁ L₁ (LieRingModule.toBracket.{u2, u2} L₁ L₁ _inst_2 (LieRing.toAddCommGroup.{u2} L₁ _inst_2) (lieRingSelfModule.{u2} L₁ _inst_2)) x y)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (Bracket.bracket.{u2, u2} L₁ L₁ (LieRingModule.toBracket.{u2, u2} L₁ L₁ _inst_2 (LieRing.toAddCommGroup.{u2} L₁ _inst_2) (lieRingSelfModule.{u2} L₁ _inst_2)) x y)) (Bracket.bracket.{u3, u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) y) (LieRingModule.toBracket.{u3, u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) y) _inst_4 (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) y) _inst_4) (lieRingSelfModule.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) _inst_4)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f y))
Case conversion may be inaccurate. Consider using '#align lie_hom.map_lie LieHom.map_lieₓ'. -/
@[simp]
theorem map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  LieHom.map_lie' f
#align lie_hom.map_lie LieHom.map_lie

/- warning: lie_hom.map_zero -> LieHom.map_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (OfNat.ofNat.{u2} L₁ 0 (OfNat.mk.{u2} L₁ 0 (Zero.zero.{u2} L₁ (AddZeroClass.toHasZero.{u2} L₁ (AddMonoid.toAddZeroClass.{u2} L₁ (SubNegMonoid.toAddMonoid.{u2} L₁ (AddGroup.toSubNegMonoid.{u2} L₁ (AddCommGroup.toAddGroup.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2)))))))))) (OfNat.ofNat.{u3} L₂ 0 (OfNat.mk.{u3} L₂ 0 (Zero.zero.{u3} L₂ (AddZeroClass.toHasZero.{u3} L₂ (AddMonoid.toAddZeroClass.{u3} L₂ (SubNegMonoid.toAddMonoid.{u3} L₂ (AddGroup.toSubNegMonoid.{u3} L₂ (AddCommGroup.toAddGroup.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4)))))))))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) 0 (Zero.toOfNat0.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (NegZeroClass.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (SubNegZeroMonoid.toNegZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (SubtractionMonoid.toSubNegZeroMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (SubtractionCommMonoid.toSubtractionMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (AddCommGroup.toDivisionAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) (OfNat.ofNat.{u2} L₁ 0 (Zero.toOfNat0.{u2} L₁ (NegZeroClass.toZero.{u2} L₁ (SubNegZeroMonoid.toNegZeroClass.{u2} L₁ (SubtractionMonoid.toSubNegZeroMonoid.{u2} L₁ (SubtractionCommMonoid.toSubtractionMonoid.{u2} L₁ (AddCommGroup.toDivisionAddCommMonoid.{u2} L₁ (LieRing.toAddCommGroup.{u2} L₁ _inst_2))))))))) _inst_4))))))))
Case conversion may be inaccurate. Consider using '#align lie_hom.map_zero LieHom.map_zeroₓ'. -/
@[simp]
theorem map_zero (f : L₁ →ₗ⁅R⁆ L₂) : f 0 = 0 :=
  (f : L₁ →ₗ[R] L₂).map_zero
#align lie_hom.map_zero LieHom.map_zero

#print LieHom.id /-
/-- The identity map is a morphism of Lie algebras. -/
def id : L₁ →ₗ⁅R⁆ L₁ :=
  { (LinearMap.id : L₁ →ₗ[R] L₁) with map_lie' := fun x y => rfl }
#align lie_hom.id LieHom.id
-/

/- warning: lie_hom.coe_id -> LieHom.coe_id is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2], Eq.{succ u2} ((fun (_x : LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) => L₁ -> L₁) (LieHom.id.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3)) (coeFn.{succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (fun (_x : LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) => L₁ -> L₁) (LieHom.hasCoeToFun.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.id.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3)) (id.{succ u2} L₁)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2], Eq.{succ u2} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) a) (FunLike.coe.{succ u2, succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) _x) (LieHom.instFunLikeLieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.id.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3)) (id.{succ u2} L₁)
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_id LieHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ((id : L₁ →ₗ⁅R⁆ L₁) : L₁ → L₁) = id :=
  rfl
#align lie_hom.coe_id LieHom.coe_id

/- warning: lie_hom.id_apply -> LieHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} L₁ (coeFn.{succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (fun (_x : LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) => L₁ -> L₁) (LieHom.hasCoeToFun.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.id.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3) x) x
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) x) (FunLike.coe.{succ u2, succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) _x) (LieHom.instFunLikeLieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.id.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3) x) x
Case conversion may be inaccurate. Consider using '#align lie_hom.id_apply LieHom.id_applyₓ'. -/
theorem id_apply (x : L₁) : (id : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_hom.id_apply LieHom.id_apply

/-- The constant 0 map is a Lie algebra morphism. -/
instance : Zero (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨{ (0 : L₁ →ₗ[R] L₂) with map_lie' := by simp }⟩

/- warning: lie_hom.coe_zero -> LieHom.coe_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], Eq.{max (succ u2) (succ u3)} ((fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (OfNat.ofNat.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (OfNat.mk.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (Zero.zero.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.hasZero.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))))) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (OfNat.ofNat.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (OfNat.mk.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (Zero.zero.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.hasZero.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))))) (OfNat.ofNat.{max u2 u3} ((fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (Zero.zero.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.hasZero.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) 0 (OfNat.mk.{max u2 u3} ((fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (Zero.zero.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.hasZero.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) 0 (Zero.zero.{max u2 u3} ((fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (Zero.zero.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.hasZero.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) (Pi.instZero.{u2, u3} L₁ (fun (ᾰ : L₁) => L₂) (fun (i : L₁) => AddZeroClass.toHasZero.{u3} L₂ (AddMonoid.toAddZeroClass.{u3} L₂ (SubNegMonoid.toAddMonoid.{u3} L₂ (AddGroup.toSubNegMonoid.{u3} L₂ (AddCommGroup.toAddGroup.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4))))))))))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], Eq.{max (succ u2) (succ u3)} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) a) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (OfNat.ofNat.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (Zero.toOfNat0.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.instZeroLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)))) (OfNat.ofNat.{max u2 u3} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) a) 0 (Zero.toOfNat0.{max u2 u3} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) a) (Pi.instZero.{u2, u3} L₁ (fun (a : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) a) (fun (i : L₁) => NegZeroClass.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) i) (SubNegZeroMonoid.toNegZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) i) (SubtractionMonoid.toSubNegZeroMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) i) (SubtractionCommMonoid.toSubtractionMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) i) (AddCommGroup.toDivisionAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) i) (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) i) _inst_4)))))))))
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_zero LieHom.coe_zeroₓ'. -/
@[norm_cast, simp]
theorem coe_zero : ((0 : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = 0 :=
  rfl
#align lie_hom.coe_zero LieHom.coe_zero

/- warning: lie_hom.zero_apply -> LieHom.zero_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (x : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (OfNat.ofNat.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (OfNat.mk.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (Zero.zero.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.hasZero.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5)))) x) (OfNat.ofNat.{u3} L₂ 0 (OfNat.mk.{u3} L₂ 0 (Zero.zero.{u3} L₂ (AddZeroClass.toHasZero.{u3} L₂ (AddMonoid.toAddZeroClass.{u3} L₂ (SubNegMonoid.toAddMonoid.{u3} L₂ (AddGroup.toSubNegMonoid.{u3} L₂ (AddCommGroup.toAddGroup.{u3} L₂ (LieRing.toAddCommGroup.{u3} L₂ _inst_4)))))))))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (x : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (OfNat.ofNat.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) 0 (Zero.toOfNat0.{max u2 u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (LieHom.instZeroLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))) x) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) 0 (Zero.toOfNat0.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (NegZeroClass.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubNegZeroMonoid.toNegZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubtractionMonoid.toSubNegZeroMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (SubtractionCommMonoid.toSubtractionMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (AddCommGroup.toDivisionAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (LieRing.toAddCommGroup.{u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) _inst_4))))))))
Case conversion may be inaccurate. Consider using '#align lie_hom.zero_apply LieHom.zero_applyₓ'. -/
theorem zero_apply (x : L₁) : (0 : L₁ →ₗ⁅R⁆ L₂) x = 0 :=
  rfl
#align lie_hom.zero_apply LieHom.zero_apply

/-- The identity map is a Lie algebra morphism. -/
instance : One (L₁ →ₗ⁅R⁆ L₁) :=
  ⟨id⟩

/- warning: lie_hom.coe_one -> LieHom.coe_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2], Eq.{succ u2} ((fun (_x : LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) => L₁ -> L₁) (OfNat.ofNat.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (OfNat.mk.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (One.one.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.hasOne.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3))))) (coeFn.{succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (fun (_x : LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) => L₁ -> L₁) (LieHom.hasCoeToFun.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (OfNat.ofNat.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (OfNat.mk.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (One.one.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.hasOne.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3))))) (id.{succ u2} L₁)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2], Eq.{succ u2} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) a) (FunLike.coe.{succ u2, succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) _x) (LieHom.instFunLikeLieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (OfNat.ofNat.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (One.toOfNat1.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.instOneLieHom.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3)))) (id.{succ u2} L₁)
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_one LieHom.coe_oneₓ'. -/
@[simp]
theorem coe_one : ((1 : L₁ →ₗ⁅R⁆ L₁) : L₁ → L₁) = id :=
  rfl
#align lie_hom.coe_one LieHom.coe_one

/- warning: lie_hom.one_apply -> LieHom.one_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} L₁ (coeFn.{succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (fun (_x : LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) => L₁ -> L₁) (LieHom.hasCoeToFun.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (OfNat.ofNat.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (OfNat.mk.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (One.one.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.hasOne.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3)))) x) x
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) x) (FunLike.coe.{succ u2, succ u2, succ u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₁) _x) (LieHom.instFunLikeLieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (OfNat.ofNat.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) 1 (One.toOfNat1.{u2} (LieHom.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_3 _inst_2 _inst_3) (LieHom.instOneLieHom.{u1, u2} R L₁ _inst_1 _inst_2 _inst_3))) x) x
Case conversion may be inaccurate. Consider using '#align lie_hom.one_apply LieHom.one_applyₓ'. -/
theorem one_apply (x : L₁) : (1 : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_hom.one_apply LieHom.one_apply

instance : Inhabited (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨0⟩

/- warning: lie_hom.coe_injective -> LieHom.coe_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], Function.Injective.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (L₁ -> L₂) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (ᾰ : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4], Function.Injective.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (L₁ -> L₂) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (ᾰ : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) ᾰ) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5))
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_injective LieHom.coe_injectiveₓ'. -/
theorem coe_injective : @Function.Injective (L₁ →ₗ⁅R⁆ L₂) (L₁ → L₂) coeFn := by
  rintro ⟨⟨f, _⟩⟩ ⟨⟨g, _⟩⟩ ⟨h⟩ <;> congr
#align lie_hom.coe_injective LieHom.coe_injective

/- warning: lie_hom.ext -> LieHom.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] {f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5} {g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5}, (forall (x : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g x)) -> (Eq.{max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f g)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] {f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5} {g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5}, (forall (x : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g x)) -> (Eq.{max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f g)
Case conversion may be inaccurate. Consider using '#align lie_hom.ext LieHom.extₓ'. -/
@[ext]
theorem ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align lie_hom.ext LieHom.ext

/- warning: lie_hom.ext_iff -> LieHom.ext_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] {f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5} {g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5}, Iff (Eq.{max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f g) (forall (x : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g x))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] {f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5} {g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5}, Iff (Eq.{max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f g) (forall (x : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g x))
Case conversion may be inaccurate. Consider using '#align lie_hom.ext_iff LieHom.ext_iffₓ'. -/
theorem ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    rfl, ext⟩
#align lie_hom.ext_iff LieHom.ext_iff

/- warning: lie_hom.congr_fun -> LieHom.congr_fun is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] {f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5} {g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5}, (Eq.{max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f g) -> (forall (x : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g x))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] {f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5} {g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5}, (Eq.{max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f g) -> (forall (x : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g x))
Case conversion may be inaccurate. Consider using '#align lie_hom.congr_fun LieHom.congr_funₓ'. -/
theorem congr_fun {f g : L₁ →ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x :=
  h ▸ rfl
#align lie_hom.congr_fun LieHom.congr_fun

/- warning: lie_hom.mk_coe -> LieHom.mk_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_hom.mk_coe LieHom.mk_coeₓ'. -/
@[simp]
theorem mk_coe (f : L₁ →ₗ⁅R⁆ L₂) (h₁ h₂ h₃) : (⟨⟨f, h₁, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) = f :=
  by
  ext
  rfl
#align lie_hom.mk_coe LieHom.mk_coe

/- warning: lie_hom.coe_mk -> LieHom.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_mk LieHom.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) : ((⟨⟨f, h₁, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f :=
  rfl
#align lie_hom.coe_mk LieHom.coe_mk

#print LieHom.comp /-
/-- The composition of morphisms is a morphism. -/
def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := fun x y => by
      change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆
      rw [map_lie, map_lie] }
#align lie_hom.comp LieHom.comp
-/

/- warning: lie_hom.comp_apply -> LieHom.comp_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_hom.comp_apply LieHom.comp_applyₓ'. -/
theorem comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f (g x) :=
  rfl
#align lie_hom.comp_apply LieHom.comp_apply

/- warning: lie_hom.coe_comp -> LieHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} {L₃ : Type.{u4}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] [_inst_6 : LieRing.{u4} L₃] [_inst_7 : LieAlgebra.{u1, u4} R L₃ _inst_1 _inst_6] (f : LieHom.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{max (succ u2) (succ u4)} ((fun (_x : LieHom.{u1, u2, u4} R L₁ L₃ _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) => L₁ -> L₃) (LieHom.comp.{u1, u2, u3, u4} R L₁ L₂ L₃ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) (coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (LieHom.{u1, u2, u4} R L₁ L₃ _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (fun (_x : LieHom.{u1, u2, u4} R L₁ L₃ _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) => L₁ -> L₃) (LieHom.hasCoeToFun.{u1, u2, u4} R L₁ L₃ _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (LieHom.comp.{u1, u2, u3, u4} R L₁ L₂ L₃ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) (Function.comp.{succ u2, succ u3, succ u4} L₁ L₂ L₃ (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (LieHom.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (fun (_x : LieHom.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) => L₂ -> L₃) (LieHom.hasCoeToFun.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) f) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} {L₃ : Type.{u4}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] [_inst_6 : LieRing.{u4} L₃] [_inst_7 : LieAlgebra.{u1, u4} R L₃ _inst_1 _inst_6] (f : LieHom.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) (g : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5), Eq.{max (succ u2) (succ u4)} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₃) a) (FunLike.coe.{max (succ u2) (succ u4), succ u2, succ u4} (LieHom.{u1, u2, u4} R L₁ L₃ _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₃) _x) (LieHom.instFunLikeLieHom.{u1, u2, u4} R L₁ L₃ _inst_1 _inst_2 _inst_3 _inst_6 _inst_7) (LieHom.comp.{u1, u2, u3, u4} R L₁ L₂ L₃ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f g)) (Function.comp.{succ u2, succ u3, succ u4} L₁ L₂ L₃ (FunLike.coe.{max (succ u3) (succ u4), succ u3, succ u4} (LieHom.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) L₂ (fun (_x : L₂) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₂) => L₃) _x) (LieHom.instFunLikeLieHom.{u1, u3, u4} R L₂ L₃ _inst_1 _inst_4 _inst_5 _inst_6 _inst_7) f) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) g))
Case conversion may be inaccurate. Consider using '#align lie_hom.coe_comp LieHom.coe_compₓ'. -/
@[norm_cast, simp]
theorem coe_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : (f.comp g : L₁ → L₃) = f ∘ g :=
  rfl
#align lie_hom.coe_comp LieHom.coe_comp

#print LieHom.coe_linearMap_comp /-
@[norm_cast, simp]
theorem coe_linearMap_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
    (f.comp g : L₁ →ₗ[R] L₃) = (f : L₂ →ₗ[R] L₃).comp (g : L₁ →ₗ[R] L₂) :=
  rfl
#align lie_hom.coe_linear_map_comp LieHom.coe_linearMap_comp
-/

#print LieHom.comp_id /-
@[simp]
theorem comp_id (f : L₁ →ₗ⁅R⁆ L₂) : f.comp (id : L₁ →ₗ⁅R⁆ L₁) = f :=
  by
  ext
  rfl
#align lie_hom.comp_id LieHom.comp_id
-/

#print LieHom.id_comp /-
@[simp]
theorem id_comp (f : L₁ →ₗ⁅R⁆ L₂) : (id : L₂ →ₗ⁅R⁆ L₂).comp f = f :=
  by
  ext
  rfl
#align lie_hom.id_comp LieHom.id_comp
-/

/- warning: lie_hom.inverse -> LieHom.inverse is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (g : L₂ -> L₁), (Function.LeftInverse.{succ u2, succ u3} L₁ L₂ g (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f)) -> (Function.RightInverse.{succ u2, succ u3} L₁ L₂ g (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f)) -> (LieHom.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_4 _inst_5 _inst_2 _inst_3)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_4 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_4] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) (g : L₂ -> L₁), (Function.LeftInverse.{succ u2, succ u3} L₁ L₂ g (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f)) -> (Function.RightInverse.{succ u2, succ u3} L₁ L₂ g (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_4 _inst_5) f)) -> (LieHom.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_4 _inst_5 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align lie_hom.inverse LieHom.inverseₓ'. -/
/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := fun x y =>
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }
#align lie_hom.inverse LieHom.inverse

end LieHom

section ModulePullBack

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)

variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [LieRingModule L₂ M]

variable (f : L₁ →ₗ⁅R⁆ L₂)

include f

#print LieRingModule.compLieHom /-
/-- A Lie ring module may be pulled back along a morphism of Lie algebras.

See note [reducible non-instances]. -/
@[reducible]
def LieRingModule.compLieHom : LieRingModule L₁ M
    where
  bracket x m := ⁅f x, m⁆
  lie_add x := lie_add (f x)
  add_lie x y m := by simp only [LieHom.map_add, add_lie]
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]
#align lie_ring_module.comp_lie_hom LieRingModule.compLieHom
-/

/- warning: lie_ring_module.comp_lie_hom_apply -> LieRingModule.compLieHom_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_ring_module.comp_lie_hom_apply LieRingModule.compLieHom_applyₓ'. -/
theorem LieRingModule.compLieHom_apply (x : L₁) (m : M) :
    haveI := LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl
#align lie_ring_module.comp_lie_hom_apply LieRingModule.compLieHom_apply

#print LieModule.compLieHom /-
/-- A Lie module may be pulled back along a morphism of Lie algebras.

See note [reducible non-instances]. -/
@[reducible]
def LieModule.compLieHom [Module R M] [LieModule R L₂ M] :
    @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f)
    where
  smul_lie t x m := by simp only [smul_lie, LieHom.map_smul]
  lie_smul t x m := by simp only [lie_smul]
#align lie_module.comp_lie_hom LieModule.compLieHom
-/

end ModulePullBack

#print LieEquiv /-
/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure LieEquiv (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ⁅R⁆ L' where
  invFun : L' → L
  left_inv : Function.LeftInverse inv_fun to_lie_hom.toFun
  right_inv : Function.RightInverse inv_fun to_lie_hom.toFun
#align lie_equiv LieEquiv
-/

attribute [nolint doc_blame] LieEquiv.toLieHom

-- mathport name: «expr ≃ₗ⁅ ⁆ »
notation:50 L " ≃ₗ⁅" R "⁆ " L' => LieEquiv R L L'

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

#print LieEquiv.toLinearEquiv /-
/-- Consider an equivalence of Lie algebras as a linear equivalence. -/
def toLinearEquiv (f : L₁ ≃ₗ⁅R⁆ L₂) : L₁ ≃ₗ[R] L₂ :=
  { f.toLieHom, f with }
#align lie_equiv.to_linear_equiv LieEquiv.toLinearEquiv
-/

#print LieEquiv.hasCoeToLieHom /-
instance hasCoeToLieHom : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨toLieHom⟩
#align lie_equiv.has_coe_to_lie_hom LieEquiv.hasCoeToLieHom
-/

#print LieEquiv.hasCoeToLinearEquiv /-
instance hasCoeToLinearEquiv : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) :=
  ⟨toLinearEquiv⟩
#align lie_equiv.has_coe_to_linear_equiv LieEquiv.hasCoeToLinearEquiv
-/

/-- see Note [function coercion] -/
instance : CoeFun (L₁ ≃ₗ⁅R⁆ L₂) fun _ => L₁ → L₂ :=
  ⟨fun e => e.toLieHom.toFun⟩

/- warning: lie_equiv.coe_to_lie_hom -> LieEquiv.coe_to_lieHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Eq.{max (succ u2) (succ u3)} ((fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.hasCoeToLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6)))) e)) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.hasCoeToLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6)))) e)) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieEquiv.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) e)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Eq.{max (succ u2) (succ u3)} (forall (a : L₁), (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) a) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.toLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6 e)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))) e)
Case conversion may be inaccurate. Consider using '#align lie_equiv.coe_to_lie_hom LieEquiv.coe_to_lieHomₓ'. -/
@[simp, norm_cast]
theorem coe_to_lieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = e :=
  rfl
#align lie_equiv.coe_to_lie_hom LieEquiv.coe_to_lieHom

/- warning: lie_equiv.coe_to_linear_equiv -> LieEquiv.coe_to_linearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_equiv.coe_to_linear_equiv LieEquiv.coe_to_linearEquivₓ'. -/
@[simp, norm_cast]
theorem coe_to_linearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ ≃ₗ[R] L₂) : L₁ → L₂) = e :=
  rfl
#align lie_equiv.coe_to_linear_equiv LieEquiv.coe_to_linearEquiv

/- warning: lie_equiv.to_linear_equiv_mk -> LieEquiv.to_linearEquiv_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_equiv.to_linear_equiv_mk LieEquiv.to_linearEquiv_mkₓ'. -/
@[simp]
theorem to_linearEquiv_mk (f : L₁ →ₗ⁅R⁆ L₂) (g h₁ h₂) :
    (mk f g h₁ h₂ : L₁ ≃ₗ[R] L₂) =
      { f with
        invFun := g
        left_inv := h₁
        right_inv := h₂ } :=
  rfl
#align lie_equiv.to_linear_equiv_mk LieEquiv.to_linearEquiv_mk

#print LieEquiv.coe_linearEquiv_injective /-
theorem coe_linearEquiv_injective : Injective (coe : (L₁ ≃ₗ⁅R⁆ L₂) → L₁ ≃ₗ[R] L₂) :=
  by
  intro f₁ f₂ h; cases f₁; cases f₂; dsimp at h; simp only at h
  congr ; exacts[LieHom.coe_injective h.1, h.2]
#align lie_equiv.coe_linear_equiv_injective LieEquiv.coe_linearEquiv_injective
-/

/- warning: lie_equiv.coe_injective -> LieEquiv.coe_injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3], Function.Injective.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (L₁ -> L₂) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (ᾰ : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieEquiv.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3], Function.Injective.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (L₁ -> L₂) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (ᾰ : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) ᾰ) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))))
Case conversion may be inaccurate. Consider using '#align lie_equiv.coe_injective LieEquiv.coe_injectiveₓ'. -/
theorem coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ → L₂) coeFn :=
  LinearEquiv.coe_injective.comp coe_linearEquiv_injective
#align lie_equiv.coe_injective LieEquiv.coe_injective

/- warning: lie_equiv.ext -> LieEquiv.ext is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] {f : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6} {g : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6}, (forall (x : L₁), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieEquiv.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) f x) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieEquiv.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) g x)) -> (Eq.{max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) f g)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] {f : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6} {g : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6}, (forall (x : L₁), Eq.{succ u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))) f x) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))) g x)) -> (Eq.{max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) f g)
Case conversion may be inaccurate. Consider using '#align lie_equiv.ext LieEquiv.extₓ'. -/
@[ext]
theorem ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align lie_equiv.ext LieEquiv.ext

instance : One (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := fun x y => rfl }⟩

/- warning: lie_equiv.one_apply -> LieEquiv.one_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} L₁ (coeFn.{succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) (fun (_x : LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) => L₁ -> L₁) (LieEquiv.hasCoeToFun.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (OfNat.ofNat.{u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) 1 (OfNat.mk.{u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) 1 (One.one.{u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) (LieEquiv.hasOne.{u1, u2} R L₁ _inst_1 _inst_2 _inst_5)))) x) x
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₁) x) (FunLike.coe.{succ u2, succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₁) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) L₁ L₁ (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) L₁ L₁ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5))) (OfNat.ofNat.{u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) 1 (One.toOfNat1.{u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) (LieEquiv.instOneLieEquiv.{u1, u2} R L₁ _inst_1 _inst_2 _inst_5))) x) x
Case conversion may be inaccurate. Consider using '#align lie_equiv.one_apply LieEquiv.one_applyₓ'. -/
@[simp]
theorem one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_equiv.one_apply LieEquiv.one_apply

instance : Inhabited (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨1⟩

#print LieEquiv.refl /-
/-- Lie algebra equivalences are reflexive. -/
@[refl]
def refl : L₁ ≃ₗ⁅R⁆ L₁ :=
  1
#align lie_equiv.refl LieEquiv.refl
-/

/- warning: lie_equiv.refl_apply -> LieEquiv.refl_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} L₁ (coeFn.{succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) (fun (_x : LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) => L₁ -> L₁) (LieEquiv.hasCoeToFun.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5) (LieEquiv.refl.{u1, u2} R L₁ _inst_1 _inst_2 _inst_5) x) x
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] (x : L₁), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₁) x) (FunLike.coe.{succ u2, succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₁) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) L₁ L₁ (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (LieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_5 _inst_2 _inst_5) L₁ L₁ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u2} R L₁ L₁ _inst_1 _inst_2 _inst_2 _inst_5 _inst_5))) (LieEquiv.refl.{u1, u2} R L₁ _inst_1 _inst_2 _inst_5) x) x
Case conversion may be inaccurate. Consider using '#align lie_equiv.refl_apply LieEquiv.refl_applyₓ'. -/
@[simp]
theorem refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_equiv.refl_apply LieEquiv.refl_apply

#print LieEquiv.symm /-
/-- Lie algebra equivalences are symmetric. -/
@[symm]
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
  { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }
#align lie_equiv.symm LieEquiv.symm
-/

#print LieEquiv.symm_symm /-
@[simp]
theorem symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e :=
  by
  ext
  rfl
#align lie_equiv.symm_symm LieEquiv.symm_symm
-/

/- warning: lie_equiv.apply_symm_apply -> LieEquiv.apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (x : L₂), Eq.{succ u3} L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieEquiv.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) e (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) (fun (_x : LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) => L₂ -> L₁) (LieEquiv.hasCoeToFun.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5) (LieEquiv.symm.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 e) x)) x
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (x : L₂), Eq.{succ u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ (fun (a : L₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₂) => L₁) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ L₁ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ L₁ (LieEquiv.instEquivLikeLieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5))) (LieEquiv.symm.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 e) x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))) e (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ (fun (_x : L₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₂) => L₁) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ L₁ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ L₁ (LieEquiv.instEquivLikeLieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5))) (LieEquiv.symm.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 e) x)) x
Case conversion may be inaccurate. Consider using '#align lie_equiv.apply_symm_apply LieEquiv.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply
#align lie_equiv.apply_symm_apply LieEquiv.apply_symm_apply

/- warning: lie_equiv.symm_apply_apply -> LieEquiv.symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (x : L₁), Eq.{succ u2} L₁ (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) (fun (_x : LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) => L₂ -> L₁) (LieEquiv.hasCoeToFun.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5) (LieEquiv.symm.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 e) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieEquiv.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6) e x)) x
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (x : L₁), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₂) => L₁) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (a : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))) e x)) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ (fun (_x : L₂) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₂) => L₁) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ L₁ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u3, succ u2} (LieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_6 _inst_2 _inst_5) L₂ L₁ (LieEquiv.instEquivLikeLieEquiv.{u1, u3, u2} R L₂ L₁ _inst_1 _inst_3 _inst_2 _inst_6 _inst_5))) (LieEquiv.symm.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6 e) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : L₁) => L₂) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u3), succ u2, succ u3} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ L₂ (LieEquiv.instEquivLikeLieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6))) e x)) x
Case conversion may be inaccurate. Consider using '#align lie_equiv.symm_apply_apply LieEquiv.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply
#align lie_equiv.symm_apply_apply LieEquiv.symm_apply_apply

#print LieEquiv.refl_symm /-
@[simp]
theorem refl_symm : (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl :=
  rfl
#align lie_equiv.refl_symm LieEquiv.refl_symm
-/

#print LieEquiv.trans /-
/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
  { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }
#align lie_equiv.trans LieEquiv.trans
-/

#print LieEquiv.self_trans_symm /-
@[simp]
theorem self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = refl :=
  ext e.symm_apply_apply
#align lie_equiv.self_trans_symm LieEquiv.self_trans_symm
-/

#print LieEquiv.symm_trans_self /-
@[simp]
theorem symm_trans_self (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.trans e = refl :=
  e.symm.self_trans_symm
#align lie_equiv.symm_trans_self LieEquiv.symm_trans_self
-/

/- warning: lie_equiv.trans_apply -> LieEquiv.trans_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_equiv.trans_apply LieEquiv.trans_applyₓ'. -/
@[simp]
theorem trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
#align lie_equiv.trans_apply LieEquiv.trans_apply

#print LieEquiv.symm_trans /-
@[simp]
theorem symm_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align lie_equiv.symm_trans LieEquiv.symm_trans
-/

/- warning: lie_equiv.bijective -> LieEquiv.bijective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Function.Bijective.{succ u2, succ u3} L₁ L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.hasCoeToLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6)))) e))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Function.Bijective.{succ u2, succ u3} L₁ L₂ (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.toLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6 e))
Case conversion may be inaccurate. Consider using '#align lie_equiv.bijective LieEquiv.bijectiveₓ'. -/
protected theorem bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Bijective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.Bijective
#align lie_equiv.bijective LieEquiv.bijective

/- warning: lie_equiv.injective -> LieEquiv.injective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Function.Injective.{succ u2, succ u3} L₁ L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.hasCoeToLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6)))) e))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Function.Injective.{succ u2, succ u3} L₁ L₂ (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.toLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6 e))
Case conversion may be inaccurate. Consider using '#align lie_equiv.injective LieEquiv.injectiveₓ'. -/
protected theorem injective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Injective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.Injective
#align lie_equiv.injective LieEquiv.injective

/- warning: lie_equiv.surjective -> LieEquiv.surjective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Function.Surjective.{succ u2, succ u3} L₁ L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u2) (succ u3)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u2) (succ u3)} a b] => self.0) (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (coeBase.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.hasCoeToLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_3 _inst_5 _inst_6)))) e))
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (e : LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), Function.Surjective.{succ u2, succ u3} L₁ L₂ (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (LieEquiv.toLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6 e))
Case conversion may be inaccurate. Consider using '#align lie_equiv.surjective LieEquiv.surjectiveₓ'. -/
protected theorem surjective (e : L₁ ≃ₗ⁅R⁆ L₂) :
    Function.Surjective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.Surjective
#align lie_equiv.surjective LieEquiv.surjective

/- warning: lie_equiv.of_bijective -> LieEquiv.ofBijective is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), (Function.Bijective.{succ u2, succ u3} L₁ L₂ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) (fun (_x : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) => L₁ -> L₂) (LieHom.hasCoeToFun.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) f)) -> (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6)
but is expected to have type
  forall {R : Type.{u1}} {L₁ : Type.{u2}} {L₂ : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L₁] [_inst_3 : LieRing.{u3} L₂] [_inst_5 : LieAlgebra.{u1, u2} R L₁ _inst_1 _inst_2] [_inst_6 : LieAlgebra.{u1, u3} R L₂ _inst_1 _inst_3] (f : LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6), (Function.Bijective.{succ u2, succ u3} L₁ L₂ (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (LieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) L₁ (fun (_x : L₁) => (fun (x._@.Mathlib.Algebra.Lie.Basic._hyg.3919 : L₁) => L₂) _x) (LieHom.instFunLikeLieHom.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6) f)) -> (LieEquiv.{u1, u2, u3} R L₁ L₂ _inst_1 _inst_2 _inst_5 _inst_3 _inst_6)
Case conversion may be inaccurate. Consider using '#align lie_equiv.of_bijective LieEquiv.ofBijectiveₓ'. -/
/-- A bijective morphism of Lie algebras yields an equivalence of Lie algebras. -/
@[simps]
noncomputable def ofBijective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Bijective f) : L₁ ≃ₗ⁅R⁆ L₂ :=
  {
    LinearEquiv.ofBijective (f : L₁ →ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := f.map_lie }
#align lie_equiv.of_bijective LieEquiv.ofBijective

end LieEquiv

section LieModuleMorphisms

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module R P]

variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

variable [LieModule R L M] [LieModule R L N] [LieModule R L P]

/- warning: lie_module_hom -> LieModuleHom is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (L : Type.{u2}) (M : Type.{u3}) (N : Type.{u4}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] [_inst_4 : AddCommGroup.{u3} M] [_inst_5 : AddCommGroup.{u4} N] [_inst_7 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_8 : Module.{u1, u4} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} N _inst_5)] [_inst_10 : LieRingModule.{u2, u3} L M _inst_2 _inst_4] [_inst_11 : LieRingModule.{u2, u4} L N _inst_2 _inst_5] [_inst_13 : LieModule.{u1, u2, u3} R L M _inst_1 _inst_2 _inst_3 _inst_4 _inst_7 _inst_10] [_inst_14 : LieModule.{u1, u2, u4} R L N _inst_1 _inst_2 _inst_3 _inst_5 _inst_8 _inst_11], Sort.{max (succ u3) (succ u4)}
but is expected to have type
  forall (R : Type.{u1}) (L : Type.{u2}) (M : Type.{u3}) (N : Type.{u4}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : AddCommGroup.{u3} M] [_inst_4 : AddCommGroup.{u4} N] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_7 : Module.{u1, u4} R N (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4)] [_inst_8 : LieRingModule.{u2, u3} L M _inst_2 _inst_3] [_inst_10 : LieRingModule.{u2, u4} L N _inst_2 _inst_4], Sort.{max (succ u3) (succ u4)}
Case conversion may be inaccurate. Consider using '#align lie_module_hom LieModuleHomₓ'. -/
/-- A morphism of Lie algebra modules is a linear map which commutes with the action of the Lie
algebra. -/
structure LieModuleHom extends M →ₗ[R] N where
  map_lie' : ∀ {x : L} {m : M}, to_fun ⁅x, m⁆ = ⁅x, to_fun m⁆
#align lie_module_hom LieModuleHom

attribute [nolint doc_blame] LieModuleHom.toLinearMap

-- mathport name: «expr →ₗ⁅ , ⁆ »
notation:25 M " →ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleHom R L M N

namespace LieModuleHom

variable {R L M N P}

instance : Coe (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) :=
  ⟨LieModuleHom.toLinearMap⟩

/-- see Note [function coercion] -/
instance : CoeFun (M →ₗ⁅R,L⁆ N) fun _ => M → N :=
  ⟨fun f => f.toLinearMap.toFun⟩

/- warning: lie_module_hom.coe_to_linear_map -> LieModuleHom.coe_to_linearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_to_linear_map LieModuleHom.coe_to_linearMapₓ'. -/
@[simp, norm_cast]
theorem coe_to_linearMap (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl
#align lie_module_hom.coe_to_linear_map LieModuleHom.coe_to_linearMap

/- warning: lie_module_hom.map_smul -> LieModuleHom.map_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_smul LieModuleHom.map_smulₓ'. -/
@[simp]
theorem map_smul (f : M →ₗ⁅R,L⁆ N) (c : R) (x : M) : f (c • x) = c • f x :=
  LinearMap.map_smul (f : M →ₗ[R] N) c x
#align lie_module_hom.map_smul LieModuleHom.map_smul

/- warning: lie_module_hom.map_add -> LieModuleHom.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_add LieModuleHom.map_addₓ'. -/
@[simp]
theorem map_add (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x + y) = f x + f y :=
  LinearMap.map_add (f : M →ₗ[R] N) x y
#align lie_module_hom.map_add LieModuleHom.map_add

/- warning: lie_module_hom.map_sub -> LieModuleHom.map_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_sub LieModuleHom.map_subₓ'. -/
@[simp]
theorem map_sub (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x - y) = f x - f y :=
  LinearMap.map_sub (f : M →ₗ[R] N) x y
#align lie_module_hom.map_sub LieModuleHom.map_sub

/- warning: lie_module_hom.map_neg -> LieModuleHom.map_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_neg LieModuleHom.map_negₓ'. -/
@[simp]
theorem map_neg (f : M →ₗ⁅R,L⁆ N) (x : M) : f (-x) = -f x :=
  LinearMap.map_neg (f : M →ₗ[R] N) x
#align lie_module_hom.map_neg LieModuleHom.map_neg

/- warning: lie_module_hom.map_lie -> LieModuleHom.map_lie is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_lie LieModuleHom.map_lieₓ'. -/
@[simp]
theorem map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
  LieModuleHom.map_lie' f
#align lie_module_hom.map_lie LieModuleHom.map_lie

/- warning: lie_module_hom.map_lie₂ -> LieModuleHom.map_lie₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_lie₂ LieModuleHom.map_lie₂ₓ'. -/
theorem map_lie₂ (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (x : L) (m : M) (n : N) :
    ⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆ := by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]
#align lie_module_hom.map_lie₂ LieModuleHom.map_lie₂

/- warning: lie_module_hom.map_zero -> LieModuleHom.map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.map_zero LieModuleHom.map_zeroₓ'. -/
@[simp]
theorem map_zero (f : M →ₗ⁅R,L⁆ N) : f 0 = 0 :=
  LinearMap.map_zero (f : M →ₗ[R] N)
#align lie_module_hom.map_zero LieModuleHom.map_zero

/- warning: lie_module_hom.id -> LieModuleHom.id is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] [_inst_4 : AddCommGroup.{u3} M] [_inst_7 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_10 : LieRingModule.{u2, u3} L M _inst_2 _inst_4] [_inst_13 : LieModule.{u1, u2, u3} R L M _inst_1 _inst_2 _inst_3 _inst_4 _inst_7 _inst_10], LieModuleHom.{u1, u2, u3, u3} R L M M _inst_1 _inst_2 _inst_3 _inst_4 _inst_4 _inst_7 _inst_7 _inst_10 _inst_10 _inst_13 _inst_13
but is expected to have type
  forall {R : Type.{u1}} {L : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : AddCommGroup.{u3} M] [_inst_4 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_7 : LieRingModule.{u2, u3} L M _inst_2 _inst_3], LieModuleHom.{u1, u2, u3, u3} R L M M _inst_1 _inst_2 _inst_3 _inst_3 _inst_4 _inst_4 _inst_7 _inst_7
Case conversion may be inaccurate. Consider using '#align lie_module_hom.id LieModuleHom.idₓ'. -/
/-- The identity map is a morphism of Lie modules. -/
def id : M →ₗ⁅R,L⁆ M :=
  { (LinearMap.id : M →ₗ[R] M) with map_lie' := fun x m => rfl }
#align lie_module_hom.id LieModuleHom.id

/- warning: lie_module_hom.coe_id -> LieModuleHom.coe_id is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_id LieModuleHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ((id : M →ₗ⁅R,L⁆ M) : M → M) = id :=
  rfl
#align lie_module_hom.coe_id LieModuleHom.coe_id

/- warning: lie_module_hom.id_apply -> LieModuleHom.id_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.id_apply LieModuleHom.id_applyₓ'. -/
theorem id_apply (x : M) : (id : M →ₗ⁅R,L⁆ M) x = x :=
  rfl
#align lie_module_hom.id_apply LieModuleHom.id_apply

/-- The constant 0 map is a Lie module morphism. -/
instance : Zero (M →ₗ⁅R,L⁆ N) :=
  ⟨{ (0 : M →ₗ[R] N) with map_lie' := by simp }⟩

/- warning: lie_module_hom.coe_zero -> LieModuleHom.coe_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_zero LieModuleHom.coe_zeroₓ'. -/
@[norm_cast, simp]
theorem coe_zero : ((0 : M →ₗ⁅R,L⁆ N) : M → N) = 0 :=
  rfl
#align lie_module_hom.coe_zero LieModuleHom.coe_zero

/- warning: lie_module_hom.zero_apply -> LieModuleHom.zero_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.zero_apply LieModuleHom.zero_applyₓ'. -/
theorem zero_apply (m : M) : (0 : M →ₗ⁅R,L⁆ N) m = 0 :=
  rfl
#align lie_module_hom.zero_apply LieModuleHom.zero_apply

/-- The identity map is a Lie module morphism. -/
instance : One (M →ₗ⁅R,L⁆ M) :=
  ⟨id⟩

instance : Inhabited (M →ₗ⁅R,L⁆ N) :=
  ⟨0⟩

/- warning: lie_module_hom.coe_injective -> LieModuleHom.coe_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_injective LieModuleHom.coe_injectiveₓ'. -/
theorem coe_injective : @Function.Injective (M →ₗ⁅R,L⁆ N) (M → N) coeFn :=
  by
  rintro ⟨⟨f, _⟩⟩ ⟨⟨g, _⟩⟩ ⟨h⟩
  congr
#align lie_module_hom.coe_injective LieModuleHom.coe_injective

/- warning: lie_module_hom.ext -> LieModuleHom.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.ext LieModuleHom.extₓ'. -/
@[ext]
theorem ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
  coe_injective <| funext h
#align lie_module_hom.ext LieModuleHom.ext

/- warning: lie_module_hom.ext_iff -> LieModuleHom.ext_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.ext_iff LieModuleHom.ext_iffₓ'. -/
theorem ext_iff {f g : M →ₗ⁅R,L⁆ N} : f = g ↔ ∀ m, f m = g m :=
  ⟨by
    rintro rfl m
    rfl, ext⟩
#align lie_module_hom.ext_iff LieModuleHom.ext_iff

/- warning: lie_module_hom.congr_fun -> LieModuleHom.congr_fun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.congr_fun LieModuleHom.congr_funₓ'. -/
theorem congr_fun {f g : M →ₗ⁅R,L⁆ N} (h : f = g) (x : M) : f x = g x :=
  h ▸ rfl
#align lie_module_hom.congr_fun LieModuleHom.congr_fun

/- warning: lie_module_hom.mk_coe -> LieModuleHom.mk_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.mk_coe LieModuleHom.mk_coeₓ'. -/
@[simp]
theorem mk_coe (f : M →ₗ⁅R,L⁆ N) (h) : (⟨f, h⟩ : M →ₗ⁅R,L⁆ N) = f :=
  by
  ext
  rfl
#align lie_module_hom.mk_coe LieModuleHom.mk_coe

/- warning: lie_module_hom.coe_mk -> LieModuleHom.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_mk LieModuleHom.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f :=
  by
  ext
  rfl
#align lie_module_hom.coe_mk LieModuleHom.coe_mk

/- warning: lie_module_hom.coe_linear_mk -> LieModuleHom.coe_linear_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_linear_mk LieModuleHom.coe_linear_mkₓ'. -/
@[norm_cast, simp]
theorem coe_linear_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M →ₗ[R] N) = f :=
  by
  ext
  rfl
#align lie_module_hom.coe_linear_mk LieModuleHom.coe_linear_mk

/- warning: lie_module_hom.comp -> LieModuleHom.comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.comp LieModuleHom.compₓ'. -/
/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := fun x m => by
      change f (g ⁅x, m⁆) = ⁅x, f (g m)⁆
      rw [map_lie, map_lie] }
#align lie_module_hom.comp LieModuleHom.comp

/- warning: lie_module_hom.comp_apply -> LieModuleHom.comp_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.comp_apply LieModuleHom.comp_applyₓ'. -/
theorem comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f (g m) :=
  rfl
#align lie_module_hom.comp_apply LieModuleHom.comp_apply

/- warning: lie_module_hom.coe_comp -> LieModuleHom.coe_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_comp LieModuleHom.coe_compₓ'. -/
@[norm_cast, simp]
theorem coe_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : (f.comp g : M → P) = f ∘ g :=
  rfl
#align lie_module_hom.coe_comp LieModuleHom.coe_comp

/- warning: lie_module_hom.coe_linear_map_comp -> LieModuleHom.coe_linearMap_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_linear_map_comp LieModuleHom.coe_linearMap_compₓ'. -/
@[norm_cast, simp]
theorem coe_linearMap_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
    (f.comp g : M →ₗ[R] P) = (f : N →ₗ[R] P).comp (g : M →ₗ[R] N) :=
  rfl
#align lie_module_hom.coe_linear_map_comp LieModuleHom.coe_linearMap_comp

/- warning: lie_module_hom.inverse -> LieModuleHom.inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.inverse LieModuleHom.inverseₓ'. -/
/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₗ⁅R,L⁆ M :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := fun x n =>
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }
#align lie_module_hom.inverse LieModuleHom.inverse

instance : Add (M →ₗ⁅R,L⁆ N)
    where add f g := { (f : M →ₗ[R] N) + (g : M →ₗ[R] N) with map_lie' := by simp }

instance : Sub (M →ₗ⁅R,L⁆ N)
    where sub f g := { (f : M →ₗ[R] N) - (g : M →ₗ[R] N) with map_lie' := by simp }

instance : Neg (M →ₗ⁅R,L⁆ N) where neg f := { -(f : M →ₗ[R] N) with map_lie' := by simp }

/- warning: lie_module_hom.coe_add -> LieModuleHom.coe_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_add LieModuleHom.coe_addₓ'. -/
@[norm_cast, simp]
theorem coe_add (f g : M →ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g :=
  rfl
#align lie_module_hom.coe_add LieModuleHom.coe_add

/- warning: lie_module_hom.add_apply -> LieModuleHom.add_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.add_apply LieModuleHom.add_applyₓ'. -/
theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
  rfl
#align lie_module_hom.add_apply LieModuleHom.add_apply

/- warning: lie_module_hom.coe_sub -> LieModuleHom.coe_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_sub LieModuleHom.coe_subₓ'. -/
@[norm_cast, simp]
theorem coe_sub (f g : M →ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g :=
  rfl
#align lie_module_hom.coe_sub LieModuleHom.coe_sub

/- warning: lie_module_hom.sub_apply -> LieModuleHom.sub_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.sub_apply LieModuleHom.sub_applyₓ'. -/
theorem sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
  rfl
#align lie_module_hom.sub_apply LieModuleHom.sub_apply

/- warning: lie_module_hom.coe_neg -> LieModuleHom.coe_neg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_neg LieModuleHom.coe_negₓ'. -/
@[norm_cast, simp]
theorem coe_neg (f : M →ₗ⁅R,L⁆ N) : ⇑(-f) = -f :=
  rfl
#align lie_module_hom.coe_neg LieModuleHom.coe_neg

/- warning: lie_module_hom.neg_apply -> LieModuleHom.neg_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.neg_apply LieModuleHom.neg_applyₓ'. -/
theorem neg_apply (f : M →ₗ⁅R,L⁆ N) (m : M) : (-f) m = -f m :=
  rfl
#align lie_module_hom.neg_apply LieModuleHom.neg_apply

/- warning: lie_module_hom.has_nsmul -> LieModuleHom.hasNsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.has_nsmul LieModuleHom.hasNsmulₓ'. -/
instance hasNsmul : SMul ℕ (M →ₗ⁅R,L⁆ N)
    where smul n f := { n • (f : M →ₗ[R] N) with map_lie' := fun x m => by simp }
#align lie_module_hom.has_nsmul LieModuleHom.hasNsmul

/- warning: lie_module_hom.coe_nsmul -> LieModuleHom.coe_nsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_nsmul LieModuleHom.coe_nsmulₓ'. -/
@[norm_cast, simp]
theorem coe_nsmul (n : ℕ) (f : M →ₗ⁅R,L⁆ N) : ⇑(n • f) = n • f :=
  rfl
#align lie_module_hom.coe_nsmul LieModuleHom.coe_nsmul

/- warning: lie_module_hom.nsmul_apply -> LieModuleHom.nsmul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.nsmul_apply LieModuleHom.nsmul_applyₓ'. -/
theorem nsmul_apply (n : ℕ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (n • f) m = n • f m :=
  rfl
#align lie_module_hom.nsmul_apply LieModuleHom.nsmul_apply

/- warning: lie_module_hom.has_zsmul -> LieModuleHom.hasZsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.has_zsmul LieModuleHom.hasZsmulₓ'. -/
instance hasZsmul : SMul ℤ (M →ₗ⁅R,L⁆ N)
    where smul z f := { z • (f : M →ₗ[R] N) with map_lie' := fun x m => by simp }
#align lie_module_hom.has_zsmul LieModuleHom.hasZsmul

/- warning: lie_module_hom.coe_zsmul -> LieModuleHom.coe_zsmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_zsmul LieModuleHom.coe_zsmulₓ'. -/
@[norm_cast, simp]
theorem coe_zsmul (z : ℤ) (f : M →ₗ⁅R,L⁆ N) : ⇑(z • f) = z • f :=
  rfl
#align lie_module_hom.coe_zsmul LieModuleHom.coe_zsmul

/- warning: lie_module_hom.zsmul_apply -> LieModuleHom.zsmul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.zsmul_apply LieModuleHom.zsmul_applyₓ'. -/
theorem zsmul_apply (z : ℤ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (z • f) m = z • f m :=
  rfl
#align lie_module_hom.zsmul_apply LieModuleHom.zsmul_apply

instance : AddCommGroup (M →ₗ⁅R,L⁆ N) :=
  coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

instance : SMul R (M →ₗ⁅R,L⁆ N) where smul t f := { t • (f : M →ₗ[R] N) with map_lie' := by simp }

/- warning: lie_module_hom.coe_smul -> LieModuleHom.coe_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.coe_smul LieModuleHom.coe_smulₓ'. -/
@[norm_cast, simp]
theorem coe_smul (t : R) (f : M →ₗ⁅R,L⁆ N) : ⇑(t • f) = t • f :=
  rfl
#align lie_module_hom.coe_smul LieModuleHom.coe_smul

/- warning: lie_module_hom.smul_apply -> LieModuleHom.smul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_hom.smul_apply LieModuleHom.smul_applyₓ'. -/
theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
  rfl
#align lie_module_hom.smul_apply LieModuleHom.smul_apply

instance : Module R (M →ₗ⁅R,L⁆ N) :=
  Function.Injective.module R ⟨fun f => f.toLinearMap.toFun, rfl, coe_add⟩ coe_injective coe_smul

end LieModuleHom

/- warning: lie_module_equiv -> LieModuleEquiv is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (L : Type.{u2}) (M : Type.{u3}) (N : Type.{u4}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] [_inst_4 : AddCommGroup.{u3} M] [_inst_5 : AddCommGroup.{u4} N] [_inst_7 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_8 : Module.{u1, u4} R N (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} N _inst_5)] [_inst_10 : LieRingModule.{u2, u3} L M _inst_2 _inst_4] [_inst_11 : LieRingModule.{u2, u4} L N _inst_2 _inst_5] [_inst_13 : LieModule.{u1, u2, u3} R L M _inst_1 _inst_2 _inst_3 _inst_4 _inst_7 _inst_10] [_inst_14 : LieModule.{u1, u2, u4} R L N _inst_1 _inst_2 _inst_3 _inst_5 _inst_8 _inst_11], Sort.{max (succ u3) (succ u4)}
but is expected to have type
  forall (R : Type.{u1}) (L : Type.{u2}) (M : Type.{u3}) (N : Type.{u4}) [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : AddCommGroup.{u3} M] [_inst_4 : AddCommGroup.{u4} N] [_inst_5 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_7 : Module.{u1, u4} R N (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u4} N _inst_4)] [_inst_8 : LieRingModule.{u2, u3} L M _inst_2 _inst_3] [_inst_10 : LieRingModule.{u2, u4} L N _inst_2 _inst_4], Sort.{max (succ u3) (succ u4)}
Case conversion may be inaccurate. Consider using '#align lie_module_equiv LieModuleEquivₓ'. -/
/-- An equivalence of Lie algebra modules is a linear equivalence which is also a morphism of
Lie algebra modules. -/
structure LieModuleEquiv extends M →ₗ⁅R,L⁆ N where
  invFun : N → M
  left_inv : Function.LeftInverse inv_fun to_fun
  right_inv : Function.RightInverse inv_fun to_fun
#align lie_module_equiv LieModuleEquiv

attribute [nolint doc_blame] LieModuleEquiv.toLieModuleHom

-- mathport name: «expr ≃ₗ⁅ , ⁆ »
notation:25 M " ≃ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleEquiv R L M N

namespace LieModuleEquiv

variable {R L M N P}

/- warning: lie_module_equiv.to_linear_equiv -> LieModuleEquiv.toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.to_linear_equiv LieModuleEquiv.toLinearEquivₓ'. -/
/-- View an equivalence of Lie modules as a linear equivalence. -/
def toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ₗ[R] N :=
  { e with }
#align lie_module_equiv.to_linear_equiv LieModuleEquiv.toLinearEquiv

/- warning: lie_module_equiv.to_equiv -> LieModuleEquiv.toEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.to_equiv LieModuleEquiv.toEquivₓ'. -/
/-- View an equivalence of Lie modules as a type level equivalence. -/
def toEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ N :=
  { e with }
#align lie_module_equiv.to_equiv LieModuleEquiv.toEquiv

/- warning: lie_module_equiv.has_coe_to_equiv -> LieModuleEquiv.hasCoeToEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.has_coe_to_equiv LieModuleEquiv.hasCoeToEquivₓ'. -/
instance hasCoeToEquiv : Coe (M ≃ₗ⁅R,L⁆ N) (M ≃ N) :=
  ⟨toEquiv⟩
#align lie_module_equiv.has_coe_to_equiv LieModuleEquiv.hasCoeToEquiv

/- warning: lie_module_equiv.has_coe_to_lie_module_hom -> LieModuleEquiv.hasCoeToLieModuleHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.has_coe_to_lie_module_hom LieModuleEquiv.hasCoeToLieModuleHomₓ'. -/
instance hasCoeToLieModuleHom : Coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) :=
  ⟨toLieModuleHom⟩
#align lie_module_equiv.has_coe_to_lie_module_hom LieModuleEquiv.hasCoeToLieModuleHom

/- warning: lie_module_equiv.has_coe_to_linear_equiv -> LieModuleEquiv.hasCoeToLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.has_coe_to_linear_equiv LieModuleEquiv.hasCoeToLinearEquivₓ'. -/
instance hasCoeToLinearEquiv : Coe (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) :=
  ⟨toLinearEquiv⟩
#align lie_module_equiv.has_coe_to_linear_equiv LieModuleEquiv.hasCoeToLinearEquiv

/-- see Note [function coercion] -/
instance : CoeFun (M ≃ₗ⁅R,L⁆ N) fun _ => M → N :=
  ⟨fun e => e.toLieModuleHom.toFun⟩

/- warning: lie_module_equiv.injective -> LieModuleEquiv.injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.injective LieModuleEquiv.injectiveₓ'. -/
theorem injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injective e :=
  e.toEquiv.Injective
#align lie_module_equiv.injective LieModuleEquiv.injective

/- warning: lie_module_equiv.coe_mk -> LieModuleEquiv.coe_mk is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.coe_mk LieModuleEquiv.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : M →ₗ⁅R,L⁆ N) (inv_fun h₁ h₂) :
    ((⟨f, inv_fun, h₁, h₂⟩ : M ≃ₗ⁅R,L⁆ N) : M → N) = f :=
  rfl
#align lie_module_equiv.coe_mk LieModuleEquiv.coe_mk

/- warning: lie_module_equiv.coe_to_lie_module_hom -> LieModuleEquiv.coe_to_lieModuleHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.coe_to_lie_module_hom LieModuleEquiv.coe_to_lieModuleHomₓ'. -/
@[simp, norm_cast]
theorem coe_to_lieModuleHom (e : M ≃ₗ⁅R,L⁆ N) : ((e : M →ₗ⁅R,L⁆ N) : M → N) = e :=
  rfl
#align lie_module_equiv.coe_to_lie_module_hom LieModuleEquiv.coe_to_lieModuleHom

/- warning: lie_module_equiv.coe_to_linear_equiv -> LieModuleEquiv.coe_to_linearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.coe_to_linear_equiv LieModuleEquiv.coe_to_linearEquivₓ'. -/
@[simp, norm_cast]
theorem coe_to_linearEquiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
  rfl
#align lie_module_equiv.coe_to_linear_equiv LieModuleEquiv.coe_to_linearEquiv

/- warning: lie_module_equiv.to_equiv_injective -> LieModuleEquiv.toEquiv_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.to_equiv_injective LieModuleEquiv.toEquiv_injectiveₓ'. -/
theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) → M ≃ N) := fun e₁ e₂ h =>
  by
  rcases e₁ with ⟨⟨⟩⟩; rcases e₂ with ⟨⟨⟩⟩
  have inj := Equiv.mk.inj h
  dsimp at inj
  apply lie_module_equiv.mk.inj_eq.mpr
  constructor
  · congr
    ext
    rw [inj.1]
  · exact inj.2
#align lie_module_equiv.to_equiv_injective LieModuleEquiv.toEquiv_injective

/- warning: lie_module_equiv.ext -> LieModuleEquiv.ext is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.ext LieModuleEquiv.extₓ'. -/
@[ext]
theorem ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
  toEquiv_injective (Equiv.ext h)
#align lie_module_equiv.ext LieModuleEquiv.ext

instance : One (M ≃ₗ⁅R,L⁆ M) :=
  ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := fun x m => rfl }⟩

/- warning: lie_module_equiv.one_apply -> LieModuleEquiv.one_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.one_apply LieModuleEquiv.one_applyₓ'. -/
@[simp]
theorem one_apply (m : M) : (1 : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl
#align lie_module_equiv.one_apply LieModuleEquiv.one_apply

instance : Inhabited (M ≃ₗ⁅R,L⁆ M) :=
  ⟨1⟩

/- warning: lie_module_equiv.refl -> LieModuleEquiv.refl is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {L : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : LieAlgebra.{u1, u2} R L _inst_1 _inst_2] [_inst_4 : AddCommGroup.{u3} M] [_inst_7 : Module.{u1, u3} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_4)] [_inst_10 : LieRingModule.{u2, u3} L M _inst_2 _inst_4] [_inst_13 : LieModule.{u1, u2, u3} R L M _inst_1 _inst_2 _inst_3 _inst_4 _inst_7 _inst_10], LieModuleEquiv.{u1, u2, u3, u3} R L M M _inst_1 _inst_2 _inst_3 _inst_4 _inst_4 _inst_7 _inst_7 _inst_10 _inst_10 _inst_13 _inst_13
but is expected to have type
  forall {R : Type.{u1}} {L : Type.{u2}} {M : Type.{u3}} [_inst_1 : CommRing.{u1} R] [_inst_2 : LieRing.{u2} L] [_inst_3 : AddCommGroup.{u3} M] [_inst_4 : Module.{u1, u3} R M (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u3} M _inst_3)] [_inst_7 : LieRingModule.{u2, u3} L M _inst_2 _inst_3], LieModuleEquiv.{u1, u2, u3, u3} R L M M _inst_1 _inst_2 _inst_3 _inst_3 _inst_4 _inst_4 _inst_7 _inst_7
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.refl LieModuleEquiv.reflₓ'. -/
/-- Lie module equivalences are reflexive. -/
@[refl]
def refl : M ≃ₗ⁅R,L⁆ M :=
  1
#align lie_module_equiv.refl LieModuleEquiv.refl

/- warning: lie_module_equiv.refl_apply -> LieModuleEquiv.refl_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.refl_apply LieModuleEquiv.refl_applyₓ'. -/
@[simp]
theorem refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl
#align lie_module_equiv.refl_apply LieModuleEquiv.refl_apply

/- warning: lie_module_equiv.symm -> LieModuleEquiv.symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.symm LieModuleEquiv.symmₓ'. -/
/-- Lie module equivalences are syemmtric. -/
@[symm]
def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
  { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }
#align lie_module_equiv.symm LieModuleEquiv.symm

/- warning: lie_module_equiv.apply_symm_apply -> LieModuleEquiv.apply_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.apply_symm_apply LieModuleEquiv.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply
#align lie_module_equiv.apply_symm_apply LieModuleEquiv.apply_symm_apply

/- warning: lie_module_equiv.symm_apply_apply -> LieModuleEquiv.symm_apply_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.symm_apply_apply LieModuleEquiv.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply
#align lie_module_equiv.symm_apply_apply LieModuleEquiv.symm_apply_apply

/- warning: lie_module_equiv.symm_symm -> LieModuleEquiv.symm_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.symm_symm LieModuleEquiv.symm_symmₓ'. -/
@[simp]
theorem symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e :=
  by
  ext
  apply_fun e.symm using e.symm.injective
  simp
#align lie_module_equiv.symm_symm LieModuleEquiv.symm_symm

/- warning: lie_module_equiv.trans -> LieModuleEquiv.trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.trans LieModuleEquiv.transₓ'. -/
/-- Lie module equivalences are transitive. -/
@[trans]
def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
  { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }
#align lie_module_equiv.trans LieModuleEquiv.trans

/- warning: lie_module_equiv.trans_apply -> LieModuleEquiv.trans_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.trans_apply LieModuleEquiv.trans_applyₓ'. -/
@[simp]
theorem trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) : (e₁.trans e₂) m = e₂ (e₁ m) :=
  rfl
#align lie_module_equiv.trans_apply LieModuleEquiv.trans_apply

/- warning: lie_module_equiv.symm_trans -> LieModuleEquiv.symm_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.symm_trans LieModuleEquiv.symm_transₓ'. -/
@[simp]
theorem symm_trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align lie_module_equiv.symm_trans LieModuleEquiv.symm_trans

/- warning: lie_module_equiv.self_trans_symm -> LieModuleEquiv.self_trans_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.self_trans_symm LieModuleEquiv.self_trans_symmₓ'. -/
@[simp]
theorem self_trans_symm (e : M ≃ₗ⁅R,L⁆ N) : e.trans e.symm = refl :=
  ext _ _ e.symm_apply_apply
#align lie_module_equiv.self_trans_symm LieModuleEquiv.self_trans_symm

/- warning: lie_module_equiv.symm_trans_self -> LieModuleEquiv.symm_trans_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lie_module_equiv.symm_trans_self LieModuleEquiv.symm_trans_selfₓ'. -/
@[simp]
theorem symm_trans_self (e : M ≃ₗ⁅R,L⁆ N) : e.symm.trans e = refl :=
  ext _ _ e.apply_symm_apply
#align lie_module_equiv.symm_trans_self LieModuleEquiv.symm_trans_self

end LieModuleEquiv

end LieModuleMorphisms

