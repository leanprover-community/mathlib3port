/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module linear_algebra.projective_space.basic
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FiniteDimensional

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is notation for `projectivization K V`, the projectivization of a `K`-vector space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `projectivization.mk'' H h` where `H : submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `projectivization.equiv_submodule` is the equivalence between `ℙ K V`
  and `{ H : submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

-/


variable (K V : Type _) [DivisionRing K] [AddCommGroup V] [Module K V]

/- warning: projectivization_setoid -> projectivizationSetoid is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Setoid.{succ u2} (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))))
but is expected to have type
  forall (K : Type.{u1}) (V : Type.{u2}) [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], Setoid.{succ u2} (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align projectivization_setoid projectivizationSetoidₓ'. -/
/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivizationSetoid : Setoid { v : V // v ≠ 0 } :=
  (MulAction.orbitRel Kˣ V).comap coe
#align projectivization_setoid projectivizationSetoid

#print Projectivization /-
/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
@[nolint has_nonempty_instance]
def Projectivization :=
  Quotient (projectivizationSetoid K V)
#align projectivization Projectivization
-/

-- mathport name: exprℙ
notation "ℙ" => Projectivization

namespace Projectivization

variable {V}

/- warning: projectivization.mk -> Projectivization.mk is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V), (Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))) -> (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V), (Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) -> (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align projectivization.mk Projectivization.mkₓ'. -/
/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩
#align projectivization.mk Projectivization.mk

/- warning: projectivization.mk' -> Projectivization.mk' is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))))))) -> (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3)
but is expected to have type
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)], (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))))))) -> (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align projectivization.mk' Projectivization.mk'ₓ'. -/
/-- A variant of `projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V :=
  Quotient.mk'' v
#align projectivization.mk' Projectivization.mk'

/- warning: projectivization.mk'_eq_mk -> Projectivization.mk'_eq_mk is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))))))), Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk'.{u1, u2} K V _inst_1 _inst_2 _inst_3 v) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))))))) V (HasLiftT.mk.{succ u2, succ u2} (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))))))) V (CoeTCₓ.coe.{succ u2, succ u2} (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))))))) V (coeBase.{succ u2, succ u2} (Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2)))))))))) V (coeSubtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))))))) v) (Subtype.property.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))) v))
but is expected to have type
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Subtype.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))))))), Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk'.{u1, u2} K V _inst_1 _inst_2 _inst_3 v) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Subtype.val.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) v) (Subtype.property.{succ u2} V (fun (v : V) => Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) v))
Case conversion may be inaccurate. Consider using '#align projectivization.mk'_eq_mk Projectivization.mk'_eq_mkₓ'. -/
@[simp]
theorem mk'_eq_mk (v : { v : V // v ≠ 0 }) : mk' K v = mk K v v.2 :=
  by
  dsimp [mk, mk']
  congr 1
  simp
#align projectivization.mk'_eq_mk Projectivization.mk'_eq_mk

instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

variable {K}

#print Projectivization.rep /-
/-- Choose a representative of `v : projectivization K V` in `V`. -/
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out'
#align projectivization.rep Projectivization.rep
-/

/- warning: projectivization.rep_nonzero -> Projectivization.rep_nonzero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3), Ne.{succ u2} V (Projectivization.rep.{u1, u2} K V _inst_1 _inst_2 _inst_3 v) (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (v : Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3), Ne.{succ u1} V (Projectivization.rep.{u2, u1} K V _inst_1 _inst_2 _inst_3 v) (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V _inst_2)))))))
Case conversion may be inaccurate. Consider using '#align projectivization.rep_nonzero Projectivization.rep_nonzeroₓ'. -/
theorem rep_nonzero (v : ℙ K V) : v.rep ≠ 0 :=
  v.out'.2
#align projectivization.rep_nonzero Projectivization.rep_nonzero

/- warning: projectivization.mk_rep -> Projectivization.mk_rep is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3), Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.rep.{u1, u2} K V _inst_1 _inst_2 _inst_3 v) (Projectivization.rep_nonzero.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)) v
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (v : Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3), Eq.{succ u1} (Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk.{u2, u1} K V _inst_1 _inst_2 _inst_3 (Projectivization.rep.{u2, u1} K V _inst_1 _inst_2 _inst_3 v) (Projectivization.rep_nonzero.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)) v
Case conversion may be inaccurate. Consider using '#align projectivization.mk_rep Projectivization.mk_repₓ'. -/
@[simp]
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v :=
  by
  dsimp [mk, Projectivization.rep]
  simp
#align projectivization.mk_rep Projectivization.mk_rep

open FiniteDimensional

#print Projectivization.submodule /-
/-- Consider an element of the projectivization as a submodule of `V`. -/
protected def submodule (v : ℙ K V) : Submodule K V :=
  (Quotient.liftOn' v fun v => K ∙ (v : V)) <|
    by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _
#align projectivization.submodule Projectivization.submodule
-/

variable (K)

/- warning: projectivization.mk_eq_mk_iff -> Projectivization.mk_eq_mk_iff is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (w : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))) (hw : Ne.{succ u2} V w (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))), Iff (Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 w hw)) (Exists.{succ u1} (Units.{u1} K (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (fun (a : Units.{u1} K (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) => Eq.{succ u2} V (SMul.smul.{u1, u2} (Units.{u1} K (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) V (Units.hasSmul.{u1, u2} K V (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (SMulZeroClass.toHasSmul.{u1, u2} K V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} K V (MulZeroClass.toHasZero.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (Semiring.toMonoidWithZero.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (Module.toMulActionWithZero.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3))))) a w) v))
but is expected to have type
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (w : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) (hw : Ne.{succ u2} V w (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))), Iff (Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 w hw)) (Exists.{succ u1} (Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) (fun (a : Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) => Eq.{succ u2} V (HSMul.hSMul.{u1, u2, u2} (Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) V V (instHSMul.{u1, u2} (Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) V (Units.instSMulUnits.{u1, u2} K V (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (SMulZeroClass.toSMul.{u1, u2} K V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} K V (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (Module.toMulActionWithZero.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)))))) a w) v))
Case conversion may be inaccurate. Consider using '#align projectivization.mk_eq_mk_iff Projectivization.mk_eq_mk_iffₓ'. -/
theorem mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Quotient.eq''
#align projectivization.mk_eq_mk_iff Projectivization.mk_eq_mk_iff

/- warning: projectivization.mk_eq_mk_iff' -> Projectivization.mk_eq_mk_iff' is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (w : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))) (hw : Ne.{succ u2} V w (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))), Iff (Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 w hw)) (Exists.{succ u1} K (fun (a : K) => Eq.{succ u2} V (SMul.smul.{u1, u2} K V (SMulZeroClass.toHasSmul.{u1, u2} K V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} K V (MulZeroClass.toHasZero.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (Semiring.toMonoidWithZero.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (Module.toMulActionWithZero.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)))) a w) v))
but is expected to have type
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (w : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))) (hw : Ne.{succ u2} V w (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))), Iff (Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv) (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 w hw)) (Exists.{succ u1} K (fun (a : K) => Eq.{succ u2} V (HSMul.hSMul.{u1, u2, u2} K V V (instHSMul.{u1, u2} K V (SMulZeroClass.toSMul.{u1, u2} K V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} K V (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (Module.toMulActionWithZero.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3))))) a w) v))
Case conversion may be inaccurate. Consider using '#align projectivization.mk_eq_mk_iff' Projectivization.mk_eq_mk_iff'ₓ'. -/
/-- Two nonzero vectors go to the same point in projective space if and only if one is
a scalar multiple of the other. -/
theorem mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v :=
  by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine' ⟨Units.mk0 a fun c => hv.symm _, ha⟩
    rwa [c, zero_smul] at ha
#align projectivization.mk_eq_mk_iff' Projectivization.mk_eq_mk_iff'

/- warning: projectivization.exists_smul_eq_mk_rep -> Projectivization.exists_smul_eq_mk_rep is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))), Exists.{succ u1} (Units.{u1} K (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (fun (a : Units.{u1} K (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) => Eq.{succ u2} V (SMul.smul.{u1, u2} (Units.{u1} K (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) V (Units.hasSmul.{u1, u2} K V (Ring.toMonoid.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (SMulZeroClass.toHasSmul.{u1, u2} K V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} K V (MulZeroClass.toHasZero.{u1} K (MulZeroOneClass.toMulZeroClass.{u1} K (MonoidWithZero.toMulZeroOneClass.{u1} K (Semiring.toMonoidWithZero.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (AddCommMonoid.toAddMonoid.{u2} V (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)))) (Module.toMulActionWithZero.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3))))) a v) (Projectivization.rep.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv)))
but is expected to have type
  forall (K : Type.{u1}) {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))), Exists.{succ u1} (Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) (fun (a : Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) => Eq.{succ u2} V (HSMul.hSMul.{u1, u2, u2} (Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) V V (instHSMul.{u1, u2} (Units.{u1} K (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) V (Units.instSMulUnits.{u1, u2} K V (MonoidWithZero.toMonoid.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (SMulZeroClass.toSMul.{u1, u2} K V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} K V (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} K V (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))) (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2))))) (Module.toMulActionWithZero.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)))))) a v) (Projectivization.rep.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv)))
Case conversion may be inaccurate. Consider using '#align projectivization.exists_smul_eq_mk_rep Projectivization.exists_smul_eq_mk_repₓ'. -/
theorem exists_smul_eq_mk_rep (v : V) (hv : v ≠ 0) : ∃ a : Kˣ, a • v = (mk K v hv).rep :=
  show (projectivizationSetoid K V).Rel _ _ from Quotient.mk_out' ⟨v, hv⟩
#align projectivization.exists_smul_eq_mk_rep Projectivization.exists_smul_eq_mk_rep

variable {K}

/- warning: projectivization.ind -> Projectivization.ind is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {P : (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) -> Prop}, (forall (v : V) (h : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))), P (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v h)) -> (forall (p : Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3), P p)
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] {P : (Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3) -> Prop}, (forall (v : V) (h : Ne.{succ u1} V v (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V _inst_2)))))))), P (Projectivization.mk.{u2, u1} K V _inst_1 _inst_2 _inst_3 v h)) -> (forall (p : Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3), P p)
Case conversion may be inaccurate. Consider using '#align projectivization.ind Projectivization.indₓ'. -/
/-- An induction principle for `projectivization`.
Use as `induction v using projectivization.ind`. -/
@[elab_as_elim]
theorem ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h
#align projectivization.ind Projectivization.ind

/- warning: projectivization.submodule_mk -> Projectivization.submodule_mk is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (OfNat.mk.{u2} V 0 (Zero.zero.{u2} V (AddZeroClass.toHasZero.{u2} V (AddMonoid.toAddZeroClass.{u2} V (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))))))))), Eq.{succ u2} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv)) (Submodule.span.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3 (Singleton.singleton.{u2, u2} V (Set.{u2} V) (Set.hasSingleton.{u2} V) v))
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : V) (hv : Ne.{succ u2} V v (OfNat.ofNat.{u2} V 0 (Zero.toOfNat0.{u2} V (NegZeroClass.toZero.{u2} V (SubNegZeroMonoid.toNegZeroClass.{u2} V (SubtractionMonoid.toSubNegZeroMonoid.{u2} V (SubtractionCommMonoid.toSubtractionMonoid.{u2} V (AddCommGroup.toDivisionAddCommMonoid.{u2} V _inst_2)))))))), Eq.{succ u2} (Submodule.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.mk.{u1, u2} K V _inst_1 _inst_2 _inst_3 v hv)) (Submodule.span.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3 (Singleton.singleton.{u2, u2} V (Set.{u2} V) (Set.instSingletonSet.{u2} V) v))
Case conversion may be inaccurate. Consider using '#align projectivization.submodule_mk Projectivization.submodule_mkₓ'. -/
@[simp]
theorem submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).Submodule = K ∙ v :=
  rfl
#align projectivization.submodule_mk Projectivization.submodule_mk

/- warning: projectivization.submodule_eq -> Projectivization.submodule_eq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3), Eq.{succ u2} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v) (Submodule.span.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3 (Singleton.singleton.{u2, u2} V (Set.{u2} V) (Set.hasSingleton.{u2} V) (Projectivization.rep.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)))
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (v : Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3), Eq.{succ u1} (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (Projectivization.submodule.{u2, u1} K V _inst_1 _inst_2 _inst_3 v) (Submodule.span.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3 (Singleton.singleton.{u1, u1} V (Set.{u1} V) (Set.instSingletonSet.{u1} V) (Projectivization.rep.{u2, u1} K V _inst_1 _inst_2 _inst_3 v)))
Case conversion may be inaccurate. Consider using '#align projectivization.submodule_eq Projectivization.submodule_eqₓ'. -/
theorem submodule_eq (v : ℙ K V) : v.Submodule = K ∙ v.rep :=
  by
  conv_lhs => rw [← v.mk_rep]
  rfl
#align projectivization.submodule_eq Projectivization.submodule_eq

/- warning: projectivization.finrank_submodule -> Projectivization.finrank_submodule is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3), Eq.{1} Nat (FiniteDimensional.finrank.{u1, u2} K (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)) (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Submodule.addCommGroup.{u1, u2} K V (DivisionRing.toRing.{u1} K _inst_1) _inst_2 _inst_3 (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)) (Submodule.module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3 (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (v : Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3), Eq.{1} Nat (FiniteDimensional.finrank.{u2, u1} K (Subtype.{succ u1} V (fun (x : V) => Membership.mem.{u1, u1} V (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) V (Submodule.setLike.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3)) x (Projectivization.submodule.{u2, u1} K V _inst_1 _inst_2 _inst_3 v))) (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (Submodule.addCommGroup.{u2, u1} K V (DivisionRing.toRing.{u2} K _inst_1) _inst_2 _inst_3 (Projectivization.submodule.{u2, u1} K V _inst_1 _inst_2 _inst_3 v)) (Submodule.module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3 (Projectivization.submodule.{u2, u1} K V _inst_1 _inst_2 _inst_3 v))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align projectivization.finrank_submodule Projectivization.finrank_submoduleₓ'. -/
theorem finrank_submodule (v : ℙ K V) : finrank K v.Submodule = 1 :=
  by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero
#align projectivization.finrank_submodule Projectivization.finrank_submodule

instance (v : ℙ K V) : FiniteDimensional K v.Submodule :=
  by
  rw [← v.mk_rep]
  change FiniteDimensional K (K ∙ v.rep)
  infer_instance

#print Projectivization.submodule_injective /-
theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V → Submodule K V) :=
  by
  intro u v h; replace h := le_of_eq h
  simp only [submodule_eq] at h
  rw [Submodule.le_span_singleton_iff] at h
  rw [← mk_rep v, ← mk_rep u]
  apply Quotient.sound'
  obtain ⟨a, ha⟩ := h u.rep (Submodule.mem_span_singleton_self _)
  have : a ≠ 0 := fun c => u.rep_nonzero (by simpa [c] using ha.symm)
  use Units.mk0 a this, ha
#align projectivization.submodule_injective Projectivization.submodule_injective
-/

variable (K V)

#print Projectivization.equivSubmodule /-
/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
  Equiv.ofBijective (fun v => ⟨v.Submodule, v.finrank_submodule⟩)
    (by
      constructor
      · intro u v h
        apply_fun fun e => e.val  at h
        apply submodule_injective h
      · rintro ⟨H, h⟩
        rw [finrank_eq_one_iff'] at h
        obtain ⟨v, hv, h⟩ := h
        have : (v : V) ≠ 0 := fun c => hv (Subtype.coe_injective c)
        use mk K v this
        symm
        ext x
        revert x
        erw [← Set.ext_iff]
        ext x
        dsimp [-SetLike.mem_coe]
        rw [Submodule.span_singleton_eq_range]
        refine' ⟨fun hh => _, _⟩
        · obtain ⟨c, hc⟩ := h ⟨x, hh⟩
          exact ⟨c, congr_arg coe hc⟩
        · rintro ⟨c, rfl⟩
          refine' Submodule.smul_mem _ _ v.2)
#align projectivization.equiv_submodule Projectivization.equivSubmodule
-/

variable {K V}

#print Projectivization.mk'' /-
/-- Construct an element of the projectivization from a subspace of dimension 1. -/
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩
#align projectivization.mk'' Projectivization.mk''
-/

/- warning: projectivization.submodule_mk'' -> Projectivization.submodule_mk'' is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (H : Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (h : Eq.{1} Nat (FiniteDimensional.finrank.{u1, u2} K (coeSort.{succ u2, succ (succ u2)} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) H) (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Submodule.addCommGroup.{u1, u2} K V (DivisionRing.toRing.{u1} K _inst_1) _inst_2 _inst_3 H) (Submodule.module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3 H)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))), Eq.{succ u2} (Submodule.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.mk''.{u1, u2} K V _inst_1 _inst_2 _inst_3 H h)) H
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (H : Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (h : Eq.{1} Nat (FiniteDimensional.finrank.{u2, u1} K (Subtype.{succ u1} V (fun (x : V) => Membership.mem.{u1, u1} V (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) V (Submodule.setLike.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3)) x H)) (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (Submodule.addCommGroup.{u2, u1} K V (DivisionRing.toRing.{u2} K _inst_1) _inst_2 _inst_3 H) (Submodule.module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3 H)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))), Eq.{succ u1} (Submodule.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2) _inst_3) (Projectivization.submodule.{u2, u1} K V _inst_1 _inst_2 _inst_3 (Projectivization.mk''.{u2, u1} K V _inst_1 _inst_2 _inst_3 H h)) H
Case conversion may be inaccurate. Consider using '#align projectivization.submodule_mk'' Projectivization.submodule_mk''ₓ'. -/
@[simp]
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).Submodule = H :=
  by
  suffices (equiv_submodule K V) (mk'' H h) = ⟨H, h⟩ by exact congr_arg coe this
  dsimp [mk'']
  simp
#align projectivization.submodule_mk'' Projectivization.submodule_mk''

/- warning: projectivization.mk''_submodule -> Projectivization.mk''_submodule is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] (v : Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3), Eq.{succ u2} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk''.{u1, u2} K V _inst_1 _inst_2 _inst_3 (Projectivization.submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v) (Projectivization.finrank_submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)) v
but is expected to have type
  forall {K : Type.{u2}} {V : Type.{u1}} [_inst_1 : DivisionRing.{u2} K] [_inst_2 : AddCommGroup.{u1} V] [_inst_3 : Module.{u2, u1} K V (DivisionSemiring.toSemiring.{u2} K (DivisionRing.toDivisionSemiring.{u2} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} V _inst_2)] (v : Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3), Eq.{succ u1} (Projectivization.{u2, u1} K V _inst_1 _inst_2 _inst_3) (Projectivization.mk''.{u2, u1} K V _inst_1 _inst_2 _inst_3 (Projectivization.submodule.{u2, u1} K V _inst_1 _inst_2 _inst_3 v) (Projectivization.finrank_submodule.{u1, u2} K V _inst_1 _inst_2 _inst_3 v)) v
Case conversion may be inaccurate. Consider using '#align projectivization.mk''_submodule Projectivization.mk''_submoduleₓ'. -/
@[simp]
theorem mk''_submodule (v : ℙ K V) : mk'' v.Submodule v.finrank_submodule = v :=
  show (equivSubmodule K V).symm (equivSubmodule K V _) = _ by simp
#align projectivization.mk''_submodule Projectivization.mk''_submodule

section Map

variable {L W : Type _} [DivisionRing L] [AddCommGroup W] [Module L W]

/- warning: projectivization.map -> Projectivization.map is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {L : Type.{u3}} {W : Type.{u4}} [_inst_4 : DivisionRing.{u3} L] [_inst_5 : AddCommGroup.{u4} W] [_inst_6 : Module.{u3, u4} L W (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5)] {σ : RingHom.{u1, u3} K L (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4)))} (f : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6), (Function.Injective.{succ u2, succ u4} V W (coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) (fun (_x : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) => V -> W) (LinearMap.hasCoeToFun.{u1, u3, u2, u4} K L V W (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6 σ) f)) -> (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) -> (Projectivization.{u3, u4} L W _inst_4 _inst_5 _inst_6)
but is expected to have type
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {L : Type.{u3}} {W : Type.{u4}} [_inst_4 : DivisionRing.{u3} L] [_inst_5 : AddCommGroup.{u4} W] [_inst_6 : Module.{u3, u4} L W (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5)] {σ : RingHom.{u1, u3} K L (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4)))} (f : LinearMap.{u1, u3, u2, u4} K L (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6), (Function.Injective.{succ u2, succ u4} V W (FunLike.coe.{max (succ u2) (succ u4), succ u2, succ u4} (LinearMap.{u1, u3, u2, u4} K L (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) V (fun (_x : V) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : V) => W) _x) (LinearMap.instFunLikeLinearMap.{u1, u3, u2, u4} K L V W (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6 σ) f)) -> (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) -> (Projectivization.{u3, u4} L W _inst_4 _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align projectivization.map Projectivization.mapₓ'. -/
/-- An injective semilinear map of vector spaces induces a map on projective spaces. -/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V → ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.to_monoid_hom a
      dsimp at ha⊢
      erw [← f.map_smulₛₗ, ha])
#align projectivization.map Projectivization.map

/- warning: projectivization.map_injective -> Projectivization.map_injective is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {L : Type.{u3}} {W : Type.{u4}} [_inst_4 : DivisionRing.{u3} L] [_inst_5 : AddCommGroup.{u4} W] [_inst_6 : Module.{u3, u4} L W (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5)] {σ : RingHom.{u1, u3} K L (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4)))} {τ : RingHom.{u3, u1} L K (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4))) (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))} [_inst_7 : RingHomInvPair.{u1, u3} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ τ] (f : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) (hf : Function.Injective.{succ u2, succ u4} V W (coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) (fun (_x : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) => V -> W) (LinearMap.hasCoeToFun.{u1, u3, u2, u4} K L V W (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6 σ) f)), Function.Injective.{succ u2, succ u4} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u3, u4} L W _inst_4 _inst_5 _inst_6) (Projectivization.map.{u1, u2, u3, u4} K V _inst_1 _inst_2 _inst_3 L W _inst_4 _inst_5 _inst_6 σ f hf)
but is expected to have type
  forall {K : Type.{u4}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u4} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u4, u2} K V (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {L : Type.{u3}} {W : Type.{u1}} [_inst_4 : DivisionRing.{u3} L] [_inst_5 : AddCommGroup.{u1} W] [_inst_6 : Module.{u3, u1} L W (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5)] {σ : RingHom.{u4, u3} K L (NonAssocRing.toNonAssocSemiring.{u4} K (Ring.toNonAssocRing.{u4} K (DivisionRing.toRing.{u4} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4)))} {τ : RingHom.{u3, u4} L K (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4))) (NonAssocRing.toNonAssocSemiring.{u4} K (Ring.toNonAssocRing.{u4} K (DivisionRing.toRing.{u4} K _inst_1)))} [_inst_7 : RingHomInvPair.{u4, u3} K L (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ τ] (f : LinearMap.{u4, u3, u2, u1} K L (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6) (hf : Function.Injective.{succ u2, succ u1} V W (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LinearMap.{u4, u3, u2, u1} K L (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6) V (fun (_x : V) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : V) => W) _x) (LinearMap.instFunLikeLinearMap.{u4, u3, u2, u1} K L V W (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6 σ) f)), Function.Injective.{succ u2, succ u1} (Projectivization.{u4, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u3, u1} L W _inst_4 _inst_5 _inst_6) (Projectivization.map.{u4, u2, u3, u1} K V _inst_1 _inst_2 _inst_3 L W _inst_4 _inst_5 _inst_6 σ f hf)
Case conversion may be inaccurate. Consider using '#align projectivization.map_injective Projectivization.map_injectiveₓ'. -/
/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
theorem map_injective {σ : K →+* L} {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) :=
  by
  intro u v h
  rw [← u.mk_rep, ← v.mk_rep] at *
  apply Quotient.sound'
  dsimp [map, mk] at h
  simp only [Quotient.eq''] at h
  obtain ⟨a, ha⟩ := h
  use Units.map τ.to_monoid_hom a
  dsimp at ha⊢
  have : (a : L) = σ (τ a) := by rw [RingHomInvPair.comp_apply_eq₂]
  change (a : L) • f v.rep = f u.rep at ha
  rw [this, ← f.map_smulₛₗ] at ha
  exact hf ha
#align projectivization.map_injective Projectivization.map_injective

#print Projectivization.map_id /-
@[simp]
theorem map_id : map (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).Injective = id :=
  by
  ext v
  induction v using Projectivization.ind
  rfl
#align projectivization.map_id Projectivization.map_id
-/

/- warning: projectivization.map_comp -> Projectivization.map_comp is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u1} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} K V (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {L : Type.{u3}} {W : Type.{u4}} [_inst_4 : DivisionRing.{u3} L] [_inst_5 : AddCommGroup.{u4} W] [_inst_6 : Module.{u3, u4} L W (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5)] {F : Type.{u5}} {U : Type.{u6}} [_inst_7 : Field.{u5} F] [_inst_8 : AddCommGroup.{u6} U] [_inst_9 : Module.{u5, u6} F U (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8)] {σ : RingHom.{u1, u3} K L (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4)))} {τ : RingHom.{u3, u5} L F (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4))) (NonAssocRing.toNonAssocSemiring.{u5} F (Ring.toNonAssocRing.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))))} {γ : RingHom.{u1, u5} K F (NonAssocRing.toNonAssocSemiring.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u5} F (Ring.toNonAssocRing.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))))} [_inst_10 : RingHomCompTriple.{u1, u3, u5} K L F (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) σ τ γ] (f : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) (hf : Function.Injective.{succ u2, succ u4} V W (coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) (fun (_x : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) => V -> W) (LinearMap.hasCoeToFun.{u1, u3, u2, u4} K L V W (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6 σ) f)) (g : LinearMap.{u3, u5, u4, u6} L F (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9) (hg : Function.Injective.{succ u4, succ u6} W U (coeFn.{max (succ u4) (succ u6), max (succ u4) (succ u6)} (LinearMap.{u3, u5, u4, u6} L F (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9) (fun (_x : LinearMap.{u3, u5, u4, u6} L F (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9) => W -> U) (LinearMap.hasCoeToFun.{u3, u5, u4, u6} L F W U (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9 τ) g)), Eq.{max (succ u2) (succ u6)} ((Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) -> (Projectivization.{u5, u6} F U (Field.toDivisionRing.{u5} F _inst_7) _inst_8 _inst_9)) (Projectivization.map.{u1, u2, u5, u6} K V _inst_1 _inst_2 _inst_3 F U (Field.toDivisionRing.{u5} F _inst_7) _inst_8 _inst_9 γ (LinearMap.comp.{u1, u3, u5, u2, u4, u6} K L F V W U (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_3 _inst_6 _inst_9 σ τ γ _inst_10 g f) (Function.Injective.comp.{succ u2, succ u4, succ u6} V W U (coeFn.{max (succ u4) (succ u6), max (succ u4) (succ u6)} (LinearMap.{u3, u5, u4, u6} L F (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9) (fun (_x : LinearMap.{u3, u5, u4, u6} L F (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9) => W -> U) (LinearMap.hasCoeToFun.{u3, u5, u4, u6} L F W U (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (Ring.toSemiring.{u5} F (DivisionRing.toRing.{u5} F (Field.toDivisionRing.{u5} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) (AddCommGroup.toAddCommMonoid.{u6} U _inst_8) _inst_6 _inst_9 τ) g) (fun (x : V) => coeFn.{max (succ u2) (succ u4), max (succ u2) (succ u4)} (LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) (fun (_x : LinearMap.{u1, u3, u2, u4} K L (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6) => V -> W) (LinearMap.hasCoeToFun.{u1, u3, u2, u4} K L V W (Ring.toSemiring.{u1} K (DivisionRing.toRing.{u1} K _inst_1)) (Ring.toSemiring.{u3} L (DivisionRing.toRing.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u4} W _inst_5) _inst_3 _inst_6 σ) f x) hg hf)) (Function.comp.{succ u2, succ u4, succ u6} (Projectivization.{u1, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u3, u4} L W _inst_4 _inst_5 _inst_6) (Projectivization.{u5, u6} F U (Field.toDivisionRing.{u5} F _inst_7) _inst_8 _inst_9) (Projectivization.map.{u3, u4, u5, u6} L W _inst_4 _inst_5 _inst_6 F U (Field.toDivisionRing.{u5} F _inst_7) _inst_8 _inst_9 τ g hg) (Projectivization.map.{u1, u2, u3, u4} K V _inst_1 _inst_2 _inst_3 L W _inst_4 _inst_5 _inst_6 σ f hf))
but is expected to have type
  forall {K : Type.{u4}} {V : Type.{u2}} [_inst_1 : DivisionRing.{u4} K] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u4, u2} K V (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] {L : Type.{u3}} {W : Type.{u1}} [_inst_4 : DivisionRing.{u3} L] [_inst_5 : AddCommGroup.{u1} W] [_inst_6 : Module.{u3, u1} L W (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5)] {F : Type.{u6}} {U : Type.{u5}} [_inst_7 : Field.{u6} F] [_inst_8 : AddCommGroup.{u5} U] [_inst_9 : Module.{u6, u5} F U (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8)] {σ : RingHom.{u4, u3} K L (NonAssocRing.toNonAssocSemiring.{u4} K (Ring.toNonAssocRing.{u4} K (DivisionRing.toRing.{u4} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4)))} {τ : RingHom.{u3, u6} L F (NonAssocRing.toNonAssocSemiring.{u3} L (Ring.toNonAssocRing.{u3} L (DivisionRing.toRing.{u3} L _inst_4))) (NonAssocRing.toNonAssocSemiring.{u6} F (Ring.toNonAssocRing.{u6} F (DivisionRing.toRing.{u6} F (Field.toDivisionRing.{u6} F _inst_7))))} {γ : RingHom.{u4, u6} K F (NonAssocRing.toNonAssocSemiring.{u4} K (Ring.toNonAssocRing.{u4} K (DivisionRing.toRing.{u4} K _inst_1))) (NonAssocRing.toNonAssocSemiring.{u6} F (Ring.toNonAssocRing.{u6} F (DivisionRing.toRing.{u6} F (Field.toDivisionRing.{u6} F _inst_7))))} [_inst_10 : RingHomCompTriple.{u4, u3, u6} K L F (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) σ τ γ] (f : LinearMap.{u4, u3, u2, u1} K L (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6) (hf : Function.Injective.{succ u2, succ u1} V W (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LinearMap.{u4, u3, u2, u1} K L (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6) V (fun (_x : V) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : V) => W) _x) (LinearMap.instFunLikeLinearMap.{u4, u3, u2, u1} K L V W (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6 σ) f)) (g : LinearMap.{u3, u6, u1, u5} L F (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8) _inst_6 _inst_9) (hg : Function.Injective.{succ u1, succ u5} W U (FunLike.coe.{max (succ u1) (succ u5), succ u1, succ u5} (LinearMap.{u3, u6, u1, u5} L F (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8) _inst_6 _inst_9) W (fun (_x : W) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : W) => U) _x) (LinearMap.instFunLikeLinearMap.{u3, u6, u1, u5} L F W U (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8) _inst_6 _inst_9 τ) g)), Eq.{max (succ u2) (succ u5)} ((Projectivization.{u4, u2} K V _inst_1 _inst_2 _inst_3) -> (Projectivization.{u6, u5} F U (Field.toDivisionRing.{u6} F _inst_7) _inst_8 _inst_9)) (Projectivization.map.{u4, u2, u6, u5} K V _inst_1 _inst_2 _inst_3 F U (Field.toDivisionRing.{u6} F _inst_7) _inst_8 _inst_9 γ (LinearMap.comp.{u4, u3, u6, u2, u1, u5} K L F V W U (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8) _inst_3 _inst_6 _inst_9 σ τ γ _inst_10 g f) (Function.Injective.comp.{succ u2, succ u1, succ u5} V W U (FunLike.coe.{max (succ u1) (succ u5), succ u1, succ u5} (LinearMap.{u3, u6, u1, u5} L F (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) τ W U (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8) _inst_6 _inst_9) W (fun (_x : W) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : W) => U) _x) (LinearMap.instFunLikeLinearMap.{u3, u6, u1, u5} L F W U (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (DivisionSemiring.toSemiring.{u6} F (Semifield.toDivisionSemiring.{u6} F (Field.toSemifield.{u6} F _inst_7))) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) (AddCommGroup.toAddCommMonoid.{u5} U _inst_8) _inst_6 _inst_9 τ) g) (fun (x : V) => FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LinearMap.{u4, u3, u2, u1} K L (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) σ V W (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6) V (fun (_x : V) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6190 : V) => W) _x) (LinearMap.instFunLikeLinearMap.{u4, u3, u2, u1} K L V W (DivisionSemiring.toSemiring.{u4} K (DivisionRing.toDivisionSemiring.{u4} K _inst_1)) (DivisionSemiring.toSemiring.{u3} L (DivisionRing.toDivisionSemiring.{u3} L _inst_4)) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) (AddCommGroup.toAddCommMonoid.{u1} W _inst_5) _inst_3 _inst_6 σ) f x) hg hf)) (Function.comp.{succ u2, succ u1, succ u5} (Projectivization.{u4, u2} K V _inst_1 _inst_2 _inst_3) (Projectivization.{u3, u1} L W _inst_4 _inst_5 _inst_6) (Projectivization.{u6, u5} F U (Field.toDivisionRing.{u6} F _inst_7) _inst_8 _inst_9) (Projectivization.map.{u3, u1, u6, u5} L W _inst_4 _inst_5 _inst_6 F U (Field.toDivisionRing.{u6} F _inst_7) _inst_8 _inst_9 τ g hg) (Projectivization.map.{u4, u2, u3, u1} K V _inst_1 _inst_2 _inst_3 L W _inst_4 _inst_5 _inst_6 σ f hf))
Case conversion may be inaccurate. Consider using '#align projectivization.map_comp Projectivization.map_compₓ'. -/
@[simp]
theorem map_comp {F U : Type _} [Field F] [AddCommGroup U] [Module F U] {σ : K →+* L} {τ : L →+* F}
    {γ : K →+* F} [RingHomCompTriple σ τ γ] (f : V →ₛₗ[σ] W) (hf : Function.Injective f)
    (g : W →ₛₗ[τ] U) (hg : Function.Injective g) :
    map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf :=
  by
  ext v
  induction v using Projectivization.ind
  rfl
#align projectivization.map_comp Projectivization.map_comp

end Map

end Projectivization

