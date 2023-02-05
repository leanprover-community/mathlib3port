/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.graded_monoid
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Data.List.BigOperators.Basic
import Mathbin.Data.List.FinRange
import Mathbin.GroupTheory.GroupAction.Defs
import Mathbin.GroupTheory.Submonoid.Basic
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Sigma.Basic

/-!
# Additively-graded multiplicative structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(*) : A i → A j → A (i + j)`; that is to say, `A`
forms an additively-graded monoid. The typeclasses are:

* `graded_monoid.ghas_one A`
* `graded_monoid.ghas_mul A`
* `graded_monoid.gmonoid A`
* `graded_monoid.gcomm_monoid A`

With the `sigma_graded` locale open, these respectively imbue:

* `has_one (graded_monoid A)`
* `has_mul (graded_monoid A)`
* `monoid (graded_monoid A)`
* `comm_monoid (graded_monoid A)`

the base type `A 0` with:

* `graded_monoid.grade_zero.has_one`
* `graded_monoid.grade_zero.has_mul`
* `graded_monoid.grade_zero.monoid`
* `graded_monoid.grade_zero.comm_monoid`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* (nothing)
* `graded_monoid.grade_zero.has_smul (A 0)`
* `graded_monoid.grade_zero.mul_action (A 0)`
* (nothing)

For now, these typeclasses are primarily used in the construction of `direct_sum.ring` and the rest
of that file.

## Dependent graded products

This also introduces `list.dprod`, which takes the (possibly non-commutative) product of a list
of graded elements of type `A i`. This definition primarily exist to allow `graded_monoid.mk`
and `direct_sum.of` to be pulled outside a product, such as in `graded_monoid.mk_list_dprod` and
`direct_sum.of_list_dprod`.

## Internally graded monoids

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_one A` (which provides the obvious `graded_monoid.ghas_one A` instance)
* `set_like.has_graded_mul A` (which provides the obvious `graded_monoid.ghas_mul A` instance)
* `set_like.graded_monoid A` (which provides the obvious `graded_monoid.gmonoid A` and
  `graded_monoid.gcomm_monoid A` instances)

which respectively provide the API lemmas

* `set_like.one_mem_graded`
* `set_like.mul_mem_graded`
* `set_like.pow_mem_graded`, `set_like.list_prod_map_mem_graded`

Strictly this last class is unecessary as it has no fields not present in its parents, but it is
included for convenience. Note that there is no need for `set_like.graded_ring` or similar, as all
the information it would contain is already supplied by `graded_monoid` when `A` is a collection
of objects satisfying `add_submonoid_class` such as `submodule`s. These constructions are explored
in `algebra.direct_sum.internal`.

This file also defines:

* `set_like.is_homogeneous A` (which says that `a` is homogeneous iff `a ∈ A i` for some `i : ι`)
* `set_like.homogeneous_submonoid A`, which is, as the name suggests, the submonoid consisting of
  all the homogeneous elements.

## tags

graded monoid
-/


variable {ι : Type _}

#print GradedMonoid /-
/-- A type alias of sigma types for graded monoids. -/
def GradedMonoid (A : ι → Type _) :=
  Sigma A
#align graded_monoid GradedMonoid
-/

namespace GradedMonoid

instance {A : ι → Type _} [Inhabited ι] [Inhabited (A default)] : Inhabited (GradedMonoid A) :=
  Sigma.inhabited

#print GradedMonoid.mk /-
/-- Construct an element of a graded monoid. -/
def mk {A : ι → Type _} : ∀ i, A i → GradedMonoid A :=
  Sigma.mk
#align graded_monoid.mk GradedMonoid.mk
-/

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _)

#print GradedMonoid.GOne /-
/-- A graded version of `has_one`, which must be of grade 0. -/
class GOne [Zero ι] where
  one : A 0
#align graded_monoid.ghas_one GradedMonoid.GOne
-/

#print GradedMonoid.GOne.toOne /-
/-- `ghas_one` implies `has_one (graded_monoid A)` -/
instance GOne.toOne [Zero ι] [GOne A] : One (GradedMonoid A) :=
  ⟨⟨_, GOne.one⟩⟩
#align graded_monoid.ghas_one.to_has_one GradedMonoid.GOne.toOne
-/

#print GradedMonoid.GMul /-
/-- A graded version of `has_mul`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class GMul [Add ι] where
  mul {i j} : A i → A j → A (i + j)
#align graded_monoid.ghas_mul GradedMonoid.GMul
-/

#print GradedMonoid.GMul.toMul /-
/-- `ghas_mul` implies `has_mul (graded_monoid A)`. -/
instance GMul.toMul [Add ι] [GMul A] : Mul (GradedMonoid A) :=
  ⟨fun x y : GradedMonoid A => ⟨_, GMul.mul x.snd y.snd⟩⟩
#align graded_monoid.ghas_mul.to_has_mul GradedMonoid.GMul.toMul
-/

/- warning: graded_monoid.mk_mul_mk -> GradedMonoid.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : Add.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A _inst_1] {i : ι} {j : ι} (a : A i) (b : A j), Eq.{succ (max u1 u2)} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (instHMul.{max u1 u2} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (GradedMonoid.GMul.toMul.{u1, u2} ι (fun {i : ι} => A i) _inst_1 _inst_2)) (GradedMonoid.mk.{u1, u2} ι (fun {i : ι} => A i) i a) (GradedMonoid.mk.{u1, u2} ι (fun {i : ι} => A i) j b)) (GradedMonoid.mk.{u1, u2} ι (fun {i : ι} => A i) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι _inst_1) i j) (GradedMonoid.GMul.mul.{u1, u2} ι A _inst_1 _inst_2 i j a b))
but is expected to have type
  forall {ι : Type.{u2}} (A : ι -> Type.{u1}) [_inst_1 : Add.{u2} ι] [_inst_2 : GradedMonoid.GMul.{u2, u1} ι A _inst_1] {i : ι} {j : ι} (a : A i) (b : A j), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.{u2, u1} ι A) (GradedMonoid.{u2, u1} ι A) (instHMul.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMul.toMul.{u2, u1} ι A _inst_1 _inst_2)) (GradedMonoid.mk.{u2, u1} ι A i a) (GradedMonoid.mk.{u2, u1} ι A j b)) (GradedMonoid.mk.{u2, u1} ι A (HAdd.hAdd.{u2, u2, u2} ι ι ι (instHAdd.{u2} ι _inst_1) i j) (GradedMonoid.GMul.mul.{u2, u1} ι A _inst_1 _inst_2 i j a b))
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_mul_mk GradedMonoid.mk_mul_mkₓ'. -/
theorem mk_mul_mk [Add ι] [GMul A] {i j} (a : A i) (b : A j) :
    mk i a * mk j b = mk (i + j) (GMul.mul a b) :=
  rfl
#align graded_monoid.mk_mul_mk GradedMonoid.mk_mul_mk

namespace Gmonoid

variable {A} [AddMonoid ι] [GMul A] [GOne A]

/- warning: graded_monoid.gmonoid.gnpow_rec -> GradedMonoid.GMonoid.gnpowRec is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] [_inst_3 : GradedMonoid.GOne.{u1, u2} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] (n : Nat) {i : ι}, (A i) -> (A (SMul.smul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_1) n i))
but is expected to have type
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] [_inst_3 : GradedMonoid.GOne.{u1, u2} ι A (AddMonoid.toZero.{u1} ι _inst_1)] (n : Nat) {i : ι}, (A i) -> (A (HSMul.hSMul.{0, u1, u1} Nat ι ι (instHSMul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_1)) n i))
Case conversion may be inaccurate. Consider using '#align graded_monoid.gmonoid.gnpow_rec GradedMonoid.GMonoid.gnpowRecₓ'. -/
/-- A default implementation of power on a graded monoid, like `npow_rec`.
`gmonoid.gnpow` should be used instead. -/
def gnpowRec : ∀ (n : ℕ) {i}, A i → A (n • i)
  | 0, i, a => cast (congr_arg A (zero_nsmul i).symm) GOne.one
  | n + 1, i, a => cast (congr_arg A (succ_nsmul i n).symm) (GMul.mul a <| gnpow_rec _ a)
#align graded_monoid.gmonoid.gnpow_rec GradedMonoid.GMonoid.gnpowRec

/- warning: graded_monoid.gmonoid.gnpow_rec_zero -> GradedMonoid.GMonoid.gnpowRec_zero is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] [_inst_3 : GradedMonoid.GOne.{u1, u2} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] (a : GradedMonoid.{u1, u2} ι A), Eq.{max (succ u1) (succ u2)} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.mk.{u1, u2} ι A (SMul.smul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_1) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Sigma.fst.{u1, u2} ι A a)) (GradedMonoid.GMonoid.gnpowRec.{u1, u2} ι A _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Sigma.fst.{u1, u2} ι A a) (Sigma.snd.{u1, u2} ι A a))) (OfNat.ofNat.{max u1 u2} (GradedMonoid.{u1, u2} ι A) 1 (OfNat.mk.{max u1 u2} (GradedMonoid.{u1, u2} ι A) 1 (One.one.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GOne.toOne.{u1, u2} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) _inst_3))))
but is expected to have type
  forall {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι (AddMonoid.toAddZeroClass.{u2} ι _inst_1))] [_inst_3 : GradedMonoid.GOne.{u2, u1} ι A (AddMonoid.toZero.{u2} ι _inst_1)] (a : GradedMonoid.{u2, u1} ι A), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.mk.{u2, u1} ι A (HSMul.hSMul.{0, u2, u2} Nat ι ι (instHSMul.{0, u2} Nat ι (AddMonoid.SMul.{u2} ι _inst_1)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Sigma.fst.{u2, u1} ι A a)) (GradedMonoid.GMonoid.gnpowRec.{u2, u1} ι A _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Sigma.fst.{u2, u1} ι A a) (Sigma.snd.{u2, u1} ι A a))) (OfNat.ofNat.{max u2 u1} (GradedMonoid.{u2, u1} ι A) 1 (One.toOfNat1.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GOne.toOne.{u2, u1} ι A (AddMonoid.toZero.{u2} ι _inst_1) _inst_3)))
Case conversion may be inaccurate. Consider using '#align graded_monoid.gmonoid.gnpow_rec_zero GradedMonoid.GMonoid.gnpowRec_zeroₓ'. -/
@[simp]
theorem gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (gnpowRec 0 a.snd) = 1 :=
  Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_zero GradedMonoid.GMonoid.gnpowRec_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_zero'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_zero_tac : tactic Unit :=
  sorry
#align graded_monoid.gmonoid.apply_gnpow_rec_zero_tac graded_monoid.gmonoid.apply_gnpow_rec_zero_tac

/- warning: graded_monoid.gmonoid.gnpow_rec_succ -> GradedMonoid.GMonoid.gnpowRec_succ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] [_inst_3 : GradedMonoid.GOne.{u1, u2} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))] (n : Nat) (a : GradedMonoid.{u1, u2} ι A), Eq.{max (succ u1) (succ u2)} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.mk.{u1, u2} ι A (SMul.smul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_1) (Nat.succ n) (Sigma.fst.{u1, u2} ι A a)) (GradedMonoid.GMonoid.gnpowRec.{u1, u2} ι A _inst_1 _inst_2 _inst_3 (Nat.succ n) (Sigma.fst.{u1, u2} ι A a) (Sigma.snd.{u1, u2} ι A a))) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.{u1, u2} ι A) (GradedMonoid.{u1, u2} ι A) (instHMul.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GMul.toMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) _inst_2)) a (Sigma.mk.{u1, u2} ι A (SMul.smul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_1) n (Sigma.fst.{u1, u2} ι A a)) (GradedMonoid.GMonoid.gnpowRec.{u1, u2} ι A _inst_1 _inst_2 _inst_3 n (Sigma.fst.{u1, u2} ι A a) (Sigma.snd.{u1, u2} ι A a))))
but is expected to have type
  forall {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι (AddMonoid.toAddZeroClass.{u2} ι _inst_1))] [_inst_3 : GradedMonoid.GOne.{u2, u1} ι A (AddMonoid.toZero.{u2} ι _inst_1)] (n : Nat) (a : GradedMonoid.{u2, u1} ι A), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.mk.{u2, u1} ι A (HSMul.hSMul.{0, u2, u2} Nat ι ι (instHSMul.{0, u2} Nat ι (AddMonoid.SMul.{u2} ι _inst_1)) (Nat.succ n) (Sigma.fst.{u2, u1} ι A a)) (GradedMonoid.GMonoid.gnpowRec.{u2, u1} ι A _inst_1 _inst_2 _inst_3 (Nat.succ n) (Sigma.fst.{u2, u1} ι A a) (Sigma.snd.{u2, u1} ι A a))) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.{u2, u1} ι A) (GradedMonoid.{u2, u1} ι A) (instHMul.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMul.toMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι (AddMonoid.toAddZeroClass.{u2} ι _inst_1)) _inst_2)) a (Sigma.mk.{u2, u1} ι A (HSMul.hSMul.{0, u2, u2} Nat ι ι (instHSMul.{0, u2} Nat ι (AddMonoid.SMul.{u2} ι _inst_1)) n (Sigma.fst.{u2, u1} ι A a)) (GradedMonoid.GMonoid.gnpowRec.{u2, u1} ι A _inst_1 _inst_2 _inst_3 n (Sigma.fst.{u2, u1} ι A a) (Sigma.snd.{u2, u1} ι A a))))
Case conversion may be inaccurate. Consider using '#align graded_monoid.gmonoid.gnpow_rec_succ GradedMonoid.GMonoid.gnpowRec_succₓ'. -/
@[simp]
theorem gnpowRec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| gnpowRec n.succ a.snd) = a * ⟨_, gnpowRec n a.snd⟩ :=
  Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm
#align graded_monoid.gmonoid.gnpow_rec_succ GradedMonoid.GMonoid.gnpowRec_succ

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Tactic used to autofill `graded_monoid.gmonoid.gnpow_succ'` when the default
`graded_monoid.gmonoid.gnpow_rec` is used. -/
unsafe def apply_gnpow_rec_succ_tac : tactic Unit :=
  sorry
#align graded_monoid.gmonoid.apply_gnpow_rec_succ_tac graded_monoid.gmonoid.apply_gnpow_rec_succ_tac

end Gmonoid

#print GradedMonoid.GMonoid /-
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic gmonoid.apply_gnpow_rec_zero_tac -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic gmonoid.apply_gnpow_rec_succ_tac -/
/-- A graded version of `monoid`.

Like `monoid.npow`, this has an optional `gmonoid.gnpow` field to allow definitional control of
natural powers of a graded monoid. -/
class GMonoid [AddMonoid ι] extends GMul A, GOne A where
  one_mul (a : GradedMonoid A) : 1 * a = a
  mul_one (a : GradedMonoid A) : a * 1 = a
  mul_assoc (a b c : GradedMonoid A) : a * b * c = a * (b * c)
  gnpow : ∀ (n : ℕ) {i}, A i → A (n • i) := GMonoid.gnpowRec
  gnpow_zero' : ∀ a : GradedMonoid A, GradedMonoid.mk _ (gnpow 0 a.snd) = 1 := by
    run_tac
      gmonoid.apply_gnpow_rec_zero_tac
  gnpow_succ' :
    ∀ (n : ℕ) (a : GradedMonoid A),
      (GradedMonoid.mk _ <| gnpow n.succ a.snd) = a * ⟨_, gnpow n a.snd⟩ := by
    run_tac
      gmonoid.apply_gnpow_rec_succ_tac
#align graded_monoid.gmonoid GradedMonoid.GMonoid
-/

#print GradedMonoid.GMonoid.toMonoid /-
/-- `gmonoid` implies a `monoid (graded_monoid A)`. -/
instance GMonoid.toMonoid [AddMonoid ι] [GMonoid A] : Monoid (GradedMonoid A)
    where
  one := 1
  mul := (· * ·)
  npow n a := GradedMonoid.mk _ (GMonoid.gnpow n a.snd)
  npow_zero a := GMonoid.gnpow_zero' a
  npow_succ n a := GMonoid.gnpow_succ' n a
  one_mul := GMonoid.one_mul
  mul_one := GMonoid.mul_one
  mul_assoc := GMonoid.mul_assoc
#align graded_monoid.gmonoid.to_monoid GradedMonoid.GMonoid.toMonoid
-/

/- warning: graded_monoid.mk_pow -> GradedMonoid.mk_pow is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1] {i : ι} (a : A i) (n : Nat), Eq.{succ (max u1 u2)} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) Nat (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (instHPow.{max u1 u2, 0} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) Nat (Monoid.Pow.{max u1 u2} (GradedMonoid.{u1, u2} ι (fun {i : ι} => A i)) (GradedMonoid.GMonoid.toMonoid.{u1, u2} ι (fun {i : ι} => A i) _inst_1 _inst_2))) (GradedMonoid.mk.{u1, u2} ι (fun {i : ι} => A i) i a) n) (GradedMonoid.mk.{u1, u2} ι (fun {i : ι} => A i) (SMul.smul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_1) n i) (GradedMonoid.GMonoid.gnpow.{u1, u2} ι A _inst_1 _inst_2 n i a))
but is expected to have type
  forall {ι : Type.{u2}} (A : ι -> Type.{u1}) [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMonoid.{u2, u1} ι A _inst_1] {i : ι} (a : A i) (n : Nat), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (HPow.hPow.{max u2 u1, 0, max u2 u1} (GradedMonoid.{u2, u1} ι A) Nat (GradedMonoid.{u2, u1} ι A) (instHPow.{max u2 u1, 0} (GradedMonoid.{u2, u1} ι A) Nat (Monoid.Pow.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMonoid.toMonoid.{u2, u1} ι A _inst_1 _inst_2))) (GradedMonoid.mk.{u2, u1} ι A i a) n) (GradedMonoid.mk.{u2, u1} ι A (HSMul.hSMul.{0, u2, u2} Nat ι ι (instHSMul.{0, u2} Nat ι (AddMonoid.SMul.{u2} ι _inst_1)) n i) (GradedMonoid.GMonoid.gnpow.{u2, u1} ι A _inst_1 _inst_2 n i a))
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_pow GradedMonoid.mk_powₓ'. -/
theorem mk_pow [AddMonoid ι] [GMonoid A] {i} (a : A i) (n : ℕ) :
    mk i a ^ n = mk (n • i) (GMonoid.gnpow _ a) :=
  by
  induction' n with n
  · rw [pow_zero]
    exact (gmonoid.gnpow_zero' ⟨_, a⟩).symm
  · rw [pow_succ, n_ih, mk_mul_mk]
    exact (gmonoid.gnpow_succ' n ⟨_, a⟩).symm
#align graded_monoid.mk_pow GradedMonoid.mk_pow

#print GradedMonoid.GCommMonoid /-
/-- A graded version of `comm_monoid`. -/
class GCommMonoid [AddCommMonoid ι] extends GMonoid A where
  mul_comm (a : GradedMonoid A) (b : GradedMonoid A) : a * b = b * a
#align graded_monoid.gcomm_monoid GradedMonoid.GCommMonoid
-/

#print GradedMonoid.GCommMonoid.toCommMonoid /-
/-- `gcomm_monoid` implies a `comm_monoid (graded_monoid A)`, although this is only used as an
instance locally to define notation in `gmonoid` and similar typeclasses. -/
instance GCommMonoid.toCommMonoid [AddCommMonoid ι] [GCommMonoid A] : CommMonoid (GradedMonoid A) :=
  { GMonoid.toMonoid A with mul_comm := GCommMonoid.mul_comm }
#align graded_monoid.gcomm_monoid.to_comm_monoid GradedMonoid.GCommMonoid.toCommMonoid
-/

end Defs

/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/


section GradeZero

variable (A : ι → Type _)

section One

variable [Zero ι] [GOne A]

#print GradedMonoid.GradeZero.one /-
/-- `1 : A 0` is the value provided in `ghas_one.one`. -/
@[nolint unused_arguments]
instance GradeZero.one : One (A 0) :=
  ⟨GOne.one⟩
#align graded_monoid.grade_zero.has_one GradedMonoid.GradeZero.one
-/

end One

section Mul

variable [AddZeroClass ι] [GMul A]

/- warning: graded_monoid.grade_zero.has_smul -> GradedMonoid.GradeZero.smul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddZeroClass.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι _inst_1)] (i : ι), SMul.{u2, u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (A i)
but is expected to have type
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddZeroClass.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toAdd.{u1} ι _inst_1)] (i : ι), SMul.{u2, u2} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddZeroClass.toZero.{u1} ι _inst_1)))) (A i)
Case conversion may be inaccurate. Consider using '#align graded_monoid.grade_zero.has_smul GradedMonoid.GradeZero.smulₓ'. -/
/-- `(•) : A 0 → A i → A i` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + i)` into `A i`.
-/
instance GradeZero.smul (i : ι) : SMul (A 0) (A i) where smul x y := (zero_add i).rec (GMul.mul x y)
#align graded_monoid.grade_zero.has_smul GradedMonoid.GradeZero.smul

/- warning: graded_monoid.grade_zero.has_mul -> GradedMonoid.GradeZero.mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddZeroClass.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι _inst_1)], Mul.{u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1)))))
but is expected to have type
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddZeroClass.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toAdd.{u1} ι _inst_1)], Mul.{u2} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddZeroClass.toZero.{u1} ι _inst_1))))
Case conversion may be inaccurate. Consider using '#align graded_monoid.grade_zero.has_mul GradedMonoid.GradeZero.mulₓ'. -/
/-- `(*) : A 0 → A 0 → A 0` is the value provided in `graded_monoid.ghas_mul.mul`, composed with
an `eq.rec` to turn `A (0 + 0)` into `A 0`.
-/
instance GradeZero.mul : Mul (A 0) where mul := (· • ·)
#align graded_monoid.grade_zero.has_mul GradedMonoid.GradeZero.mul

variable {A}

/- warning: graded_monoid.mk_zero_smul -> GradedMonoid.mk_zero_smul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddZeroClass.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι _inst_1)] {i : ι} (a : A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (b : A i), Eq.{max (succ u1) (succ u2)} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.mk.{u1, u2} ι A i (SMul.smul.{u2, u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (A i) (GradedMonoid.GradeZero.smul.{u1, u2} ι A _inst_1 _inst_2 i) a b)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.{u1, u2} ι A) (GradedMonoid.{u1, u2} ι A) (instHMul.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GMul.toMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι _inst_1) _inst_2)) (GradedMonoid.mk.{u1, u2} ι A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1)))) a) (GradedMonoid.mk.{u1, u2} ι A i b))
but is expected to have type
  forall {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : AddZeroClass.{u2} ι] [_inst_2 : GradedMonoid.GMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι _inst_1)] {i : ι} (a : A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (b : A i), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.mk.{u2, u1} ι A i (HSMul.hSMul.{u1, u1, u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A i) (A i) (instHSMul.{u1, u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A i) (GradedMonoid.GradeZero.smul.{u2, u1} ι A _inst_1 _inst_2 i)) a b)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.{u2, u1} ι A) (GradedMonoid.{u2, u1} ι A) (instHMul.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMul.toMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι _inst_1) _inst_2)) (GradedMonoid.mk.{u2, u1} ι A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1))) a) (GradedMonoid.mk.{u2, u1} ι A i b))
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_zero_smul GradedMonoid.mk_zero_smulₓ'. -/
@[simp]
theorem mk_zero_smul {i} (a : A 0) (b : A i) : mk _ (a • b) = mk _ a * mk _ b :=
  Sigma.ext (zero_add _).symm <| eq_rec_hEq _ _
#align graded_monoid.mk_zero_smul GradedMonoid.mk_zero_smul

/- warning: graded_monoid.grade_zero.smul_eq_mul -> GradedMonoid.GradeZero.smul_eq_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddZeroClass.{u1} ι] [_inst_2 : GradedMonoid.GMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι _inst_1)] (a : A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (b : A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))), Eq.{succ u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (SMul.smul.{u2, u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (GradedMonoid.GradeZero.smul.{u1, u2} ι A _inst_1 _inst_2 (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) a b) (HMul.hMul.{u2, u2, u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (instHMul.{u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι _inst_1))))) (GradedMonoid.GradeZero.mul.{u1, u2} ι A _inst_1 _inst_2)) a b)
but is expected to have type
  forall {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : AddZeroClass.{u2} ι] [_inst_2 : GradedMonoid.GMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι _inst_1)] (a : A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (b : A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))), Eq.{succ u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (HSMul.hSMul.{u1, u1, u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (instHSMul.{u1, u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (GradedMonoid.GradeZero.smul.{u2, u1} ι A _inst_1 _inst_2 (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (instHMul.{u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddZeroClass.toZero.{u2} ι _inst_1)))) (GradedMonoid.GradeZero.mul.{u2, u1} ι A _inst_1 _inst_2)) a b)
Case conversion may be inaccurate. Consider using '#align graded_monoid.grade_zero.smul_eq_mul GradedMonoid.GradeZero.smul_eq_mulₓ'. -/
@[simp]
theorem GradeZero.smul_eq_mul (a b : A 0) : a • b = a * b :=
  rfl
#align graded_monoid.grade_zero.smul_eq_mul GradedMonoid.GradeZero.smul_eq_mul

end Mul

section Monoid

variable [AddMonoid ι] [GMonoid A]

instance : Pow (A 0) ℕ where pow x n := (nsmul_zero n).rec (GMonoid.gnpow n x : A (n • 0))

variable {A}

/- warning: graded_monoid.mk_zero_pow -> GradedMonoid.mk_zero_pow is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1] (a : A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) (n : Nat), Eq.{max (succ u1) (succ u2)} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.mk.{u1, u2} ι A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))))) (HPow.hPow.{u2, 0, u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) Nat (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) (instHPow.{u2, 0} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) Nat (GradedMonoid.Nat.hasPow.{u1, u2} ι A _inst_1 _inst_2)) a n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (GradedMonoid.{u1, u2} ι A) Nat (GradedMonoid.{u1, u2} ι A) (instHPow.{max u1 u2, 0} (GradedMonoid.{u1, u2} ι A) Nat (Monoid.Pow.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GMonoid.toMonoid.{u1, u2} ι A _inst_1 _inst_2))) (GradedMonoid.mk.{u1, u2} ι A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))))) a) n)
but is expected to have type
  forall {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMonoid.{u2, u1} ι A _inst_1] (a : A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1)))) (n : Nat), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.mk.{u2, u1} ι A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1))) (HPow.hPow.{u1, 0, u1} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1)))) Nat (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1)))) (instHPow.{u1, 0} (A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1)))) Nat (GradedMonoid.instPowOfNatToOfNat0ToZeroNat.{u2, u1} ι A _inst_1 _inst_2)) a n)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (GradedMonoid.{u2, u1} ι A) Nat (GradedMonoid.{u2, u1} ι A) (instHPow.{max u2 u1, 0} (GradedMonoid.{u2, u1} ι A) Nat (Monoid.Pow.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMonoid.toMonoid.{u2, u1} ι A _inst_1 _inst_2))) (GradedMonoid.mk.{u2, u1} ι A (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1))) a) n)
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_zero_pow GradedMonoid.mk_zero_powₓ'. -/
@[simp]
theorem mk_zero_pow (a : A 0) (n : ℕ) : mk _ (a ^ n) = mk _ a ^ n :=
  Sigma.ext (nsmul_zero n).symm <| eq_rec_hEq _ _
#align graded_monoid.mk_zero_pow GradedMonoid.mk_zero_pow

variable (A)

/- warning: graded_monoid.grade_zero.monoid -> GradedMonoid.GradeZero.monoid is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1], Monoid.{u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))))))
but is expected to have type
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1], Monoid.{u2} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddMonoid.toZero.{u1} ι _inst_1))))
Case conversion may be inaccurate. Consider using '#align graded_monoid.grade_zero.monoid GradedMonoid.GradeZero.monoidₓ'. -/
/-- The `monoid` structure derived from `gmonoid A`. -/
instance GradeZero.monoid : Monoid (A 0) :=
  Function.Injective.monoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.monoid GradedMonoid.GradeZero.monoid

end Monoid

section Monoid

variable [AddCommMonoid ι] [GCommMonoid A]

/- warning: graded_monoid.grade_zero.comm_monoid -> GradedMonoid.GradeZero.commMonoid is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : GradedMonoid.GCommMonoid.{u1, u2} ι A _inst_1], CommMonoid.{u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι (AddCommMonoid.toAddMonoid.{u1} ι _inst_1)))))))
but is expected to have type
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : GradedMonoid.GCommMonoid.{u1, u2} ι A _inst_1], CommMonoid.{u2} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddMonoid.toZero.{u1} ι (AddCommMonoid.toAddMonoid.{u1} ι _inst_1)))))
Case conversion may be inaccurate. Consider using '#align graded_monoid.grade_zero.comm_monoid GradedMonoid.GradeZero.commMonoidₓ'. -/
/-- The `comm_monoid` structure derived from `gcomm_monoid A`. -/
instance GradeZero.commMonoid : CommMonoid (A 0) :=
  Function.Injective.commMonoid (mk 0) sigma_mk_injective rfl mk_zero_smul mk_zero_pow
#align graded_monoid.grade_zero.comm_monoid GradedMonoid.GradeZero.commMonoid

end Monoid

section MulAction

variable [AddMonoid ι] [GMonoid A]

/- warning: graded_monoid.mk_zero_monoid_hom -> GradedMonoid.mkZeroMonoidHom is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1], MonoidHom.{u2, max u1 u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) (GradedMonoid.{u1, u2} ι A) (Monoid.toMulOneClass.{u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) (GradedMonoid.GradeZero.monoid.{u1, u2} ι A _inst_1 _inst_2)) (Monoid.toMulOneClass.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GMonoid.toMonoid.{u1, u2} ι A _inst_1 _inst_2))
but is expected to have type
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1], MonoidHom.{u2, max u2 u1} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddMonoid.toZero.{u1} ι _inst_1)))) (GradedMonoid.{u1, u2} ι A) (Monoid.toMulOneClass.{u2} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddMonoid.toZero.{u1} ι _inst_1)))) (GradedMonoid.GradeZero.monoid.{u1, u2} ι A _inst_1 _inst_2)) (Monoid.toMulOneClass.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GMonoid.toMonoid.{u1, u2} ι A _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_zero_monoid_hom GradedMonoid.mkZeroMonoidHomₓ'. -/
/-- `graded_monoid.mk 0` is a `monoid_hom`, using the `graded_monoid.grade_zero.monoid` structure.
-/
def mkZeroMonoidHom : A 0 →* GradedMonoid A
    where
  toFun := mk 0
  map_one' := rfl
  map_mul' := mk_zero_smul
#align graded_monoid.mk_zero_monoid_hom GradedMonoid.mkZeroMonoidHom

/- warning: graded_monoid.grade_zero.mul_action -> GradedMonoid.GradeZero.mulAction is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1] {i : ι}, MulAction.{u2, u2} (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))) (A i) (GradedMonoid.GradeZero.monoid.{u1, u2} ι A _inst_1 _inst_2)
but is expected to have type
  forall {ι : Type.{u1}} (A : ι -> Type.{u2}) [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1] {i : ι}, MulAction.{u2, u2} (A (OfNat.ofNat.{u1} ι 0 (Zero.toOfNat0.{u1} ι (AddMonoid.toZero.{u1} ι _inst_1)))) (A i) (GradedMonoid.GradeZero.monoid.{u1, u2} ι A _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align graded_monoid.grade_zero.mul_action GradedMonoid.GradeZero.mulActionₓ'. -/
/-- Each grade `A i` derives a `A 0`-action structure from `gmonoid A`. -/
instance GradeZero.mulAction {i} : MulAction (A 0) (A i) :=
  letI := MulAction.compHom (GradedMonoid A) (mk_zero_monoid_hom A)
  Function.Injective.mulAction (mk i) sigma_mk_injective mk_zero_smul
#align graded_monoid.grade_zero.mul_action GradedMonoid.GradeZero.mulAction

end MulAction

end GradeZero

end GradedMonoid

/-! ### Dependent products of graded elements -/


section Dprod

variable {α : Type _} {A : ι → Type _} [AddMonoid ι] [GradedMonoid.GMonoid A]

#print List.dProdIndex /-
/-- The index used by `list.dprod`. Propositionally this is equal to `(l.map fι).sum`, but
definitionally it needs to have a different form to avoid introducing `eq.rec`s in `list.dprod`. -/
def List.dProdIndex (l : List α) (fι : α → ι) : ι :=
  l.foldr (fun i b => fι i + b) 0
#align list.dprod_index List.dProdIndex
-/

/- warning: list.dprod_index_nil -> List.dProdIndex_nil is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] (fι : α -> ι), Eq.{succ u1} ι (List.dProdIndex.{u1, u2} ι α _inst_1 (List.nil.{u2} α) fι) (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] (fι : α -> ι), Eq.{succ u2} ι (List.dProdIndex.{u2, u1} ι α _inst_1 (List.nil.{u1} α) fι) (OfNat.ofNat.{u2} ι 0 (Zero.toOfNat0.{u2} ι (AddMonoid.toZero.{u2} ι _inst_1)))
Case conversion may be inaccurate. Consider using '#align list.dprod_index_nil List.dProdIndex_nilₓ'. -/
@[simp]
theorem List.dProdIndex_nil (fι : α → ι) : ([] : List α).dProdIndex fι = 0 :=
  rfl
#align list.dprod_index_nil List.dProdIndex_nil

/- warning: list.dprod_index_cons -> List.dProdIndex_cons is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] (a : α) (l : List.{u2} α) (fι : α -> ι), Eq.{succ u1} ι (List.dProdIndex.{u1, u2} ι α _inst_1 (List.cons.{u2} α a l) fι) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))) (fι a) (List.dProdIndex.{u1, u2} ι α _inst_1 l fι))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] (a : α) (l : List.{u2} α) (fι : α -> ι), Eq.{succ u1} ι (List.dProdIndex.{u1, u2} ι α _inst_1 (List.cons.{u2} α a l) fι) (HAdd.hAdd.{u1, u1, u1} ι ι ι (instHAdd.{u1} ι (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1))) (fι a) (List.dProdIndex.{u1, u2} ι α _inst_1 l fι))
Case conversion may be inaccurate. Consider using '#align list.dprod_index_cons List.dProdIndex_consₓ'. -/
@[simp]
theorem List.dProdIndex_cons (a : α) (l : List α) (fι : α → ι) :
    (a :: l).dProdIndex fι = fι a + l.dProdIndex fι :=
  rfl
#align list.dprod_index_cons List.dProdIndex_cons

/- warning: list.dprod_index_eq_map_sum -> List.dProdIndex_eq_map_sum is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] (l : List.{u2} α) (fι : α -> ι), Eq.{succ u1} ι (List.dProdIndex.{u1, u2} ι α _inst_1 l fι) (List.sum.{u1} ι (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (List.map.{u2, u1} α ι fι l))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] (l : List.{u2} α) (fι : α -> ι), Eq.{succ u1} ι (List.dProdIndex.{u1, u2} ι α _inst_1 l fι) (List.sum.{u1} ι (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (AddMonoid.toZero.{u1} ι _inst_1) (List.map.{u2, u1} α ι fι l))
Case conversion may be inaccurate. Consider using '#align list.dprod_index_eq_map_sum List.dProdIndex_eq_map_sumₓ'. -/
theorem List.dProdIndex_eq_map_sum (l : List α) (fι : α → ι) : l.dProdIndex fι = (l.map fι).Sum :=
  by
  dsimp only [List.dProdIndex]
  induction l
  · simp
  · simp [l_ih]
#align list.dprod_index_eq_map_sum List.dProdIndex_eq_map_sum

#print List.dProd /-
/-- A dependent product for graded monoids represented by the indexed family of types `A i`.
This is a dependent version of `(l.map fA).prod`.

For a list `l : list α`, this computes the product of `fA a` over `a`, where each `fA` is of type
`A (fι a)`. -/
def List.dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) : A (l.dProdIndex fι) :=
  l.foldrRecOn _ _ GradedMonoid.GOne.one fun i x a ha => GradedMonoid.GMul.mul (fA a) x
#align list.dprod List.dProd
-/

/- warning: list.dprod_nil -> List.dProd_nil is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {A : ι -> Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u3} ι A _inst_1] (fι : α -> ι) (fA : forall (a : α), A (fι a)), Eq.{succ u3} (A (List.dProdIndex.{u1, u2} ι α _inst_1 (List.nil.{u2} α) fι)) (List.dProd.{u1, u2, u3} ι α A _inst_1 _inst_2 (List.nil.{u2} α) fι fA) (GradedMonoid.GOne.one.{u1, u3} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasOne.{u1, u3} ι A _inst_1 _inst_2))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {A : ι -> Type.{u3}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMonoid.{u2, u3} ι A _inst_1] (fι : α -> ι) (fA : forall (a : α), A (fι a)), Eq.{succ u3} (A (List.dProdIndex.{u2, u1} ι α _inst_1 (List.nil.{u1} α) fι)) (List.dProd.{u2, u1, u3} ι α A _inst_1 _inst_2 (List.nil.{u1} α) fι fA) (GradedMonoid.GOne.one.{u2, u3} ι A (AddMonoid.toZero.{u2} ι _inst_1) (GradedMonoid.GMonoid.toGOne.{u2, u3} ι A _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align list.dprod_nil List.dProd_nilₓ'. -/
@[simp]
theorem List.dProd_nil (fι : α → ι) (fA : ∀ a, A (fι a)) :
    (List.nil : List α).dProd fι fA = GradedMonoid.GOne.one :=
  rfl
#align list.dprod_nil List.dProd_nil

/- warning: list.dprod_cons -> List.dProd_cons is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {A : ι -> Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u3} ι A _inst_1] (fι : α -> ι) (fA : forall (a : α), A (fι a)) (a : α) (l : List.{u2} α), Eq.{succ u3} (A (List.dProdIndex.{u1, u2} ι α _inst_1 (List.cons.{u2} α a l) fι)) (List.dProd.{u1, u2, u3} ι α A _inst_1 _inst_2 (List.cons.{u2} α a l) fι fA) (GradedMonoid.GMul.mul.{u1, u3} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasMul.{u1, u3} ι A _inst_1 _inst_2) (fι a) (List.dProdIndex.{u1, u2} ι α _inst_1 l fι) (fA a) (List.dProd.{u1, u2, u3} ι α A _inst_1 _inst_2 l fι fA))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u3}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1] (fι : α -> ι) (fA : forall (a : α), A (fι a)) (a : α) (l : List.{u3} α), Eq.{succ u2} (A (List.dProdIndex.{u1, u3} ι α _inst_1 (List.cons.{u3} α a l) fι)) (List.dProd.{u1, u3, u2} ι α A _inst_1 _inst_2 (List.cons.{u3} α a l) fι fA) (GradedMonoid.GMul.mul.{u1, u2} ι A (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGMul.{u1, u2} ι A _inst_1 _inst_2) (fι a) (List.dProdIndex.{u1, u3} ι α _inst_1 l fι) (fA a) (List.dProd.{u1, u3, u2} ι α A _inst_1 _inst_2 l fι fA))
Case conversion may be inaccurate. Consider using '#align list.dprod_cons List.dProd_consₓ'. -/
-- the `( : _)` in this lemma statement results in the type on the RHS not being unfolded, which
-- is nicer in the goal view.
@[simp]
theorem List.dProd_cons (fι : α → ι) (fA : ∀ a, A (fι a)) (a : α) (l : List α) :
    (a :: l).dProd fι fA = (GradedMonoid.GMul.mul (fA a) (l.dProd fι fA) : _) :=
  rfl
#align list.dprod_cons List.dProd_cons

/- warning: graded_monoid.mk_list_dprod -> GradedMonoid.mk_list_dProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {A : ι -> Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u3} ι A _inst_1] (l : List.{u2} α) (fι : α -> ι) (fA : forall (a : α), A (fι a)), Eq.{max (succ u1) (succ u3)} (GradedMonoid.{u1, u3} ι A) (GradedMonoid.mk.{u1, u3} ι A (List.dProdIndex.{u1, u2} ι α _inst_1 l fι) (List.dProd.{u1, u2, u3} ι α A _inst_1 _inst_2 l fι fA)) (List.prod.{max u1 u3} (GradedMonoid.{u1, u3} ι A) (GradedMonoid.GMul.toMul.{u1, u3} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasMul.{u1, u3} ι A _inst_1 _inst_2)) (GradedMonoid.GOne.toOne.{u1, u3} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasOne.{u1, u3} ι A _inst_1 _inst_2)) (List.map.{u2, max u1 u3} α (GradedMonoid.{u1, u3} ι A) (fun (a : α) => GradedMonoid.mk.{u1, u3} ι A (fι a) (fA a)) l))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {A : ι -> Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMonoid.{u2, u1} ι A _inst_1] (l : List.{u3} α) (fι : α -> ι) (fA : forall (a : α), A (fι a)), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.mk.{u2, u1} ι A (List.dProdIndex.{u2, u3} ι α _inst_1 l fι) (List.dProd.{u2, u3, u1} ι α A _inst_1 _inst_2 l fι fA)) (List.prod.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMul.toMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι (AddMonoid.toAddZeroClass.{u2} ι _inst_1)) (GradedMonoid.GMonoid.toGMul.{u2, u1} ι A _inst_1 _inst_2)) (GradedMonoid.GOne.toOne.{u2, u1} ι A (AddMonoid.toZero.{u2} ι _inst_1) (GradedMonoid.GMonoid.toGOne.{u2, u1} ι A _inst_1 _inst_2)) (List.map.{u3, max u1 u2} α (GradedMonoid.{u2, u1} ι A) (fun (a : α) => GradedMonoid.mk.{u2, u1} ι A (fι a) (fA a)) l))
Case conversion may be inaccurate. Consider using '#align graded_monoid.mk_list_dprod GradedMonoid.mk_list_dProdₓ'. -/
theorem GradedMonoid.mk_list_dProd (l : List α) (fι : α → ι) (fA : ∀ a, A (fι a)) :
    GradedMonoid.mk _ (l.dProd fι fA) = (l.map fun a => GradedMonoid.mk (fι a) (fA a)).Prod :=
  by
  induction l
  · simp
    rfl
  · simp [← l_ih, GradedMonoid.mk_mul_mk, List.prod_cons]
    rfl
#align graded_monoid.mk_list_dprod GradedMonoid.mk_list_dProd

/- warning: graded_monoid.list_prod_map_eq_dprod -> GradedMonoid.list_prod_map_eq_dProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {A : ι -> Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u3} ι A _inst_1] (l : List.{u2} α) (f : α -> (GradedMonoid.{u1, u3} ι A)), Eq.{max (succ u1) (succ u3)} (GradedMonoid.{u1, u3} ι A) (List.prod.{max u1 u3} (GradedMonoid.{u1, u3} ι A) (GradedMonoid.GMul.toMul.{u1, u3} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasMul.{u1, u3} ι A _inst_1 _inst_2)) (GradedMonoid.GOne.toOne.{u1, u3} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasOne.{u1, u3} ι A _inst_1 _inst_2)) (List.map.{u2, max u1 u3} α (GradedMonoid.{u1, u3} ι A) f l)) (GradedMonoid.mk.{u1, u3} ι A (List.dProdIndex.{u1, u2} ι α _inst_1 l (fun (i : α) => Sigma.fst.{u1, u3} ι A (f i))) (List.dProd.{u1, u2, u3} ι α A _inst_1 _inst_2 l (fun (i : α) => Sigma.fst.{u1, u3} ι A (f i)) (fun (i : α) => Sigma.snd.{u1, u3} ι A (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u3}} {A : ι -> Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMonoid.{u2, u1} ι A _inst_1] (l : List.{u3} α) (f : α -> (GradedMonoid.{u2, u1} ι A)), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (List.prod.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMul.toMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι (AddMonoid.toAddZeroClass.{u2} ι _inst_1)) (GradedMonoid.GMonoid.toGMul.{u2, u1} ι A _inst_1 _inst_2)) (GradedMonoid.GOne.toOne.{u2, u1} ι A (AddMonoid.toZero.{u2} ι _inst_1) (GradedMonoid.GMonoid.toGOne.{u2, u1} ι A _inst_1 _inst_2)) (List.map.{u3, max u2 u1} α (GradedMonoid.{u2, u1} ι A) f l)) (GradedMonoid.mk.{u2, u1} ι A (List.dProdIndex.{u2, u3} ι α _inst_1 l (fun (i : α) => Sigma.fst.{u2, u1} ι A (f i))) (List.dProd.{u2, u3, u1} ι α A _inst_1 _inst_2 l (fun (i : α) => Sigma.fst.{u2, u1} ι A (f i)) (fun (i : α) => Sigma.snd.{u2, u1} ι A (f i))))
Case conversion may be inaccurate. Consider using '#align graded_monoid.list_prod_map_eq_dprod GradedMonoid.list_prod_map_eq_dProdₓ'. -/
/-- A variant of `graded_monoid.mk_list_dprod` for rewriting in the other direction. -/
theorem GradedMonoid.list_prod_map_eq_dProd (l : List α) (f : α → GradedMonoid A) :
    (l.map f).Prod = GradedMonoid.mk _ (l.dProd (fun i => (f i).1) fun i => (f i).2) :=
  by
  rw [GradedMonoid.mk_list_dProd, GradedMonoid.mk]
  simp_rw [Sigma.eta]
#align graded_monoid.list_prod_map_eq_dprod GradedMonoid.list_prod_map_eq_dProd

/- warning: graded_monoid.list_prod_of_fn_eq_dprod -> GradedMonoid.list_prod_ofFn_eq_dProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {A : ι -> Type.{u2}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : GradedMonoid.GMonoid.{u1, u2} ι A _inst_1] {n : Nat} (f : (Fin n) -> (GradedMonoid.{u1, u2} ι A)), Eq.{max (succ u1) (succ u2)} (GradedMonoid.{u1, u2} ι A) (List.prod.{max u1 u2} (GradedMonoid.{u1, u2} ι A) (GradedMonoid.GMul.toMul.{u1, u2} ι A (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasMul.{u1, u2} ι A _inst_1 _inst_2)) (GradedMonoid.GOne.toOne.{u1, u2} ι A (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_1)) (GradedMonoid.GMonoid.toGhasOne.{u1, u2} ι A _inst_1 _inst_2)) (List.ofFn.{max u1 u2} (GradedMonoid.{u1, u2} ι A) n f)) (GradedMonoid.mk.{u1, u2} ι A (List.dProdIndex.{u1, 0} ι (Fin n) _inst_1 (List.finRange n) (fun (i : Fin n) => Sigma.fst.{u1, u2} ι A (f i))) (List.dProd.{u1, 0, u2} ι (Fin n) A _inst_1 _inst_2 (List.finRange n) (fun (i : Fin n) => Sigma.fst.{u1, u2} ι A (f i)) (fun (i : Fin n) => Sigma.snd.{u1, u2} ι A (f i))))
but is expected to have type
  forall {ι : Type.{u2}} {A : ι -> Type.{u1}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : GradedMonoid.GMonoid.{u2, u1} ι A _inst_1] {n : Nat} (f : (Fin n) -> (GradedMonoid.{u2, u1} ι A)), Eq.{max (succ u2) (succ u1)} (GradedMonoid.{u2, u1} ι A) (List.prod.{max u2 u1} (GradedMonoid.{u2, u1} ι A) (GradedMonoid.GMul.toMul.{u2, u1} ι A (AddZeroClass.toAdd.{u2} ι (AddMonoid.toAddZeroClass.{u2} ι _inst_1)) (GradedMonoid.GMonoid.toGMul.{u2, u1} ι A _inst_1 _inst_2)) (GradedMonoid.GOne.toOne.{u2, u1} ι A (AddMonoid.toZero.{u2} ι _inst_1) (GradedMonoid.GMonoid.toGOne.{u2, u1} ι A _inst_1 _inst_2)) (List.ofFn.{max u2 u1} (GradedMonoid.{u2, u1} ι A) n f)) (GradedMonoid.mk.{u2, u1} ι A (List.dProdIndex.{u2, 0} ι (Fin n) _inst_1 (List.finRange n) (fun (i : Fin n) => Sigma.fst.{u2, u1} ι A (f i))) (List.dProd.{u2, 0, u1} ι (Fin n) A _inst_1 _inst_2 (List.finRange n) (fun (i : Fin n) => Sigma.fst.{u2, u1} ι A (f i)) (fun (i : Fin n) => Sigma.snd.{u2, u1} ι A (f i))))
Case conversion may be inaccurate. Consider using '#align graded_monoid.list_prod_of_fn_eq_dprod GradedMonoid.list_prod_ofFn_eq_dProdₓ'. -/
theorem GradedMonoid.list_prod_ofFn_eq_dProd {n : ℕ} (f : Fin n → GradedMonoid A) :
    (List.ofFn f).Prod =
      GradedMonoid.mk _ ((List.finRange n).dProd (fun i => (f i).1) fun i => (f i).2) :=
  by rw [List.ofFn_eq_map, GradedMonoid.list_prod_map_eq_dProd]
#align graded_monoid.list_prod_of_fn_eq_dprod GradedMonoid.list_prod_ofFn_eq_dProd

end Dprod

/-! ### Concrete instances -/


section

variable (ι) {R : Type _}

#print One.gOne /-
@[simps one]
instance One.gOne [Zero ι] [One R] : GradedMonoid.GOne fun i : ι => R where one := 1
#align has_one.ghas_one One.gOne
-/

#print Mul.gMul /-
@[simps mul]
instance Mul.gMul [Add ι] [Mul R] : GradedMonoid.GMul fun i : ι => R where mul i j := (· * ·)
#align has_mul.ghas_mul Mul.gMul
-/

#print Monoid.gMonoid /-
/-- If all grades are the same type and themselves form a monoid, then there is a trivial grading
structure. -/
@[simps gnpow]
instance Monoid.gMonoid [AddMonoid ι] [Monoid R] : GradedMonoid.GMonoid fun i : ι => R :=
  { One.gOne ι,
    Mul.gMul ι with
    one_mul := fun a => Sigma.ext (zero_add _) (hEq_of_eq (one_mul _))
    mul_one := fun a => Sigma.ext (add_zero _) (hEq_of_eq (mul_one _))
    mul_assoc := fun a b c => Sigma.ext (add_assoc _ _ _) (hEq_of_eq (mul_assoc _ _ _))
    gnpow := fun n i a => a ^ n
    gnpow_zero' := fun a => Sigma.ext (zero_nsmul _) (hEq_of_eq (Monoid.npow_zero _))
    gnpow_succ' := fun n ⟨i, a⟩ => Sigma.ext (succ_nsmul _ _) (hEq_of_eq (Monoid.npow_succ _ _)) }
#align monoid.gmonoid Monoid.gMonoid
-/

#print CommMonoid.gCommMonoid /-
/-- If all grades are the same type and themselves form a commutative monoid, then there is a
trivial grading structure. -/
instance CommMonoid.gCommMonoid [AddCommMonoid ι] [CommMonoid R] :
    GradedMonoid.GCommMonoid fun i : ι => R :=
  { Monoid.gMonoid ι with
    mul_comm := fun a b => Sigma.ext (add_comm _ _) (hEq_of_eq (mul_comm _ _)) }
#align comm_monoid.gcomm_monoid CommMonoid.gCommMonoid
-/

/- warning: list.dprod_monoid -> List.dProd_monoid is a dubious translation:
lean 3 declaration is
  forall (ι : Type.{u1}) {R : Type.{u2}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : Monoid.{u2} R] (l : List.{u3} α) (fι : α -> ι) (fA : α -> R), Eq.{succ u2} R (List.dProd.{u1, u3, u2} ι α (fun (i : ι) => R) _inst_1 (Monoid.gMonoid.{u1, u2} ι R _inst_1 _inst_2) l fι fA) (List.prod.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (MulOneClass.toHasOne.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (List.map.{u3, u2} α R fA l))
but is expected to have type
  forall (ι : Type.{u2}) {R : Type.{u1}} {α : Type.{u3}} [_inst_1 : AddMonoid.{u2} ι] [_inst_2 : Monoid.{u1} R] (l : List.{u3} α) (fι : α -> ι) (fA : α -> R), Eq.{succ u1} R (List.dProd.{u2, u3, u1} ι α (fun (i : ι) => R) _inst_1 (Monoid.gMonoid.{u2, u1} ι R _inst_1 _inst_2) l fι fA) (List.prod.{u1} R (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R _inst_2)) (Monoid.toOne.{u1} R _inst_2) (List.map.{u3, u1} α R fA l))
Case conversion may be inaccurate. Consider using '#align list.dprod_monoid List.dProd_monoidₓ'. -/
/-- When all the indexed types are the same, the dependent product is just the regular product. -/
@[simp]
theorem List.dProd_monoid {α} [AddMonoid ι] [Monoid R] (l : List α) (fι : α → ι) (fA : α → R) :
    (l.dProd fι fA : (fun i : ι => R) _) = ((l.map fA).Prod : _) :=
  by
  induction l
  · rw [List.dProd_nil, List.map_nil, List.prod_nil]
    rfl
  · rw [List.dProd_cons, List.map_cons, List.prod_cons, l_ih]
    rfl
#align list.dprod_monoid List.dProd_monoid

end

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

#print SetLike.GradedOne /-
/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.GradedOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S) : Prop where
  one_mem : (1 : R) ∈ A 0
#align set_like.has_graded_one SetLike.GradedOne
-/

#print SetLike.one_mem_graded /-
theorem SetLike.one_mem_graded {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : (1 : R) ∈ A 0 :=
  SetLike.GradedOne.one_mem
#align set_like.one_mem_graded SetLike.one_mem_graded
-/

#print SetLike.gOne /-
instance SetLike.gOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : GradedMonoid.GOne fun i => A i
    where one := ⟨1, SetLike.one_mem_graded _⟩
#align set_like.ghas_one SetLike.gOne
-/

#print SetLike.coe_gOne /-
@[simp]
theorem SetLike.coe_gOne {S : Type _} [SetLike S R] [One R] [Zero ι] (A : ι → S)
    [SetLike.GradedOne A] : ↑(@GradedMonoid.GOne.one _ (fun i => A i) _ _) = (1 : R) :=
  rfl
#align set_like.coe_ghas_one SetLike.coe_gOne
-/

#print SetLike.GradedMul /-
/-- A version of `graded_monoid.ghas_one` for internally graded objects. -/
class SetLike.GradedMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) : Prop where
  mul_mem : ∀ ⦃i j⦄ {gi gj}, gi ∈ A i → gj ∈ A j → gi * gj ∈ A (i + j)
#align set_like.has_graded_mul SetLike.GradedMul
-/

#print SetLike.mul_mem_graded /-
theorem SetLike.mul_mem_graded {S : Type _} [SetLike S R] [Mul R] [Add ι] {A : ι → S}
    [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ A j) : gi * gj ∈ A (i + j) :=
  SetLike.GradedMul.mul_mem hi hj
#align set_like.mul_mem_graded SetLike.mul_mem_graded
-/

#print SetLike.gMul /-
instance SetLike.gMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S) [SetLike.GradedMul A] :
    GradedMonoid.GMul fun i => A i
    where mul i j a b := ⟨(a * b : R), SetLike.mul_mem_graded a.Prop b.Prop⟩
#align set_like.ghas_mul SetLike.gMul
-/

#print SetLike.coe_gMul /-
@[simp]
theorem SetLike.coe_gMul {S : Type _} [SetLike S R] [Mul R] [Add ι] (A : ι → S)
    [SetLike.GradedMul A] {i j : ι} (x : A i) (y : A j) :
    ↑(@GradedMonoid.GMul.mul _ (fun i => A i) _ _ _ _ x y) = (x * y : R) :=
  rfl
#align set_like.coe_ghas_mul SetLike.coe_gMul
-/

#print SetLike.GradedMonoid /-
/-- A version of `graded_monoid.gmonoid` for internally graded objects. -/
class SetLike.GradedMonoid {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S) extends
  SetLike.GradedOne A, SetLike.GradedMul A : Prop
#align set_like.graded_monoid SetLike.GradedMonoid
-/

namespace SetLike

variable {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

/- warning: set_like.pow_mem_graded -> SetLike.pow_mem_graded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : SetLike.{u3, u2} S R] [_inst_2 : Monoid.{u2} R] [_inst_3 : AddMonoid.{u1} ι] {A : ι -> S} [_inst_4 : SetLike.GradedMonoid.{u1, u2, u3} ι R S _inst_1 _inst_2 _inst_3 A] (n : Nat) {r : R} {i : ι}, (Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) r (A i)) -> (Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) (HPow.hPow.{u2, 0, u2} R Nat R (instHPow.{u2, 0} R Nat (Monoid.Pow.{u2} R _inst_2)) r n) (A (SMul.smul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_3) n i)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : Monoid.{u3} R] [_inst_3 : AddMonoid.{u1} ι] {A : ι -> S} [_inst_4 : SetLike.GradedMonoid.{u1, u3, u2} ι R S _inst_1 _inst_2 _inst_3 A] (n : Nat) {r : R} {i : ι}, (Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) r (A i)) -> (Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) (HPow.hPow.{u3, 0, u3} R Nat R (instHPow.{u3, 0} R Nat (Monoid.Pow.{u3} R _inst_2)) r n) (A (HSMul.hSMul.{0, u1, u1} Nat ι ι (instHSMul.{0, u1} Nat ι (AddMonoid.SMul.{u1} ι _inst_3)) n i)))
Case conversion may be inaccurate. Consider using '#align set_like.pow_mem_graded SetLike.pow_mem_gradedₓ'. -/
theorem pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) :=
  by
  induction n
  · rw [pow_zero, zero_nsmul]
    exact one_mem_graded _
  · rw [pow_succ', succ_nsmul']
    exact mul_mem_graded n_ih h
#align set_like.pow_mem_graded SetLike.pow_mem_graded

/- warning: set_like.list_prod_map_mem_graded -> SetLike.list_prod_map_mem_graded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : SetLike.{u3, u2} S R] [_inst_2 : Monoid.{u2} R] [_inst_3 : AddMonoid.{u1} ι] {A : ι -> S} [_inst_4 : SetLike.GradedMonoid.{u1, u2, u3} ι R S _inst_1 _inst_2 _inst_3 A] {ι' : Type.{u4}} (l : List.{u4} ι') (i : ι' -> ι) (r : ι' -> R), (forall (j : ι'), (Membership.Mem.{u4, u4} ι' (List.{u4} ι') (List.hasMem.{u4} ι') j l) -> (Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) (r j) (A (i j)))) -> (Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) (List.prod.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (MulOneClass.toHasOne.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (List.map.{u4, u2} ι' R r l)) (A (List.sum.{u1} ι (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (List.map.{u4, u1} ι' ι i l))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : Monoid.{u3} R] [_inst_3 : AddMonoid.{u1} ι] {A : ι -> S} [_inst_4 : SetLike.GradedMonoid.{u1, u3, u2} ι R S _inst_1 _inst_2 _inst_3 A] {ι' : Type.{u4}} (l : List.{u4} ι') (i : ι' -> ι) (r : ι' -> R), (forall (j : ι'), (Membership.mem.{u4, u4} ι' (List.{u4} ι') (List.instMembershipList.{u4} ι') j l) -> (Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) (r j) (A (i j)))) -> (Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) (List.prod.{u3} R (MulOneClass.toMul.{u3} R (Monoid.toMulOneClass.{u3} R _inst_2)) (Monoid.toOne.{u3} R _inst_2) (List.map.{u4, u3} ι' R r l)) (A (List.sum.{u1} ι (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (AddMonoid.toZero.{u1} ι _inst_3) (List.map.{u4, u1} ι' ι i l))))
Case conversion may be inaccurate. Consider using '#align set_like.list_prod_map_mem_graded SetLike.list_prod_map_mem_gradedₓ'. -/
theorem list_prod_map_mem_graded {ι'} (l : List ι') (i : ι' → ι) (r : ι' → R)
    (h : ∀ j ∈ l, r j ∈ A (i j)) : (l.map r).Prod ∈ A (l.map i).Sum :=
  by
  induction l
  · rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil]
    exact one_mem_graded _
  · rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact
      mul_mem_graded (h _ <| List.mem_cons_self _ _)
        (l_ih fun j hj => h _ <| List.mem_cons_of_mem _ hj)
#align set_like.list_prod_map_mem_graded SetLike.list_prod_map_mem_graded

/- warning: set_like.list_prod_of_fn_mem_graded -> SetLike.list_prod_ofFn_mem_graded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : SetLike.{u3, u2} S R] [_inst_2 : Monoid.{u2} R] [_inst_3 : AddMonoid.{u1} ι] {A : ι -> S} [_inst_4 : SetLike.GradedMonoid.{u1, u2, u3} ι R S _inst_1 _inst_2 _inst_3 A] {n : Nat} (i : (Fin n) -> ι) (r : (Fin n) -> R), (forall (j : Fin n), Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) (r j) (A (i j))) -> (Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) (List.prod.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (MulOneClass.toHasOne.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (List.ofFn.{u2} R n r)) (A (List.sum.{u1} ι (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (List.ofFn.{u1} ι n i))))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : Monoid.{u3} R] [_inst_3 : AddMonoid.{u1} ι] {A : ι -> S} [_inst_4 : SetLike.GradedMonoid.{u1, u3, u2} ι R S _inst_1 _inst_2 _inst_3 A] {n : Nat} (i : (Fin n) -> ι) (r : (Fin n) -> R), (forall (j : Fin n), Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) (r j) (A (i j))) -> (Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) (List.prod.{u3} R (MulOneClass.toMul.{u3} R (Monoid.toMulOneClass.{u3} R _inst_2)) (Monoid.toOne.{u3} R _inst_2) (List.ofFn.{u3} R n r)) (A (List.sum.{u1} ι (AddZeroClass.toAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (AddMonoid.toZero.{u1} ι _inst_3) (List.ofFn.{u1} ι n i))))
Case conversion may be inaccurate. Consider using '#align set_like.list_prod_of_fn_mem_graded SetLike.list_prod_ofFn_mem_gradedₓ'. -/
theorem list_prod_ofFn_mem_graded {n} (i : Fin n → ι) (r : Fin n → R) (h : ∀ j, r j ∈ A (i j)) :
    (List.ofFn r).Prod ∈ A (List.ofFn i).Sum :=
  by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  exact list_prod_map_mem_graded _ _ _ fun _ _ => h _
#align set_like.list_prod_of_fn_mem_graded SetLike.list_prod_ofFn_mem_graded

end SetLike

#print SetLike.gMonoid /-
/-- Build a `gmonoid` instance for a collection of subobjects. -/
instance SetLike.gMonoid {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GMonoid fun i => A i :=
  { SetLike.gOne A,
    SetLike.gMul
      A with
    one_mul := fun ⟨i, a, h⟩ => Sigma.subtype_ext (zero_add _) (one_mul _)
    mul_one := fun ⟨i, a, h⟩ => Sigma.subtype_ext (add_zero _) (mul_one _)
    mul_assoc := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ ⟨k, c, hc⟩ =>
      Sigma.subtype_ext (add_assoc _ _ _) (mul_assoc _ _ _)
    gnpow := fun n i a => ⟨a ^ n, SetLike.pow_mem_graded n a.Prop⟩
    gnpow_zero' := fun n => Sigma.subtype_ext (zero_nsmul _) (pow_zero _)
    gnpow_succ' := fun n a => Sigma.subtype_ext (succ_nsmul _ _) (pow_succ _ _) }
#align set_like.gmonoid SetLike.gMonoid
-/

#print SetLike.coe_gnpow /-
@[simp]
theorem SetLike.coe_gnpow {S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] {i : ι} (x : A i) (n : ℕ) :
    ↑(@GradedMonoid.GMonoid.gnpow _ (fun i => A i) _ _ n _ x) = (x ^ n : R) :=
  rfl
#align set_like.coe_gnpow SetLike.coe_gnpow
-/

#print SetLike.gCommMonoid /-
/-- Build a `gcomm_monoid` instance for a collection of subobjects. -/
instance SetLike.gCommMonoid {S : Type _} [SetLike S R] [CommMonoid R] [AddCommMonoid ι] (A : ι → S)
    [SetLike.GradedMonoid A] : GradedMonoid.GCommMonoid fun i => A i :=
  { SetLike.gMonoid A with
    mul_comm := fun ⟨i, a, ha⟩ ⟨j, b, hb⟩ => Sigma.subtype_ext (add_comm _ _) (mul_comm _ _) }
#align set_like.gcomm_monoid SetLike.gCommMonoid
-/

section Dprod

open SetLike SetLike.GradedMonoid

variable {α S : Type _} [SetLike S R] [Monoid R] [AddMonoid ι]

/- warning: set_like.coe_list_dprod -> SetLike.coe_list_dProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} {S : Type.{u4}} [_inst_1 : SetLike.{u4, u2} S R] [_inst_2 : Monoid.{u2} R] [_inst_3 : AddMonoid.{u1} ι] (A : ι -> S) [_inst_4 : SetLike.GradedMonoid.{u1, u2, u4} ι R S _inst_1 _inst_2 _inst_3 A] (fι : α -> ι) (fA : forall (a : α), coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) (l : List.{u3} α), Eq.{succ u2} R ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))) R (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))) R (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))) R (coeBase.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))) R (coeSubtype.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))))))) (List.dProd.{u1, u3, u2} ι α (fun (i : ι) => coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A i)) _inst_3 (SetLike.gMonoid.{u1, u2, u4} ι R S _inst_1 _inst_2 _inst_3 (fun (i : ι) => A i) _inst_4) l fι fA)) (List.prod.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (MulOneClass.toHasOne.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (List.map.{u3, u2} α R (fun (a : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeBase.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeSubtype.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (fι a))))))) (fA a)) l))
but is expected to have type
  forall {ι : Type.{u4}} {R : Type.{u3}} {α : Type.{u1}} {S : Type.{u2}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : Monoid.{u3} R] [_inst_3 : AddMonoid.{u4} ι] (A : ι -> S) [_inst_4 : SetLike.GradedMonoid.{u4, u3, u2} ι R S _inst_1 _inst_2 _inst_3 A] (fι : α -> ι) (fA : forall (a : α), Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A (fι a)))) (l : List.{u1} α), Eq.{succ u3} R (Subtype.val.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Set.{u3} R) (Set.instMembershipSet.{u3} R) x (SetLike.coe.{u2, u3} S R _inst_1 (A (List.dProdIndex.{u4, u1} ι α _inst_3 l fι)))) (List.dProd.{u4, u1, u3} ι α (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A i))) _inst_3 (SetLike.gMonoid.{u4, u3, u2} ι R S _inst_1 _inst_2 _inst_3 (fun (i : ι) => A i) _inst_4) l fι fA)) (List.prod.{u3} R (MulOneClass.toMul.{u3} R (Monoid.toMulOneClass.{u3} R _inst_2)) (Monoid.toOne.{u3} R _inst_2) (List.map.{u1, u3} α R (fun (a : α) => Subtype.val.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Set.{u3} R) (Set.instMembershipSet.{u3} R) x (SetLike.coe.{u2, u3} S R _inst_1 (A (fι a)))) (fA a)) l))
Case conversion may be inaccurate. Consider using '#align set_like.coe_list_dprod SetLike.coe_list_dProdₓ'. -/
/-- Coercing a dependent product of subtypes is the same as taking the regular product of the
coercions. -/
@[simp]
theorem SetLike.coe_list_dProd (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι)
    (fA : ∀ a, A (fι a)) (l : List α) :
    ↑(l.dProd fι fA : (fun i => ↥(A i)) _) = (List.prod (l.map fun a => fA a) : R) :=
  by
  induction l
  · rw [List.dProd_nil, coe_ghas_one, List.map_nil, List.prod_nil]
  · rw [List.dProd_cons, coe_ghas_mul, List.map_cons, List.prod_cons, l_ih]
#align set_like.coe_list_dprod SetLike.coe_list_dProd

include R

/- warning: set_like.list_dprod_eq -> SetLike.list_dProd_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {α : Type.{u3}} {S : Type.{u4}} [_inst_1 : SetLike.{u4, u2} S R] [_inst_2 : Monoid.{u2} R] [_inst_3 : AddMonoid.{u1} ι] (A : ι -> S) [_inst_4 : SetLike.GradedMonoid.{u1, u2, u4} ι R S _inst_1 _inst_2 _inst_3 A] (fι : α -> ι) (fA : forall (a : α), coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) (l : List.{u3} α), Eq.{succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))) (List.dProd.{u1, u3, u2} ι α (fun (i : ι) => coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A i)) _inst_3 (SetLike.gMonoid.{u1, u2, u4} ι R S _inst_1 _inst_2 _inst_3 (fun (i : ι) => A i) _inst_4) l fι fA) (Subtype.mk.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (List.dProdIndex.{u1, u3} ι α _inst_3 l fι))) (List.prod.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (MulOneClass.toHasOne.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (List.map.{u3, u2} α R (fun (a : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeBase.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeSubtype.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (fι a))))))) (fA a)) l)) (Eq.subst.{succ u1} ι (fun (_x : ι) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) (List.prod.{u2} R (MulOneClass.toHasMul.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (MulOneClass.toHasOne.{u2} R (Monoid.toMulOneClass.{u2} R _inst_2)) (List.map.{u3, u2} α R (fun (a : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeBase.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeSubtype.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (fι a))))))) (fA a)) l)) (A _x)) (List.sum.{u1} ι (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (List.map.{u3, u1} α ι fι l)) (List.dProdIndex.{u1, u3} ι α _inst_3 l fι) (Eq.symm.{succ u1} ι (List.dProdIndex.{u1, u3} ι α _inst_3 l fι) (List.sum.{u1} ι (AddZeroClass.toHasAdd.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (AddZeroClass.toHasZero.{u1} ι (AddMonoid.toAddZeroClass.{u1} ι _inst_3)) (List.map.{u3, u1} α ι fι l)) (List.dProdIndex_eq_map_sum.{u1, u3} ι α _inst_3 l fι)) (SetLike.list_prod_map_mem_graded.{u1, u2, u4, u3} ι R S _inst_1 _inst_2 _inst_3 A _inst_4 α l fι (fun (a : α) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeBase.{succ u2, succ u2} (coeSort.{succ u4, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u4, u2} S R _inst_1) (A (fι a))) R (coeSubtype.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (fι a))))))) (fA a)) (fun (i : α) (hi : Membership.Mem.{u3, u3} α (List.{u3} α) (List.hasMem.{u3} α) i l) => Subtype.prop.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u4} R S (SetLike.hasMem.{u4, u2} S R _inst_1) x (A (fι i))) (fA i)))))
but is expected to have type
  forall {ι : Type.{u4}} {R : Type.{u3}} {α : Type.{u1}} {S : Type.{u2}} [_inst_1 : SetLike.{u2, u3} S R] [_inst_2 : Monoid.{u3} R] [_inst_3 : AddMonoid.{u4} ι] (A : ι -> S) [_inst_4 : SetLike.GradedMonoid.{u4, u3, u2} ι R S _inst_1 _inst_2 _inst_3 A] (fι : α -> ι) (fA : forall (a : α), Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A (fι a)))) (l : List.{u1} α), Eq.{succ u3} (Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A (List.dProdIndex.{u4, u1} ι α _inst_3 l fι)))) (List.dProd.{u4, u1, u3} ι α (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A i))) _inst_3 (SetLike.gMonoid.{u4, u3, u2} ι R S _inst_1 _inst_2 _inst_3 (fun (i : ι) => A i) _inst_4) l fι fA) (Subtype.mk.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A (List.dProdIndex.{u4, u1} ι α _inst_3 l fι))) (List.prod.{u3} R (MulOneClass.toMul.{u3} R (Monoid.toMulOneClass.{u3} R _inst_2)) (Monoid.toOne.{u3} R _inst_2) (List.map.{u1, u3} α R (fun (a : α) => Subtype.val.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Set.{u3} R) (Set.instMembershipSet.{u3} R) x (SetLike.coe.{u2, u3} S R _inst_1 (A (fι a)))) (fA a)) l)) (Eq.rec.{0, succ u4} ι (List.sum.{u4} ι (AddZeroClass.toAdd.{u4} ι (AddMonoid.toAddZeroClass.{u4} ι _inst_3)) (AddMonoid.toZero.{u4} ι _inst_3) (List.map.{u1, u4} α ι fι l)) (fun (x._@.Mathlib.Algebra.GradedMonoid._hyg.4836 : ι) (h._@.Mathlib.Algebra.GradedMonoid._hyg.4837 : Eq.{succ u4} ι (List.sum.{u4} ι (AddZeroClass.toAdd.{u4} ι (AddMonoid.toAddZeroClass.{u4} ι _inst_3)) (AddMonoid.toZero.{u4} ι _inst_3) (List.map.{u1, u4} α ι fι l)) x._@.Mathlib.Algebra.GradedMonoid._hyg.4836) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) (List.prod.{u3} R (MulOneClass.toMul.{u3} R (Monoid.toMulOneClass.{u3} R _inst_2)) (Monoid.toOne.{u3} R _inst_2) (List.map.{u1, u3} α R (fun (a : α) => Subtype.val.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Set.{u3} R) (Set.instMembershipSet.{u3} R) x (SetLike.coe.{u2, u3} S R _inst_1 (A (fι a)))) (fA a)) l)) (A x._@.Mathlib.Algebra.GradedMonoid._hyg.4836)) (SetLike.list_prod_map_mem_graded.{u4, u2, u3, u1} ι R S _inst_1 _inst_2 _inst_3 A _inst_4 α l fι (fun (a : α) => Subtype.val.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Set.{u3} R) (Set.instMembershipSet.{u3} R) x (SetLike.coe.{u2, u3} S R _inst_1 (A (fι a)))) (fA a)) (fun (i : α) (x._@.Mathlib.Algebra.GradedMonoid._hyg.4829 : Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) i l) => Subtype.prop.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A (fι i))) (fA i))) (List.dProdIndex.{u4, u1} ι α _inst_3 l fι) (Eq.symm.{succ u4} ι (List.dProdIndex.{u4, u1} ι α _inst_3 l fι) (List.sum.{u4} ι (AddZeroClass.toAdd.{u4} ι (AddMonoid.toAddZeroClass.{u4} ι _inst_3)) (AddMonoid.toZero.{u4} ι _inst_3) (List.map.{u1, u4} α ι fι l)) (List.dProdIndex_eq_map_sum.{u4, u1} ι α _inst_3 l fι))))
Case conversion may be inaccurate. Consider using '#align set_like.list_dprod_eq SetLike.list_dProd_eqₓ'. -/
/-- A version of `list.coe_dprod_set_like` with `subtype.mk`. -/
theorem SetLike.list_dProd_eq (A : ι → S) [SetLike.GradedMonoid A] (fι : α → ι) (fA : ∀ a, A (fι a))
    (l : List α) :
    (l.dProd fι fA : (fun i => ↥(A i)) _) =
      ⟨List.prod (l.map fun a => fA a),
        (l.dProdIndex_eq_map_sum fι).symm ▸
          list_prod_map_mem_graded l _ _ fun i hi => (fA i).Prop⟩ :=
  Subtype.ext <| SetLike.coe_list_dProd _ _ _ _
#align set_like.list_dprod_eq SetLike.list_dProd_eq

end Dprod

end Subobjects

section HomogeneousElements

variable {R S : Type _} [SetLike S R]

#print SetLike.Homogeneous /-
/-- An element `a : R` is said to be homogeneous if there is some `i : ι` such that `a ∈ A i`. -/
def SetLike.Homogeneous (A : ι → S) (a : R) : Prop :=
  ∃ i, a ∈ A i
#align set_like.is_homogeneous SetLike.Homogeneous
-/

/- warning: set_like.is_homogeneous_coe -> SetLike.homogeneous_coe is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : SetLike.{u3, u2} S R] {A : ι -> S} {i : ι} (x : coeSort.{succ u3, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u3, u2} S R _inst_1) (A i)), SetLike.Homogeneous.{u1, u2, u3} ι R S _inst_1 A ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u3, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u3, u2} S R _inst_1) (A i)) R (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u3, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u3, u2} S R _inst_1) (A i)) R (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u3, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u3, u2} S R _inst_1) (A i)) R (coeBase.{succ u2, succ u2} (coeSort.{succ u3, succ (succ u2)} S Type.{u2} (SetLike.hasCoeToSort.{u3, u2} S R _inst_1) (A i)) R (coeSubtype.{succ u2} R (fun (x : R) => Membership.Mem.{u2, u3} R S (SetLike.hasMem.{u3, u2} S R _inst_1) x (A i)))))) x)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u3}} {S : Type.{u2}} [_inst_1 : SetLike.{u2, u3} S R] {A : ι -> S} {i : ι} (x : Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R S (SetLike.instMembership.{u2, u3} S R _inst_1) x (A i))), SetLike.Homogeneous.{u1, u3, u2} ι R S _inst_1 A (Subtype.val.{succ u3} R (fun (x : R) => Membership.mem.{u3, u3} R (Set.{u3} R) (Set.instMembershipSet.{u3} R) x (SetLike.coe.{u2, u3} S R _inst_1 (A i))) x)
Case conversion may be inaccurate. Consider using '#align set_like.is_homogeneous_coe SetLike.homogeneous_coeₓ'. -/
@[simp]
theorem SetLike.homogeneous_coe {A : ι → S} {i} (x : A i) : SetLike.Homogeneous A (x : R) :=
  ⟨i, x.Prop⟩
#align set_like.is_homogeneous_coe SetLike.homogeneous_coe

/- warning: set_like.is_homogeneous_one -> SetLike.homogeneous_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : SetLike.{u3, u2} S R] [_inst_2 : Zero.{u1} ι] [_inst_3 : One.{u2} R] (A : ι -> S) [_inst_4 : SetLike.GradedOne.{u1, u2, u3} ι R S _inst_1 _inst_3 _inst_2 A], SetLike.Homogeneous.{u1, u2, u3} ι R S _inst_1 A (OfNat.ofNat.{u2} R 1 (OfNat.mk.{u2} R 1 (One.one.{u2} R _inst_3)))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : SetLike.{u1, u2} S R] [_inst_2 : Zero.{u3} ι] [_inst_3 : One.{u2} R] (A : ι -> S) [_inst_4 : SetLike.GradedOne.{u3, u2, u1} ι R S _inst_1 _inst_3 _inst_2 A], SetLike.Homogeneous.{u3, u2, u1} ι R S _inst_1 A (OfNat.ofNat.{u2} R 1 (One.toOfNat1.{u2} R _inst_3))
Case conversion may be inaccurate. Consider using '#align set_like.is_homogeneous_one SetLike.homogeneous_oneₓ'. -/
theorem SetLike.homogeneous_one [Zero ι] [One R] (A : ι → S) [SetLike.GradedOne A] :
    SetLike.Homogeneous A (1 : R) :=
  ⟨0, SetLike.one_mem_graded _⟩
#align set_like.is_homogeneous_one SetLike.homogeneous_one

/- warning: set_like.is_homogeneous.mul -> SetLike.homogeneous_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {S : Type.{u3}} [_inst_1 : SetLike.{u3, u2} S R] [_inst_2 : Add.{u1} ι] [_inst_3 : Mul.{u2} R] {A : ι -> S} [_inst_4 : SetLike.GradedMul.{u1, u2, u3} ι R S _inst_1 _inst_3 _inst_2 A] {a : R} {b : R}, (SetLike.Homogeneous.{u1, u2, u3} ι R S _inst_1 A a) -> (SetLike.Homogeneous.{u1, u2, u3} ι R S _inst_1 A b) -> (SetLike.Homogeneous.{u1, u2, u3} ι R S _inst_1 A (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_3) a b))
but is expected to have type
  forall {ι : Type.{u3}} {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : SetLike.{u1, u2} S R] [_inst_2 : Add.{u3} ι] [_inst_3 : Mul.{u2} R] {A : ι -> S} [_inst_4 : SetLike.GradedMul.{u3, u2, u1} ι R S _inst_1 _inst_3 _inst_2 A] {a : R} {b : R}, (SetLike.Homogeneous.{u3, u2, u1} ι R S _inst_1 A a) -> (SetLike.Homogeneous.{u3, u2, u1} ι R S _inst_1 A b) -> (SetLike.Homogeneous.{u3, u2, u1} ι R S _inst_1 A (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R _inst_3) a b))
Case conversion may be inaccurate. Consider using '#align set_like.is_homogeneous.mul SetLike.homogeneous_mulₓ'. -/
theorem SetLike.homogeneous_mul [Add ι] [Mul R] {A : ι → S} [SetLike.GradedMul A] {a b : R} :
    SetLike.Homogeneous A a → SetLike.Homogeneous A b → SetLike.Homogeneous A (a * b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.mul_mem_graded hi hj⟩
#align set_like.is_homogeneous.mul SetLike.homogeneous_mul

#print SetLike.homogeneousSubmonoid /-
/-- When `A` is a `set_like.graded_monoid A`, then the homogeneous elements forms a submonoid. -/
def SetLike.homogeneousSubmonoid [AddMonoid ι] [Monoid R] (A : ι → S) [SetLike.GradedMonoid A] :
    Submonoid R where
  carrier := { a | SetLike.Homogeneous A a }
  one_mem' := SetLike.homogeneous_one A
  mul_mem' a b := SetLike.homogeneous_mul
#align set_like.homogeneous_submonoid SetLike.homogeneousSubmonoid
-/

end HomogeneousElements

