/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module set_theory.ordinal.cantor_normal_form
! leanprover-community/mathlib commit 991ff3b5269848f6dd942ae8e9dd3c946035dc8b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Arithmetic
import Mathbin.SetTheory.Ordinal.Exponential

/-!
# Cantor Normal Form

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

# Implementation notes

We implement `ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/


noncomputable section

universe u

open List

namespace Ordinal

/- warning: ordinal.CNF_rec -> Ordinal.CNFRec is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) {C : Ordinal.{u1} -> Sort.{u2}}, (C (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (forall (o : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (C (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o)))) -> (C o)) -> (forall (o : Ordinal.{u1}), C o)
but is expected to have type
  forall (b : Ordinal.{u1}) {C : Ordinal.{u1} -> Sort.{u2}}, (C (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) -> (forall (o : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) -> (C (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.mod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.pow.{u1}) b (Ordinal.log.{u1} b o)))) -> (C o)) -> (forall (o : Ordinal.{u1}), C o)
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_rec Ordinal.CNFRecₓ'. -/
/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
noncomputable def CNFRec (b : Ordinal) {C : Ordinal → Sort _} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : ∀ o, C o
  | o =>
    if ho : o = 0 then by rwa [ho]
    else
      let hwf := mod_opow_log_lt_self b ho
      H o ho (CNF_rec (o % b ^ log b o))
#align ordinal.CNF_rec Ordinal.CNFRec

/- warning: ordinal.CNF_rec_zero -> Ordinal.CNFRec_zero is a dubious translation:
lean 3 declaration is
  forall {C : Ordinal.{u1} -> Sort.{u2}} (b : Ordinal.{u1}) (H0 : C (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (H : forall (o : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (C (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o)))) -> (C o)), Eq.{u2} (C (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (Ordinal.CNFRec.{u1, u2} b C H0 H (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) H0
but is expected to have type
  forall {C : Ordinal.{u2} -> Sort.{u1}} (b : Ordinal.{u2}) (H0 : C (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) (H : forall (o : Ordinal.{u2}), (Ne.{succ (succ u2)} Ordinal.{u2} o (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) -> (C (HMod.hMod.{succ u2, succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.{u2} (instHMod.{succ u2} Ordinal.{u2} Ordinal.mod.{u2}) o (HPow.hPow.{succ u2, succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.{u2} (instHPow.{succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.pow.{u2}) b (Ordinal.log.{u2} b o)))) -> (C o)), Eq.{u1} (C (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) (Ordinal.CNFRec.{u2, u1} b C H0 H (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) H0
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_rec_zero Ordinal.CNFRec_zeroₓ'. -/
@[simp]
theorem CNFRec_zero {C : Ordinal → Sort _} (b : Ordinal) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : @CNFRec b C H0 H 0 = H0 :=
  by
  rw [CNF_rec, dif_pos rfl]
  rfl
#align ordinal.CNF_rec_zero Ordinal.CNFRec_zero

/- warning: ordinal.CNF_rec_pos -> Ordinal.CNFRec_pos is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) {o : Ordinal.{u1}} {C : Ordinal.{u1} -> Sort.{u2}} (ho : Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (H0 : C (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) (H : forall (o : Ordinal.{u1}), (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (C (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o)))) -> (C o)), Eq.{u2} (C o) (Ordinal.CNFRec.{u1, u2} b C H0 H o) (H o ho (Ordinal.CNFRec.{u1, u2} b C H0 H (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o)))))
but is expected to have type
  forall (b : Ordinal.{u2}) {o : Ordinal.{u2}} {C : Ordinal.{u2} -> Sort.{u1}} (ho : Ne.{succ (succ u2)} Ordinal.{u2} o (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) (H0 : C (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) (H : forall (o : Ordinal.{u2}), (Ne.{succ (succ u2)} Ordinal.{u2} o (OfNat.ofNat.{succ u2} Ordinal.{u2} 0 (Zero.toOfNat0.{succ u2} Ordinal.{u2} Ordinal.zero.{u2}))) -> (C (HMod.hMod.{succ u2, succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.{u2} (instHMod.{succ u2} Ordinal.{u2} Ordinal.mod.{u2}) o (HPow.hPow.{succ u2, succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.{u2} (instHPow.{succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.pow.{u2}) b (Ordinal.log.{u2} b o)))) -> (C o)), Eq.{u1} (C o) (Ordinal.CNFRec.{u2, u1} b C H0 H o) (H o ho (Ordinal.CNFRec.{u2, u1} b C H0 H (HMod.hMod.{succ u2, succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.{u2} (instHMod.{succ u2} Ordinal.{u2} Ordinal.mod.{u2}) o (HPow.hPow.{succ u2, succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.{u2} (instHPow.{succ u2, succ u2} Ordinal.{u2} Ordinal.{u2} Ordinal.pow.{u2}) b (Ordinal.log.{u2} b o)))))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_rec_pos Ordinal.CNFRec_posₓ'. -/
theorem CNFRec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal → Sort _} (ho : o ≠ 0) (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) :
    @CNFRec b C H0 H o = H o ho (@CNFRec b C H0 H _) := by rw [CNF_rec, dif_neg ho]
#align ordinal.CNF_rec_pos Ordinal.CNFRec_pos

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Ordinal.CNF /-
/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNFRec b [] (fun o ho IH => (log b o, o / b ^ log b o)::IH) o
#align ordinal.CNF Ordinal.CNF
-/

#print Ordinal.CNF_zero /-
@[simp]
theorem CNF_zero (b : Ordinal) : CNF b 0 = [] :=
  CNFRec_zero b _ _
#align ordinal.CNF_zero Ordinal.CNF_zero
-/

/- warning: ordinal.CNF_ne_zero -> Ordinal.CNF_ne_zero is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} b o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (Ordinal.log.{u1} b o) (HDiv.hDiv.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHDiv.{succ u1} Ordinal.{u1} Ordinal.hasDiv.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o)))) (Ordinal.CNF.{u1} b (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.hasMod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Ordinal.log.{u1} b o))))))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} b o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (Ordinal.log.{u1} b o) (HDiv.hDiv.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHDiv.{succ u1} Ordinal.{u1} Ordinal.div.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.pow.{u1}) b (Ordinal.log.{u1} b o)))) (Ordinal.CNF.{u1} b (HMod.hMod.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMod.{succ u1} Ordinal.{u1} Ordinal.mod.{u1}) o (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.pow.{u1}) b (Ordinal.log.{u1} b o))))))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_ne_zero Ordinal.CNF_ne_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (ho : o ≠ 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
  CNFRec_pos b ho _ _
#align ordinal.CNF_ne_zero Ordinal.CNF_ne_zero

#print Ordinal.zero_CNF /-
theorem zero_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 0 o = [⟨0, o⟩] := by simp [CNF_ne_zero ho]
#align ordinal.zero_CNF Ordinal.zero_CNF
-/

/- warning: ordinal.one_CNF -> Ordinal.one_CNF is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o) (List.nil.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}))))
but is expected to have type
  forall {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})) o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o) (List.nil.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.one_CNF Ordinal.one_CNFₓ'. -/
theorem one_CNF {o : Ordinal} (ho : o ≠ 0) : CNF 1 o = [⟨0, o⟩] := by simp [CNF_ne_zero ho]
#align ordinal.one_CNF Ordinal.one_CNF

/- warning: ordinal.CNF_of_le_one -> Ordinal.CNF_of_le_one is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toHasLe.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))) -> (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} b o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o) (List.nil.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}))))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) b (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))) -> (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} b o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o) (List.nil.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_of_le_one Ordinal.CNF_of_le_oneₓ'. -/
theorem CNF_of_le_one {b o : Ordinal} (hb : b ≤ 1) (ho : o ≠ 0) : CNF b o = [⟨0, o⟩] :=
  by
  rcases le_one_iff.1 hb with (rfl | rfl)
  · exact zero_CNF ho
  · exact one_CNF ho
#align ordinal.CNF_of_le_one Ordinal.CNF_of_le_one

/- warning: ordinal.CNF_of_lt -> Ordinal.CNF_of_lt is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1})))) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toHasLt.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o b) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} b o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o) (List.nil.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}))))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (Ne.{succ (succ u1)} Ordinal.{u1} o (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1}))) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o b) -> (Eq.{succ (succ u1)} (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (Ordinal.CNF.{u1} b o) (List.cons.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Prod.mk.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o) (List.nil.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_of_lt Ordinal.CNF_of_ltₓ'. -/
theorem CNF_of_lt {b o : Ordinal} (ho : o ≠ 0) (hb : o < b) : CNF b o = [⟨0, o⟩] := by
  simp [CNF_ne_zero ho, log_eq_zero hb]
#align ordinal.CNF_of_lt Ordinal.CNF_of_lt

/- warning: ordinal.CNF_foldr -> Ordinal.CNF_foldr is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) (o : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (List.foldr.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) Ordinal.{u1} (fun (p : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (r : Ordinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.hasAdd.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toHasMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.hasPow.{u1}) b (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} p)) (Prod.snd.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} p)) r) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Ordinal.CNF.{u1} b o)) o
but is expected to have type
  forall (b : Ordinal.{u1}) (o : Ordinal.{u1}), Eq.{succ (succ u1)} Ordinal.{u1} (List.foldr.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) Ordinal.{u1} (fun (p : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (r : Ordinal.{u1}) => HAdd.hAdd.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHAdd.{succ u1} Ordinal.{u1} Ordinal.add.{u1}) (HMul.hMul.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHMul.{succ u1} Ordinal.{u1} (MulZeroClass.toMul.{succ u1} Ordinal.{u1} (MulZeroOneClass.toMulZeroClass.{succ u1} Ordinal.{u1} (MonoidWithZero.toMulZeroOneClass.{succ u1} Ordinal.{u1} Ordinal.monoidWithZero.{u1})))) (HPow.hPow.{succ u1, succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.{u1} (instHPow.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} Ordinal.pow.{u1}) b (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} p)) (Prod.snd.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} p)) r) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Ordinal.CNF.{u1} b o)) o
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_foldr Ordinal.CNF_foldrₓ'. -/
/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr (b o : Ordinal) : (CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o :=
  CNFRec b
    (by
      rw [CNF_zero]
      rfl)
    (fun o ho IH => by rw [CNF_ne_zero ho, foldr_cons, IH, div_add_mod]) o
#align ordinal.CNF_foldr Ordinal.CNF_foldr

/- warning: ordinal.CNF_fst_le_log -> Ordinal.CNF_fst_le_log is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}} {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.Mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.hasMem.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toHasLe.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x) (Ordinal.log.{u1} b o))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}} {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.instMembershipList.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x) (Ordinal.log.{u1} b o))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_fst_le_log Ordinal.CNF_fst_le_logₓ'. -/
/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem CNF_fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → x.1 ≤ log b o :=
  by
  refine' CNF_rec b _ (fun o ho H => _) o
  · simp
  · rw [CNF_ne_zero ho, mem_cons_iff]
    rintro (rfl | h)
    · exact le_rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)
#align ordinal.CNF_fst_le_log Ordinal.CNF_fst_le_log

/- warning: ordinal.CNF_fst_le -> Ordinal.CNF_fst_le is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}} {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.Mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.hasMem.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toHasLe.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x) o)
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}} {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.instMembershipList.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LE.le.{succ u1} Ordinal.{u1} (Preorder.toLE.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x) o)
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_fst_le Ordinal.CNF_fst_leₓ'. -/
/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem CNF_fst_le {b o : Ordinal.{u}} {x : Ordinal × Ordinal} (h : x ∈ CNF b o) : x.1 ≤ o :=
  (CNF_fst_le_log h).trans <| log_le_self _ _
#align ordinal.CNF_fst_le Ordinal.CNF_fst_le

/- warning: ordinal.CNF_lt_snd -> Ordinal.CNF_lt_snd is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}} {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.Mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.hasMem.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toHasLt.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) (Prod.snd.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}} {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.instMembershipList.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) (Prod.snd.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_lt_snd Ordinal.CNF_lt_sndₓ'. -/
/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_lt_snd {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x ∈ CNF b o → 0 < x.2 :=
  by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
  · rw [CNF_ne_zero ho]
    rintro (rfl | h)
    · exact div_opow_log_pos b ho
    · exact IH h
#align ordinal.CNF_lt_snd Ordinal.CNF_lt_snd

/- warning: ordinal.CNF_snd_lt -> Ordinal.CNF_snd_lt is a dubious translation:
lean 3 declaration is
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toHasLt.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))) b) -> (forall {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.Mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.hasMem.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toHasLt.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Prod.snd.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x) b))
but is expected to have type
  forall {b : Ordinal.{u1}} {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})) b) -> (forall {x : Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}}, (Membership.mem.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (List.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) (List.instMembershipList.{succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1})) x (Ordinal.CNF.{u1} b o)) -> (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Prod.snd.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1} x) b))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_snd_lt Ordinal.CNF_snd_ltₓ'. -/
/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x ∈ CNF b o → x.2 < b := by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
  · rw [CNF_ne_zero ho]
    rintro (rfl | h)
    · simpa using div_opow_log_lt o hb
    · exact IH h
#align ordinal.CNF_snd_lt Ordinal.CNF_snd_lt

/- warning: ordinal.CNF_sorted -> Ordinal.CNF_sorted is a dubious translation:
lean 3 declaration is
  forall (b : Ordinal.{u1}) (o : Ordinal.{u1}), List.Sorted.{succ u1} Ordinal.{u1} (GT.gt.{succ u1} Ordinal.{u1} (Preorder.toHasLt.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (List.map.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) Ordinal.{u1} (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Ordinal.CNF.{u1} b o))
but is expected to have type
  forall (b : Ordinal.{u1}) (o : Ordinal.{u1}), List.Sorted.{succ u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Ordinal.CantorNormalForm._hyg.1273 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Ordinal.CantorNormalForm._hyg.1275 : Ordinal.{u1}) => GT.gt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Ordinal.CantorNormalForm._hyg.1273 x._@.Mathlib.SetTheory.Ordinal.CantorNormalForm._hyg.1275) (List.map.{succ u1, succ u1} (Prod.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) Ordinal.{u1} (Prod.fst.{succ u1, succ u1} Ordinal.{u1} Ordinal.{u1}) (Ordinal.CNF.{u1} b o))
Case conversion may be inaccurate. Consider using '#align ordinal.CNF_sorted Ordinal.CNF_sortedₓ'. -/
/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : Ordinal) : ((CNF b o).map Prod.fst).Sorted (· > ·) :=
  by
  refine' CNF_rec b _ (fun o ho IH => _) o
  · simp
  · cases' le_or_lt b 1 with hb hb
    · simp [CNF_of_le_one hb ho]
    · cases' lt_or_le o b with hob hbo
      · simp [CNF_of_lt ho hob]
      · rw [CNF_ne_zero ho, List.map_cons, List.sorted_cons]
        refine' ⟨fun a H => _, IH⟩
        rw [List.mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (CNF_fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb ho hbo)
#align ordinal.CNF_sorted Ordinal.CNF_sorted

end Ordinal

