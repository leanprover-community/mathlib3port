/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland

! This file was ported from Lean 3 source module data.pnat.basic
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pnat.Defs
import Mathbin.Data.Nat.Bits
import Mathbin.Data.Nat.Order.Basic
import Mathbin.Data.Set.Basic
import Mathbin.Algebra.GroupWithZero.Divisibility
import Mathbin.Algebra.Order.Positive.Ring

/-!
# The positive natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
It is defined in `data.pnat.defs`, but most of the development is deferred to here so
that `data.pnat.defs` can have very few imports.
-/


deriving instance AddLeftCancelSemigroup, AddRightCancelSemigroup, AddCommSemigroup,
  LinearOrderedCancelCommMonoid, Add, Mul, Distrib for PNat

namespace PNat

#print PNat.one_add_natPred /-
@[simp]
theorem one_add_natPred (n : ℕ+) : 1 + n.natPred = n := by
  rw [nat_pred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]
#align pnat.one_add_nat_pred PNat.one_add_natPred
-/

#print PNat.natPred_add_one /-
@[simp]
theorem natPred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_nat_pred
#align pnat.nat_pred_add_one PNat.natPred_add_one
-/

/- warning: pnat.nat_pred_strict_mono -> PNat.natPred_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{0, 0} PNat Nat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) PNat.natPred
but is expected to have type
  StrictMono.{0, 0} PNat Nat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) PNat.natPred
Case conversion may be inaccurate. Consider using '#align pnat.nat_pred_strict_mono PNat.natPred_strictMonoₓ'. -/
@[mono]
theorem natPred_strictMono : StrictMono natPred := fun m n h => Nat.pred_lt_pred m.2.ne' h
#align pnat.nat_pred_strict_mono PNat.natPred_strictMono

/- warning: pnat.nat_pred_monotone -> PNat.natPred_monotone is a dubious translation:
lean 3 declaration is
  Monotone.{0, 0} PNat Nat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))) (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) PNat.natPred
but is expected to have type
  Monotone.{0, 0} PNat Nat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))) (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) PNat.natPred
Case conversion may be inaccurate. Consider using '#align pnat.nat_pred_monotone PNat.natPred_monotoneₓ'. -/
@[mono]
theorem natPred_monotone : Monotone natPred :=
  natPred_strictMono.Monotone
#align pnat.nat_pred_monotone PNat.natPred_monotone

#print PNat.natPred_injective /-
theorem natPred_injective : Function.Injective natPred :=
  natPred_strictMono.Injective
#align pnat.nat_pred_injective PNat.natPred_injective
-/

/- warning: pnat.nat_pred_lt_nat_pred -> PNat.natPred_lt_natPred is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {n : PNat}, Iff (LT.lt.{0} Nat Nat.hasLt (PNat.natPred m) (PNat.natPred n)) (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n)
but is expected to have type
  forall {m : PNat} {n : PNat}, Iff (LT.lt.{0} Nat instLTNat (PNat.natPred m) (PNat.natPred n)) (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n)
Case conversion may be inaccurate. Consider using '#align pnat.nat_pred_lt_nat_pred PNat.natPred_lt_natPredₓ'. -/
@[simp]
theorem natPred_lt_natPred {m n : ℕ+} : m.natPred < n.natPred ↔ m < n :=
  natPred_strictMono.lt_iff_lt
#align pnat.nat_pred_lt_nat_pred PNat.natPred_lt_natPred

/- warning: pnat.nat_pred_le_nat_pred -> PNat.natPred_le_natPred is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {n : PNat}, Iff (LE.le.{0} Nat Nat.hasLe (PNat.natPred m) (PNat.natPred n)) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n)
but is expected to have type
  forall {m : PNat} {n : PNat}, Iff (LE.le.{0} Nat instLENat (PNat.natPred m) (PNat.natPred n)) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n)
Case conversion may be inaccurate. Consider using '#align pnat.nat_pred_le_nat_pred PNat.natPred_le_natPredₓ'. -/
@[simp]
theorem natPred_le_natPred {m n : ℕ+} : m.natPred ≤ n.natPred ↔ m ≤ n :=
  natPred_strictMono.le_iff_le
#align pnat.nat_pred_le_nat_pred PNat.natPred_le_natPred

#print PNat.natPred_inj /-
@[simp]
theorem natPred_inj {m n : ℕ+} : m.natPred = n.natPred ↔ m = n :=
  natPred_injective.eq_iff
#align pnat.nat_pred_inj PNat.natPred_inj
-/

end PNat

namespace Nat

/- warning: nat.succ_pnat_strict_mono -> Nat.succPNat_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{0, 0} Nat PNat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))) Nat.succPNat
but is expected to have type
  StrictMono.{0, 0} Nat PNat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))) Nat.succPNat
Case conversion may be inaccurate. Consider using '#align nat.succ_pnat_strict_mono Nat.succPNat_strictMonoₓ'. -/
@[mono]
theorem succPNat_strictMono : StrictMono succPNat := fun m n => Nat.succ_lt_succ
#align nat.succ_pnat_strict_mono Nat.succPNat_strictMono

/- warning: nat.succ_pnat_mono -> Nat.succPNat_mono is a dubious translation:
lean 3 declaration is
  Monotone.{0, 0} Nat PNat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))) Nat.succPNat
but is expected to have type
  Monotone.{0, 0} Nat PNat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))) Nat.succPNat
Case conversion may be inaccurate. Consider using '#align nat.succ_pnat_mono Nat.succPNat_monoₓ'. -/
@[mono]
theorem succPNat_mono : Monotone succPNat :=
  succPNat_strictMono.Monotone
#align nat.succ_pnat_mono Nat.succPNat_mono

/- warning: nat.succ_pnat_lt_succ_pnat -> Nat.succPNat_lt_succPNat is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (Nat.succPNat m) (Nat.succPNat n)) (LT.lt.{0} Nat Nat.hasLt m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (Nat.succPNat m) (Nat.succPNat n)) (LT.lt.{0} Nat instLTNat m n)
Case conversion may be inaccurate. Consider using '#align nat.succ_pnat_lt_succ_pnat Nat.succPNat_lt_succPNatₓ'. -/
@[simp]
theorem succPNat_lt_succPNat {m n : ℕ} : m.succPnat < n.succPnat ↔ m < n :=
  succPNat_strictMono.lt_iff_lt
#align nat.succ_pnat_lt_succ_pnat Nat.succPNat_lt_succPNat

/- warning: nat.succ_pnat_le_succ_pnat -> Nat.succPNat_le_succPNat is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (Nat.succPNat m) (Nat.succPNat n)) (LE.le.{0} Nat Nat.hasLe m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (Nat.succPNat m) (Nat.succPNat n)) (LE.le.{0} Nat instLENat m n)
Case conversion may be inaccurate. Consider using '#align nat.succ_pnat_le_succ_pnat Nat.succPNat_le_succPNatₓ'. -/
@[simp]
theorem succPNat_le_succPNat {m n : ℕ} : m.succPnat ≤ n.succPnat ↔ m ≤ n :=
  succPNat_strictMono.le_iff_le
#align nat.succ_pnat_le_succ_pnat Nat.succPNat_le_succPNat

#print Nat.succPNat_injective /-
theorem succPNat_injective : Function.Injective succPNat :=
  succPNat_strictMono.Injective
#align nat.succ_pnat_injective Nat.succPNat_injective
-/

#print Nat.succPNat_inj /-
@[simp]
theorem succPNat_inj {n m : ℕ} : succPNat n = succPNat m ↔ n = m :=
  succPNat_injective.eq_iff
#align nat.succ_pnat_inj Nat.succPNat_inj
-/

end Nat

namespace PNat

open Nat

#print PNat.coe_inj /-
/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
@[simp, norm_cast]
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  SetCoe.ext_iff
#align pnat.coe_inj PNat.coe_inj
-/

/- warning: pnat.add_coe -> PNat.add_coe is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (n : PNat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) m n)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) n))
but is expected to have type
  forall (m : PNat) (n : PNat), Eq.{1} Nat (PNat.val (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) m n)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (PNat.val m) (PNat.val n))
Case conversion may be inaccurate. Consider using '#align pnat.add_coe PNat.add_coeₓ'. -/
@[simp, norm_cast]
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl
#align pnat.add_coe PNat.add_coe

/- warning: pnat.coe_add_hom -> PNat.coeAddHom is a dubious translation:
lean 3 declaration is
  AddHom.{0, 0} PNat Nat PNat.hasAdd Nat.hasAdd
but is expected to have type
  AddHom.{0, 0} PNat Nat instPNatAdd instAddNat
Case conversion may be inaccurate. Consider using '#align pnat.coe_add_hom PNat.coeAddHomₓ'. -/
/-- `pnat.coe` promoted to an `add_hom`, that is, a morphism which preserves addition. -/
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := coe
  map_add' := add_coe
#align pnat.coe_add_hom PNat.coeAddHom

instance : CovariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.covariantClass_add_le

instance : CovariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.covariantClass_add_lt

instance : ContravariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.contravariantClass_add_le

instance : ContravariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.contravariantClass_add_lt

#print Equiv.pnatEquivNat /-
/-- An equivalence between `ℕ+` and `ℕ` given by `pnat.nat_pred` and `nat.succ_pnat`. -/
@[simps (config := { fullyApplied := false })]
def Equiv.pnatEquivNat : ℕ+ ≃ ℕ where
  toFun := PNat.natPred
  invFun := Nat.succPNat
  left_inv := succ_pnat_nat_pred
  right_inv := Nat.natPred_succPNat
#align equiv.pnat_equiv_nat Equiv.pnatEquivNat
-/

/- warning: order_iso.pnat_iso_nat -> OrderIso.pnatIsoNat is a dubious translation:
lean 3 declaration is
  OrderIso.{0, 0} PNat Nat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) Nat.hasLe
but is expected to have type
  OrderIso.{0, 0} PNat Nat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) instLENat
Case conversion may be inaccurate. Consider using '#align order_iso.pnat_iso_nat OrderIso.pnatIsoNatₓ'. -/
/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps (config := { fullyApplied := false }) apply]
def OrderIso.pnatIsoNat : ℕ+ ≃o ℕ
    where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' _ _ := natPred_le_natPred
#align order_iso.pnat_iso_nat OrderIso.pnatIsoNat

/- warning: order_iso.pnat_iso_nat_symm_apply -> OrderIso.pnatIsoNat_symm_apply is a dubious translation:
lean 3 declaration is
  Eq.{1} (Nat -> PNat) (coeFn.{1, 1} (OrderIso.{0, 0} Nat PNat Nat.hasLe (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))) (fun (_x : RelIso.{0, 0} Nat PNat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) => Nat -> PNat) (RelIso.hasCoeToFun.{0, 0} Nat PNat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) (OrderIso.symm.{0, 0} PNat Nat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) Nat.hasLe OrderIso.pnatIsoNat)) Nat.succPNat
but is expected to have type
  Eq.{1} (forall (ᾰ : Nat), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => PNat) ᾰ) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat PNat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => PNat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat PNat) Nat PNat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat PNat)) (RelEmbedding.toEmbedding.{0, 0} Nat PNat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : PNat) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : PNat) => LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{0, 0} Nat PNat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : PNat) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : PNat) => LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (OrderIso.symm.{0, 0} PNat Nat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) instLENat OrderIso.pnatIsoNat)))) Nat.succPNat
Case conversion may be inaccurate. Consider using '#align order_iso.pnat_iso_nat_symm_apply OrderIso.pnatIsoNat_symm_applyₓ'. -/
@[simp]
theorem OrderIso.pnatIsoNat_symm_apply : ⇑OrderIso.pnatIsoNat.symm = Nat.succPNat :=
  rfl
#align order_iso.pnat_iso_nat_symm_apply OrderIso.pnatIsoNat_symm_apply

/- warning: pnat.lt_add_one_iff -> PNat.lt_add_one_iff is a dubious translation:
lean 3 declaration is
  forall {a : PNat} {b : PNat}, Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) a (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) b (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) a b)
but is expected to have type
  forall {a : PNat} {b : PNat}, Iff (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) a (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) b (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) a b)
Case conversion may be inaccurate. Consider using '#align pnat.lt_add_one_iff PNat.lt_add_one_iffₓ'. -/
theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := fun a b => Nat.lt_add_one_iff
#align pnat.lt_add_one_iff PNat.lt_add_one_iff

/- warning: pnat.add_one_le_iff -> PNat.add_one_le_iff is a dubious translation:
lean 3 declaration is
  forall {a : PNat} {b : PNat}, Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) a (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) b) (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) a b)
but is expected to have type
  forall {a : PNat} {b : PNat}, Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) a (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) b) (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) a b)
Case conversion may be inaccurate. Consider using '#align pnat.add_one_le_iff PNat.add_one_le_iffₓ'. -/
theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := fun a b => Nat.add_one_le_iff
#align pnat.add_one_le_iff PNat.add_one_le_iff

instance : OrderBot ℕ+ where
  bot := 1
  bot_le a := a.property

/- warning: pnat.bot_eq_one -> PNat.bot_eq_one is a dubious translation:
lean 3 declaration is
  Eq.{1} PNat (Bot.bot.{0} PNat (OrderBot.toHasBot.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) PNat.orderBot)) (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))
but is expected to have type
  Eq.{1} PNat (Bot.bot.{0} PNat (OrderBot.toBot.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) PNat.instOrderBotPNatToLEToPreorderToPartialOrderToOrderedCancelCommMonoidInstPNatLinearOrderedCancelCommMonoid)) (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))
Case conversion may be inaccurate. Consider using '#align pnat.bot_eq_one PNat.bot_eq_oneₓ'. -/
@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl
#align pnat.bot_eq_one PNat.bot_eq_one

/- warning: pnat.mk_bit0 -> PNat.mk_bit0 is a dubious translation:
lean 3 declaration is
  forall (n : Nat) {h : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (bit0.{0} Nat Nat.hasAdd n)}, Eq.{1} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (bit0.{0} Nat Nat.hasAdd n) h) (bit0.{0} PNat PNat.hasAdd (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) n (Nat.pos_of_bit0_pos n h)))
but is expected to have type
  forall (n : Nat) {h : LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (bit0.{0} Nat instAddNat n)}, Eq.{1} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (bit0.{0} Nat instAddNat n) h) (bit0.{0} PNat instPNatAdd (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) n (Nat.pos_of_bit0_pos n h)))
Case conversion may be inaccurate. Consider using '#align pnat.mk_bit0 PNat.mk_bit0ₓ'. -/
-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) :=
  rfl
#align pnat.mk_bit0 PNat.mk_bit0

/- warning: pnat.mk_bit1 -> PNat.mk_bit1 is a dubious translation:
lean 3 declaration is
  forall (n : Nat) {h : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (bit1.{0} Nat Nat.hasOne Nat.hasAdd n)} {k : LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n}, Eq.{1} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (bit1.{0} Nat Nat.hasOne Nat.hasAdd n) h) (bit1.{0} PNat PNat.hasOne PNat.hasAdd (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) n k))
but is expected to have type
  forall (n : Nat) {h : LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat n)} {k : LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n}, Eq.{1} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat n) h) (bit1.{0} PNat instOnePNat instPNatAdd (Subtype.mk.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) n k))
Case conversion may be inaccurate. Consider using '#align pnat.mk_bit1 PNat.mk_bit1ₓ'. -/
@[simp]
theorem mk_bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) :=
  rfl
#align pnat.mk_bit1 PNat.mk_bit1

/- warning: pnat.bit0_le_bit0 -> PNat.bit0_le_bit0 is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (bit0.{0} PNat PNat.hasAdd n) (bit0.{0} PNat PNat.hasAdd m)) (LE.le.{0} Nat Nat.hasLe (bit0.{0} Nat Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) n)) (bit0.{0} Nat Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m)))
but is expected to have type
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (bit0.{0} PNat instPNatAdd n) (bit0.{0} PNat instPNatAdd m)) (LE.le.{0} Nat instLENat (bit0.{0} Nat instAddNat (PNat.val n)) (bit0.{0} Nat instAddNat (PNat.val m)))
Case conversion may be inaccurate. Consider using '#align pnat.bit0_le_bit0 PNat.bit0_le_bit0ₓ'. -/
-- Some lemmas that rewrite inequalities between explicit numerals in `ℕ+`
-- into the corresponding inequalities in `ℕ`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp]
theorem bit0_le_bit0 (n m : ℕ+) : bit0 n ≤ bit0 m ↔ bit0 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl
#align pnat.bit0_le_bit0 PNat.bit0_le_bit0

/- warning: pnat.bit0_le_bit1 -> PNat.bit0_le_bit1 is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (bit0.{0} PNat PNat.hasAdd n) (bit1.{0} PNat PNat.hasOne PNat.hasAdd m)) (LE.le.{0} Nat Nat.hasLe (bit0.{0} Nat Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) n)) (bit1.{0} Nat Nat.hasOne Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m)))
but is expected to have type
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (bit0.{0} PNat instPNatAdd n) (bit1.{0} PNat instOnePNat instPNatAdd m)) (LE.le.{0} Nat instLENat (bit0.{0} Nat instAddNat (PNat.val n)) (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat (PNat.val m)))
Case conversion may be inaccurate. Consider using '#align pnat.bit0_le_bit1 PNat.bit0_le_bit1ₓ'. -/
@[simp]
theorem bit0_le_bit1 (n m : ℕ+) : bit0 n ≤ bit1 m ↔ bit0 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl
#align pnat.bit0_le_bit1 PNat.bit0_le_bit1

/- warning: pnat.bit1_le_bit0 -> PNat.bit1_le_bit0 is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (bit1.{0} PNat PNat.hasOne PNat.hasAdd n) (bit0.{0} PNat PNat.hasAdd m)) (LE.le.{0} Nat Nat.hasLe (bit1.{0} Nat Nat.hasOne Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) n)) (bit0.{0} Nat Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m)))
but is expected to have type
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (bit1.{0} PNat instOnePNat instPNatAdd n) (bit0.{0} PNat instPNatAdd m)) (LE.le.{0} Nat instLENat (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat (PNat.val n)) (bit0.{0} Nat instAddNat (PNat.val m)))
Case conversion may be inaccurate. Consider using '#align pnat.bit1_le_bit0 PNat.bit1_le_bit0ₓ'. -/
@[simp]
theorem bit1_le_bit0 (n m : ℕ+) : bit1 n ≤ bit0 m ↔ bit1 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl
#align pnat.bit1_le_bit0 PNat.bit1_le_bit0

/- warning: pnat.bit1_le_bit1 -> PNat.bit1_le_bit1 is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (bit1.{0} PNat PNat.hasOne PNat.hasAdd n) (bit1.{0} PNat PNat.hasOne PNat.hasAdd m)) (LE.le.{0} Nat Nat.hasLe (bit1.{0} Nat Nat.hasOne Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) n)) (bit1.{0} Nat Nat.hasOne Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m)))
but is expected to have type
  forall (n : PNat) (m : PNat), Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (bit1.{0} PNat instOnePNat instPNatAdd n) (bit1.{0} PNat instOnePNat instPNatAdd m)) (LE.le.{0} Nat instLENat (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat (PNat.val n)) (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat (PNat.val m)))
Case conversion may be inaccurate. Consider using '#align pnat.bit1_le_bit1 PNat.bit1_le_bit1ₓ'. -/
@[simp]
theorem bit1_le_bit1 (n m : ℕ+) : bit1 n ≤ bit1 m ↔ bit1 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl
#align pnat.bit1_le_bit1 PNat.bit1_le_bit1

/- warning: pnat.mul_coe -> PNat.mul_coe is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (n : PNat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat PNat.hasMul) m n)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) n))
but is expected to have type
  forall (m : PNat) (n : PNat), Eq.{1} Nat (PNat.val (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat instPNatMul) m n)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (PNat.val m) (PNat.val n))
Case conversion may be inaccurate. Consider using '#align pnat.mul_coe PNat.mul_coeₓ'. -/
@[simp, norm_cast]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl
#align pnat.mul_coe PNat.mul_coe

/- warning: pnat.coe_monoid_hom -> PNat.coeMonoidHom is a dubious translation:
lean 3 declaration is
  MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))
but is expected to have type
  MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))
Case conversion may be inaccurate. Consider using '#align pnat.coe_monoid_hom PNat.coeMonoidHomₓ'. -/
/-- `pnat.coe` promoted to a `monoid_hom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := coe
  map_one' := one_coe
  map_mul' := mul_coe
#align pnat.coe_monoid_hom PNat.coeMonoidHom

/- warning: pnat.coe_coe_monoid_hom -> PNat.coe_coeMonoidHom is a dubious translation:
lean 3 declaration is
  Eq.{1} ((fun (_x : MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) => PNat -> Nat) PNat.coeMonoidHom) (coeFn.{1, 1} (MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) (fun (_x : MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) => PNat -> Nat) (MonoidHom.hasCoeToFun.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) PNat.coeMonoidHom) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))))
but is expected to have type
  Eq.{1} (forall (a : PNat), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : PNat) => Nat) a) (FunLike.coe.{1, 1, 1} (MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) PNat (fun (_x : PNat) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : PNat) => Nat) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) PNat Nat (MulOneClass.toMul.{0} PNat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) (MulOneClass.toMul.{0} Nat (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidHom.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))) PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring))) (MonoidHom.monoidHomClass.{0, 0} PNat Nat (Monoid.toMulOneClass.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) (MulZeroOneClass.toMulOneClass.{0} Nat (NonAssocSemiring.toMulZeroOneClass.{0} Nat (Semiring.toNonAssocSemiring.{0} Nat Nat.semiring)))))) PNat.coeMonoidHom) (Coe.coe.{1, 1} PNat Nat coePNatNat)
Case conversion may be inaccurate. Consider using '#align pnat.coe_coe_monoid_hom PNat.coe_coeMonoidHomₓ'. -/
@[simp]
theorem coe_coeMonoidHom : (coeMonoidHom : ℕ+ → ℕ) = coe :=
  rfl
#align pnat.coe_coe_monoid_hom PNat.coe_coeMonoidHom

/- warning: pnat.le_one_iff -> PNat.le_one_iff is a dubious translation:
lean 3 declaration is
  forall {n : PNat}, Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) (Eq.{1} PNat n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))
but is expected to have type
  forall {n : PNat}, Iff (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Eq.{1} PNat n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align pnat.le_one_iff PNat.le_one_iffₓ'. -/
@[simp]
theorem le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 :=
  le_bot_iff
#align pnat.le_one_iff PNat.le_one_iff

/- warning: pnat.lt_add_left -> PNat.lt_add_left is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) n (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) m n)
but is expected to have type
  forall (n : PNat) (m : PNat), LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) n (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) m n)
Case conversion may be inaccurate. Consider using '#align pnat.lt_add_left PNat.lt_add_leftₓ'. -/
theorem lt_add_left (n m : ℕ+) : n < m + n :=
  lt_add_of_pos_left _ m.2
#align pnat.lt_add_left PNat.lt_add_left

/- warning: pnat.lt_add_right -> PNat.lt_add_right is a dubious translation:
lean 3 declaration is
  forall (n : PNat) (m : PNat), LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) n (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n m)
but is expected to have type
  forall (n : PNat) (m : PNat), LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) n (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n m)
Case conversion may be inaccurate. Consider using '#align pnat.lt_add_right PNat.lt_add_rightₓ'. -/
theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)
#align pnat.lt_add_right PNat.lt_add_right

/- warning: pnat.coe_bit0 -> PNat.coe_bit0 is a dubious translation:
lean 3 declaration is
  forall (a : PNat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) (bit0.{0} PNat PNat.hasAdd a)) (bit0.{0} Nat Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat), Eq.{1} Nat (PNat.val (bit0.{0} PNat instPNatAdd a)) (bit0.{0} Nat instAddNat (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.coe_bit0 PNat.coe_bit0ₓ'. -/
@[simp, norm_cast]
theorem coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) :=
  rfl
#align pnat.coe_bit0 PNat.coe_bit0

/- warning: pnat.coe_bit1 -> PNat.coe_bit1 is a dubious translation:
lean 3 declaration is
  forall (a : PNat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) (bit1.{0} PNat PNat.hasOne PNat.hasAdd a)) (bit1.{0} Nat Nat.hasOne Nat.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat), Eq.{1} Nat (PNat.val (bit1.{0} PNat instOnePNat instPNatAdd a)) (bit1.{0} Nat (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring) instAddNat (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.coe_bit1 PNat.coe_bit1ₓ'. -/
@[simp, norm_cast]
theorem coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) :=
  rfl
#align pnat.coe_bit1 PNat.coe_bit1

/- warning: pnat.pow_coe -> PNat.pow_coe is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (n : Nat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) (HPow.hPow.{0, 0, 0} PNat Nat PNat (instHPow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) m n)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m) n)
but is expected to have type
  forall (m : PNat) (n : Nat), Eq.{1} Nat (PNat.val (Pow.pow.{0, 0} PNat Nat (Monoid.Pow.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))))) m n)) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) (PNat.val m) n)
Case conversion may be inaccurate. Consider using '#align pnat.pow_coe PNat.pow_coeₓ'. -/
@[simp, norm_cast]
theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
  rfl
#align pnat.pow_coe PNat.pow_coe

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : Sub ℕ+ :=
  ⟨fun a b => toPNat' (a - b : ℕ)⟩

/- warning: pnat.sub_coe -> PNat.sub_coe is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) (HSub.hSub.{0, 0, 0} PNat PNat PNat (instHSub.{0} PNat PNat.hasSub) a b)) (ite.{1} Nat (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) b a) (Subtype.decidableLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (fun (a : Nat) (b : Nat) => Nat.decidableLt a b) (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) b a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (PNat.val (HSub.hSub.{0, 0, 0} PNat PNat PNat (instHSub.{0} PNat PNat.instSubPNat) a b)) (ite.{1} Nat (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) b a) (instDecidableLtToLTToPreorderToPartialOrder.{0} PNat instPNatLinearOrder b a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val a) (PNat.val b)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pnat.sub_coe PNat.sub_coeₓ'. -/
theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 :=
  by
  change (to_pnat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact to_pnat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b)]
    rfl
#align pnat.sub_coe PNat.sub_coe

/- warning: pnat.add_sub_of_lt -> PNat.add_sub_of_lt is a dubious translation:
lean 3 declaration is
  forall {a : PNat} {b : PNat}, (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) a b) -> (Eq.{1} PNat (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) a (HSub.hSub.{0, 0, 0} PNat PNat PNat (instHSub.{0} PNat PNat.hasSub) b a)) b)
but is expected to have type
  forall {a : PNat} {b : PNat}, (LT.lt.{0} PNat (Preorder.toLT.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) a b) -> (Eq.{1} PNat (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) a (HSub.hSub.{0, 0, 0} PNat PNat PNat (instHSub.{0} PNat PNat.instSubPNat) b a)) b)
Case conversion may be inaccurate. Consider using '#align pnat.add_sub_of_lt PNat.add_sub_of_ltₓ'. -/
theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b := fun h =>
  Eq <| by
    rw [add_coe, sub_coe, if_pos h]
    exact add_tsub_cancel_of_le h.le
#align pnat.add_sub_of_lt PNat.add_sub_of_lt

/- warning: pnat.exists_eq_succ_of_ne_one -> PNat.exists_eq_succ_of_ne_one is a dubious translation:
lean 3 declaration is
  forall {n : PNat}, (Ne.{1} PNat n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) -> (Exists.{1} PNat (fun (k : PNat) => Eq.{1} PNat n (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) k (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))))
but is expected to have type
  forall {n : PNat}, (Ne.{1} PNat n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> (Exists.{1} PNat (fun (k : PNat) => Eq.{1} PNat n (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) k (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align pnat.exists_eq_succ_of_ne_one PNat.exists_eq_succ_of_ne_oneₓ'. -/
/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (h1 : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h1 => False.elim <| h1 rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩
#align pnat.exists_eq_succ_of_ne_one PNat.exists_eq_succ_of_ne_one

/- warning: pnat.case_strong_induction_on -> PNat.caseStrongInductionOn is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Sort.{u1}} (a : PNat), (p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) -> (forall (n : PNat), (forall (m : PNat), (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n) -> (p m)) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))) -> (p a)
but is expected to have type
  forall {p : PNat -> Sort.{u1}} (a : PNat), (p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> (forall (n : PNat), (forall (m : PNat), (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n) -> (p m)) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (p a)
Case conversion may be inaccurate. Consider using '#align pnat.case_strong_induction_on PNat.caseStrongInductionOnₓ'. -/
/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def caseStrongInductionOn {p : ℕ+ → Sort _} (a : ℕ+) (hz : p 1)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a :=
  by
  apply strong_induction_on a
  rintro ⟨k, kprop⟩ hk
  cases' k with k
  · exact (lt_irrefl 0 kprop).elim
  cases' k with k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (lt_succ_iff.2 hm)
#align pnat.case_strong_induction_on PNat.caseStrongInductionOn

/- warning: pnat.rec_on -> PNat.recOn is a dubious translation:
lean 3 declaration is
  forall (n : PNat) {p : PNat -> Sort.{u1}}, (p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) -> (forall (n : PNat), (p n) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))) -> (p n)
but is expected to have type
  forall (n : PNat) {p : PNat -> Sort.{u1}}, (p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) -> (forall (n : PNat), (p n) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (p n)
Case conversion may be inaccurate. Consider using '#align pnat.rec_on PNat.recOnₓ'. -/
/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim]
def recOn (n : ℕ+) {p : ℕ+ → Sort _} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n :=
  by
  rcases n with ⟨n, h⟩
  induction' n with n IH
  · exact absurd h (by decide)
  · cases' n with n
    · exact p1
    · exact hp _ (IH n.succ_pos)
#align pnat.rec_on PNat.recOn

/- warning: pnat.rec_on_one -> PNat.recOn_one is a dubious translation:
lean 3 declaration is
  forall {p : PNat -> Sort.{u1}} (p1 : p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) (hp : forall (n : PNat), (p n) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))), Eq.{u1} (p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) (PNat.recOn.{u1} (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))) p p1 hp) p1
but is expected to have type
  forall {p : PNat -> Sort.{u1}} (p1 : p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (hp : forall (n : PNat), (p n) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))), Eq.{u1} (p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (PNat.recOn.{u1} (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) p p1 hp) p1
Case conversion may be inaccurate. Consider using '#align pnat.rec_on_one PNat.recOn_oneₓ'. -/
@[simp]
theorem recOn_one {p} (p1 hp) : @PNat.recOn 1 p p1 hp = p1 :=
  rfl
#align pnat.rec_on_one PNat.recOn_one

/- warning: pnat.rec_on_succ -> PNat.recOn_succ is a dubious translation:
lean 3 declaration is
  forall (n : PNat) {p : PNat -> Sort.{u1}} (p1 : p (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) (hp : forall (n : PNat), (p n) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))))), Eq.{u1} (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))) (PNat.recOn.{u1} (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat PNat.hasAdd) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) p p1 hp) (hp n (PNat.recOn.{u1} n p p1 hp))
but is expected to have type
  forall (n : PNat) {p : PNat -> Sort.{u1}} (p1 : p (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (hp : forall (n : PNat), (p n) -> (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))), Eq.{u1} (p (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (PNat.recOn.{u1} (HAdd.hAdd.{0, 0, 0} PNat PNat PNat (instHAdd.{0} PNat instPNatAdd) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) p p1 hp) (hp n (PNat.recOn.{u1} n p p1 hp))
Case conversion may be inaccurate. Consider using '#align pnat.rec_on_succ PNat.recOn_succₓ'. -/
@[simp]
theorem recOn_succ (n : ℕ+) {p : ℕ+ → Sort _} (p1 hp) :
    @PNat.recOn (n + 1) p p1 hp = hp n (@PNat.recOn n p p1 hp) :=
  by
  cases' n with n h
  cases n <;> [exact absurd h (by decide), rfl]
#align pnat.rec_on_succ PNat.recOn_succ

#print PNat.modDivAux_spec /-
theorem modDivAux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (h : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | k, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, h =>
    by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | k, r + 1, q, h => rfl
#align pnat.mod_div_aux_spec PNat.modDivAux_spec
-/

#print PNat.mod_add_div /-
theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m :=
  by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) :=
    by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀
#align pnat.mod_add_div PNat.mod_add_div
-/

#print PNat.div_add_mod /-
theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_comm _ _).trans (mod_add_div _ _)
#align pnat.div_add_mod PNat.div_add_mod
-/

#print PNat.mod_add_div' /-
theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m :=
  by
  rw [mul_comm]
  exact mod_add_div _ _
#align pnat.mod_add_div' PNat.mod_add_div'
-/

#print PNat.div_add_mod' /-
theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m :=
  by
  rw [mul_comm]
  exact div_add_mod _ _
#align pnat.div_add_mod' PNat.div_add_mod'
-/

/- warning: pnat.mod_le -> PNat.mod_le is a dubious translation:
lean 3 declaration is
  forall (m : PNat) (k : PNat), And (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.mod m k) m) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) (PNat.mod m k) k)
but is expected to have type
  forall (m : PNat) (k : PNat), And (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.mod m k) m) (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) (PNat.mod m k) k)
Case conversion may be inaccurate. Consider using '#align pnat.mod_le PNat.mod_leₓ'. -/
theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k :=
  by
  change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
  rw [mod_coe]; split_ifs
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm⊢
    by_cases h' : (m : ℕ) / (k : ℕ) = 0
    · rw [h', mul_zero] at hm
      exact (lt_irrefl _ hm).elim
    · let h' := Nat.mul_le_mul_left (k : ℕ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h'))
      rw [mul_one] at h'
      exact ⟨h', le_refl (k : ℕ)⟩
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩
#align pnat.mod_le PNat.mod_le

/- warning: pnat.dvd_iff -> PNat.dvd_iff is a dubious translation:
lean 3 declaration is
  forall {k : PNat} {m : PNat}, Iff (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) k m) (Dvd.Dvd.{0} Nat Nat.hasDvd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) k) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) m))
but is expected to have type
  forall {k : PNat} {m : PNat}, Iff (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) k m) (Dvd.dvd.{0} Nat Nat.instDvdNat (PNat.val k) (PNat.val m))
Case conversion may be inaccurate. Consider using '#align pnat.dvd_iff PNat.dvd_iffₓ'. -/
theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) :=
  by
  constructor <;> intro h; rcases h with ⟨_, rfl⟩; apply dvd_mul_right
  rcases h with ⟨a, h⟩; cases a;
  · contrapose h
    apply NeZero
  use a.succ; apply Nat.succ_pos; rw [← coe_inj, h, mul_coe, mk_coe]
#align pnat.dvd_iff PNat.dvd_iff

/- warning: pnat.dvd_iff' -> PNat.dvd_iff' is a dubious translation:
lean 3 declaration is
  forall {k : PNat} {m : PNat}, Iff (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) k m) (Eq.{1} PNat (PNat.mod m k) k)
but is expected to have type
  forall {k : PNat} {m : PNat}, Iff (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) k m) (Eq.{1} PNat (PNat.mod m k) k)
Case conversion may be inaccurate. Consider using '#align pnat.dvd_iff' PNat.dvd_iff'ₓ'. -/
theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k :=
  by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply Eq
    rw [mod_coe, if_pos h]
  · intro h
    by_cases h' : (m : ℕ) % (k : ℕ) = 0
    · exact h'
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, if_neg h'] at h
      exact ((Nat.mod_lt (m : ℕ) k.pos).Ne h).elim
#align pnat.dvd_iff' PNat.dvd_iff'

/- warning: pnat.le_of_dvd -> PNat.le_of_dvd is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {n : PNat}, (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) m n) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid)))) m n)
but is expected to have type
  forall {m : PNat} {n : PNat}, (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) m n) -> (LE.le.{0} PNat (Preorder.toLE.{0} PNat (PartialOrder.toPreorder.{0} PNat (OrderedCancelCommMonoid.toPartialOrder.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid)))) m n)
Case conversion may be inaccurate. Consider using '#align pnat.le_of_dvd PNat.le_of_dvdₓ'. -/
theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n :=
  by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left
#align pnat.le_of_dvd PNat.le_of_dvd

/- warning: pnat.mul_div_exact -> PNat.mul_div_exact is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {k : PNat}, (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) k m) -> (Eq.{1} PNat (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat PNat.hasMul) k (PNat.divExact m k)) m)
but is expected to have type
  forall {m : PNat} {k : PNat}, (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) k m) -> (Eq.{1} PNat (HMul.hMul.{0, 0, 0} PNat PNat PNat (instHMul.{0} PNat instPNatMul) k (PNat.divExact m k)) m)
Case conversion may be inaccurate. Consider using '#align pnat.mul_div_exact PNat.mul_div_exactₓ'. -/
theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m :=
  by
  apply Eq; rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]
#align pnat.mul_div_exact PNat.mul_div_exact

/- warning: pnat.dvd_antisymm -> PNat.dvd_antisymm is a dubious translation:
lean 3 declaration is
  forall {m : PNat} {n : PNat}, (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) m n) -> (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) n m) -> (Eq.{1} PNat m n)
but is expected to have type
  forall {m : PNat} {n : PNat}, (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) m n) -> (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) n m) -> (Eq.{1} PNat m n)
Case conversion may be inaccurate. Consider using '#align pnat.dvd_antisymm PNat.dvd_antisymmₓ'. -/
theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)
#align pnat.dvd_antisymm PNat.dvd_antisymm

/- warning: pnat.dvd_one_iff -> PNat.dvd_one_iff is a dubious translation:
lean 3 declaration is
  forall (n : PNat), Iff (Dvd.Dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat PNat.linearOrderedCancelCommMonoid))))))) n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne)))) (Eq.{1} PNat n (OfNat.ofNat.{0} PNat 1 (OfNat.mk.{0} PNat 1 (One.one.{0} PNat PNat.hasOne))))
but is expected to have type
  forall (n : PNat), Iff (Dvd.dvd.{0} PNat (semigroupDvd.{0} PNat (Monoid.toSemigroup.{0} PNat (RightCancelMonoid.toMonoid.{0} PNat (CancelMonoid.toRightCancelMonoid.{0} PNat (CancelCommMonoid.toCancelMonoid.{0} PNat (OrderedCancelCommMonoid.toCancelCommMonoid.{0} PNat (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{0} PNat instPNatLinearOrderedCancelCommMonoid))))))) n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Eq.{1} PNat n (OfNat.ofNat.{0} PNat 1 (instOfNatPNatHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align pnat.dvd_one_iff PNat.dvd_one_iffₓ'. -/
theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩
#align pnat.dvd_one_iff PNat.dvd_one_iff

#print PNat.pos_of_div_pos /-
theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a :=
  by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)
#align pnat.pos_of_div_pos PNat.pos_of_div_pos
-/

end PNat

