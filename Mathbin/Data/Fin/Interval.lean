/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.fin.interval
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Finset.LocallyFinite

/-!
# Finite intervals in `fin n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that `fin n` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset Fin Function

open BigOperators

variable (n : ℕ)

instance : LocallyFiniteOrder (Fin n) :=
  OrderIso.locallyFiniteOrder Fin.orderIsoSubtype

instance : LocallyFiniteOrderBot (Fin n) :=
  OrderIso.locallyFiniteOrderBot Fin.orderIsoSubtype

instance : ∀ n, LocallyFiniteOrderTop (Fin n)
  | 0 => IsEmpty.toLocallyFiniteOrderTop
  | n + 1 => inferInstance

namespace Fin

variable {n} (a b : Fin n)

/- warning: fin.Icc_eq_finset_subtype -> Fin.Icc_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b) (Finset.fin n (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b) (Finset.fin n (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b)))
Case conversion may be inaccurate. Consider using '#align fin.Icc_eq_finset_subtype Fin.Icc_eq_finset_subtypeₓ'. -/
theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).Fin n :=
  rfl
#align fin.Icc_eq_finset_subtype Fin.Icc_eq_finset_subtype

/- warning: fin.Ico_eq_finset_subtype -> Fin.Ico_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b) (Finset.fin n (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b) (Finset.fin n (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b)))
Case conversion may be inaccurate. Consider using '#align fin.Ico_eq_finset_subtype Fin.Ico_eq_finset_subtypeₓ'. -/
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).Fin n :=
  rfl
#align fin.Ico_eq_finset_subtype Fin.Ico_eq_finset_subtype

/- warning: fin.Ioc_eq_finset_subtype -> Fin.Ioc_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b) (Finset.fin n (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b) (Finset.fin n (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b)))
Case conversion may be inaccurate. Consider using '#align fin.Ioc_eq_finset_subtype Fin.Ioc_eq_finset_subtypeₓ'. -/
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).Fin n :=
  rfl
#align fin.Ioc_eq_finset_subtype Fin.Ioc_eq_finset_subtype

/- warning: fin.Ioo_eq_finset_subtype -> Fin.Ioo_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b) (Finset.fin n (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b) (Finset.fin n (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b)))
Case conversion may be inaccurate. Consider using '#align fin.Ioo_eq_finset_subtype Fin.Ioo_eq_finset_subtypeₓ'. -/
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).Fin n :=
  rfl
#align fin.Ioo_eq_finset_subtype Fin.Ioo_eq_finset_subtype

/- warning: fin.map_subtype_embedding_Icc -> Fin.map_subtype_embedding_Icc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Icc Fin.map_subtype_embedding_Iccₓ'. -/
@[simp]
theorem map_subtype_embedding_Icc : (Icc a b).map Fin.valEmbedding = Icc a b := by
  simp [Icc_eq_finset_subtype, Finset.fin, Finset.map_map, Icc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Icc Fin.map_subtype_embedding_Icc

/- warning: fin.map_subtype_embedding_Ico -> Fin.map_subtype_embedding_Ico is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Ico Fin.map_subtype_embedding_Icoₓ'. -/
@[simp]
theorem map_subtype_embedding_Ico : (Ico a b).map Fin.valEmbedding = Ico a b := by
  simp [Ico_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ico Fin.map_subtype_embedding_Ico

/- warning: fin.map_subtype_embedding_Ioc -> Fin.map_subtype_embedding_Ioc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Ioc Fin.map_subtype_embedding_Iocₓ'. -/
@[simp]
theorem map_subtype_embedding_Ioc : (Ioc a b).map Fin.valEmbedding = Ioc a b := by
  simp [Ioc_eq_finset_subtype, Finset.fin, Finset.map_map, Ioc_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Ioc Fin.map_subtype_embedding_Ioc

/- warning: fin.map_subtype_embedding_Ioo -> Fin.map_subtype_embedding_Ioo is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (Fin.val n b))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Ioo Fin.map_subtype_embedding_Iooₓ'. -/
@[simp]
theorem map_subtype_embedding_Ioo : (Ioo a b).map Fin.valEmbedding = Ioo a b := by
  simp [Ioo_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Ioo Fin.map_subtype_embedding_Ioo

/- warning: fin.card_Icc -> Fin.card_Icc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.val n a))
Case conversion may be inaccurate. Consider using '#align fin.card_Icc Fin.card_Iccₓ'. -/
@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]
#align fin.card_Icc Fin.card_Icc

/- warning: fin.card_Ico -> Fin.card_Ico is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val n b) (Fin.val n a))
Case conversion may be inaccurate. Consider using '#align fin.card_Ico Fin.card_Icoₓ'. -/
@[simp]
theorem card_Ico : (Ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]
#align fin.card_Ico Fin.card_Ico

/- warning: fin.card_Ioc -> Fin.card_Ioc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val n b) (Fin.val n a))
Case conversion may be inaccurate. Consider using '#align fin.card_Ioc Fin.card_Iocₓ'. -/
@[simp]
theorem card_Ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]
#align fin.card_Ioc Fin.card_Ioc

/- warning: fin.card_Ioo -> Fin.card_Ioo is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val n b) (Fin.val n a)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align fin.card_Ioo Fin.card_Iooₓ'. -/
@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]
#align fin.card_Ioo Fin.card_Ioo

/- warning: fin.card_fintype_Icc -> Fin.card_fintypeIcc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) a b)) (Set.fintypeIcc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Icc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) a b)) (Set.fintypeIcc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.val n a))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Icc Fin.card_fintypeIccₓ'. -/
@[simp]
theorem card_fintypeIcc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align fin.card_fintype_Icc Fin.card_fintypeIcc

/- warning: fin.card_fintype_Ico -> Fin.card_fintypeIco is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) a b)) (Set.fintypeIco.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Ico.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) a b)) (Set.fintypeIco.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val n b) (Fin.val n a))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Ico Fin.card_fintypeIcoₓ'. -/
@[simp]
theorem card_fintypeIco : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align fin.card_fintype_Ico Fin.card_fintypeIco

/- warning: fin.card_fintype_Ioc -> Fin.card_fintypeIoc is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) a b)) (Set.fintypeIoc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Ioc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) a b)) (Set.fintypeIoc.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val n b) (Fin.val n a))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Ioc Fin.card_fintypeIocₓ'. -/
@[simp]
theorem card_fintypeIoc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align fin.card_fintype_Ioc Fin.card_fintypeIoc

/- warning: fin.card_fintype_Ioo -> Fin.card_fintypeIoo is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) a b)) (Set.fintypeIoo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrder n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {n : Nat} (a : Fin n) (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Ioo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) a b)) (Set.fintypeIoo.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderFinToPreorderInstPartialOrderFin n) a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val n b) (Fin.val n a)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Ioo Fin.card_fintypeIooₓ'. -/
@[simp]
theorem card_fintypeIoo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align fin.card_fintype_Ioo Fin.card_fintypeIoo

/- warning: fin.Ici_eq_finset_subtype -> Fin.Ici_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a) (Finset.fin n (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) n))
but is expected to have type
  forall {n : Nat} (a : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a) (Finset.fin n (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) n))
Case conversion may be inaccurate. Consider using '#align fin.Ici_eq_finset_subtype Fin.Ici_eq_finset_subtypeₓ'. -/
theorem Ici_eq_finset_subtype : Ici a = (Icc (a : ℕ) n).Fin n :=
  by
  ext
  simp
#align fin.Ici_eq_finset_subtype Fin.Ici_eq_finset_subtype

/- warning: fin.Ioi_eq_finset_subtype -> Fin.Ioi_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a) (Finset.fin n (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) n))
but is expected to have type
  forall {n : Nat} (a : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a) (Finset.fin n (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) n))
Case conversion may be inaccurate. Consider using '#align fin.Ioi_eq_finset_subtype Fin.Ioi_eq_finset_subtypeₓ'. -/
theorem Ioi_eq_finset_subtype : Ioi a = (Ioc (a : ℕ) n).Fin n :=
  by
  ext
  simp
#align fin.Ioi_eq_finset_subtype Fin.Ioi_eq_finset_subtype

/- warning: fin.Iic_eq_finset_subtype -> Fin.Iic_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b) (Finset.fin n (Finset.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.orderBot Nat.locallyFiniteOrder) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)))
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b) (Finset.fin n (Finset.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Nat.orderBot instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring) (Fin.val n b)))
Case conversion may be inaccurate. Consider using '#align fin.Iic_eq_finset_subtype Fin.Iic_eq_finset_subtypeₓ'. -/
theorem Iic_eq_finset_subtype : Iic b = (Iic (b : ℕ)).Fin n :=
  rfl
#align fin.Iic_eq_finset_subtype Fin.Iic_eq_finset_subtype

/- warning: fin.Iio_eq_finset_subtype -> Fin.Iio_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b) (Finset.fin n (Finset.Iio.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.orderBot Nat.locallyFiniteOrder) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)))
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} (Fin n)) (Finset.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b) (Finset.fin n (Finset.Iio.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Nat.orderBot instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring) (Fin.val n b)))
Case conversion may be inaccurate. Consider using '#align fin.Iio_eq_finset_subtype Fin.Iio_eq_finset_subtypeₓ'. -/
theorem Iio_eq_finset_subtype : Iio b = (Iio (b : ℕ)).Fin n :=
  rfl
#align fin.Iio_eq_finset_subtype Fin.Iio_eq_finset_subtype

/- warning: fin.map_subtype_embedding_Ici -> Fin.map_subtype_embedding_Ici is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a)) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {n : Nat} (a : Fin n), (Fin n) -> (Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a)) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Ici Fin.map_subtype_embedding_Iciₓ'. -/
@[simp]
theorem map_subtype_embedding_Ici : (Ici a).map Fin.valEmbedding = Icc a (n - 1) :=
  by
  ext x
  simp only [exists_prop, embedding.coe_subtype, mem_Ici, mem_map, mem_Icc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ici Fin.map_subtype_embedding_Ici

/- warning: fin.map_subtype_embedding_Ioi -> Fin.map_subtype_embedding_Ioi is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a)) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {n : Nat} (a : Fin n), (Fin n) -> (Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a)) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (Fin.val n a) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Ioi Fin.map_subtype_embedding_Ioiₓ'. -/
@[simp]
theorem map_subtype_embedding_Ioi : (Ioi a).map Fin.valEmbedding = Ioc a (n - 1) :=
  by
  ext x
  simp only [exists_prop, embedding.coe_subtype, mem_Ioi, mem_map, mem_Ioc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, le_tsub_of_add_le_right <| x.2⟩
  cases n
  · exact Fin.elim0 a
  · exact fun hx => ⟨⟨x, Nat.lt_succ_iff.2 hx.2⟩, hx.1, rfl⟩
#align fin.map_subtype_embedding_Ioi Fin.map_subtype_embedding_Ioi

/- warning: fin.map_subtype_embedding_Iic -> Fin.map_subtype_embedding_Iic is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b)) (Finset.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.orderBot Nat.locallyFiniteOrder) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b))
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b)) (Finset.Iic.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Nat.orderBot instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring) (Fin.val n b))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Iic Fin.map_subtype_embedding_Iicₓ'. -/
@[simp]
theorem map_subtype_embedding_Iic : (Iic b).map Fin.valEmbedding = Iic b := by
  simp [Iic_eq_finset_subtype, Finset.fin, Finset.map_map, Iic_filter_lt_of_lt_right]
#align fin.map_subtype_embedding_Iic Fin.map_subtype_embedding_Iic

/- warning: fin.map_subtype_embedding_Iio -> Fin.map_subtype_embedding_Iio is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b)) (Finset.Iio.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.orderBot Nat.locallyFiniteOrder) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b))
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b)) (Finset.Iio.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (Finset.LocallyFiniteOrder.toLocallyFiniteOrderBot.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) Nat.orderBot instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring) (Fin.val n b))
Case conversion may be inaccurate. Consider using '#align fin.map_subtype_embedding_Iio Fin.map_subtype_embedding_Iioₓ'. -/
@[simp]
theorem map_subtype_embedding_Iio : (Iio b).map Fin.valEmbedding = Iio b := by
  simp [Iio_eq_finset_subtype, Finset.fin, Finset.map_map]
#align fin.map_subtype_embedding_Iio Fin.map_subtype_embedding_Iio

/- warning: fin.card_Ici -> Fin.card_Ici is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n), (Fin n) -> (Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (Fin.val n a)))
Case conversion may be inaccurate. Consider using '#align fin.card_Ici Fin.card_Iciₓ'. -/
@[simp]
theorem card_Ici : (Ici a).card = n - a := by
  cases n
  · exact Fin.elim0 a
  rw [← card_map, map_subtype_embedding_Ici, Nat.card_Icc]
  rfl
#align fin.card_Ici Fin.card_Ici

/- warning: fin.card_Ioi -> Fin.card_Ioi is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n), (Fin n) -> (Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.val n a)))
Case conversion may be inaccurate. Consider using '#align fin.card_Ioi Fin.card_Ioiₓ'. -/
@[simp]
theorem card_Ioi : (Ioi a).card = n - 1 - a := by
  rw [← card_map, map_subtype_embedding_Ioi, Nat.card_Ioc]
#align fin.card_Ioi Fin.card_Ioi

/- warning: fin.card_Iic -> Fin.card_Iic is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align fin.card_Iic Fin.card_Iicₓ'. -/
@[simp]
theorem card_Iic : (Iic b).card = b + 1 := by
  rw [← Nat.card_Iic b, ← map_subtype_embedding_Iic, card_map]
#align fin.card_Iic Fin.card_Iic

/- warning: fin.card_Iio -> Fin.card_Iio is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Finset.card.{0} (Fin n) (Finset.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b)) (Fin.val n b)
Case conversion may be inaccurate. Consider using '#align fin.card_Iio Fin.card_Iioₓ'. -/
@[simp]
theorem card_Iio : (Iio b).card = b := by
  rw [← Nat.card_Iio b, ← map_subtype_embedding_Iio, card_map]
#align fin.card_Iio Fin.card_Iio

/- warning: fin.card_fintype_Ici -> Fin.card_fintypeIci is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) a)) (Set.fintypeIci.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n), (Fin n) -> (Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Ici.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) a)) (Set.fintypeIci.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (Fin.val n a)))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Ici Fin.card_fintypeIciₓ'. -/
@[simp]
theorem card_fintypeIci : Fintype.card (Set.Ici a) = n - a := by
  rw [Fintype.card_ofFinset, card_Ici]
#align fin.card_fintype_Ici Fin.card_fintypeIci

/- warning: fin.card_fintype_Ioi -> Fin.card_fintypeIoi is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (a : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) a)) (Set.fintypeIoi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderTop n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) a))
but is expected to have type
  forall {n : Nat} (a : Fin n), (Fin n) -> (Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Ioi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) a)) (Set.fintypeIoi.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instForAllNatLocallyFiniteOrderTopFinToPreorderInstPartialOrderFin n) a)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Fin.val n a)))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Ioi Fin.card_fintypeIoiₓ'. -/
@[simp]
theorem card_fintypeIoi : Fintype.card (Set.Ioi a) = n - 1 - a := by
  rw [Fintype.card_ofFinset, card_Ioi]
#align fin.card_fintype_Ioi Fin.card_fintypeIoi

/- warning: fin.card_fintype_Iic -> Fin.card_fintypeIic is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) b)) (Set.fintypeIic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Iic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) b)) (Set.fintypeIic.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Iic Fin.card_fintypeIicₓ'. -/
@[simp]
theorem card_fintypeIic : Fintype.card (Set.Iic b) = b + 1 := by
  rw [Fintype.card_ofFinset, card_Iic]
#align fin.card_fintype_Iic Fin.card_fintypeIic

/- warning: fin.card_fintype_Iio -> Fin.card_fintypeIio is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} (Fin n)) Type (Set.hasCoeToSort.{0} (Fin n)) (Set.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) b)) (Set.fintypeIio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.partialOrder n)) (Fin.locallyFiniteOrderBot n) b)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) b)
but is expected to have type
  forall {n : Nat} (b : Fin n), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} (Fin n) (Set.Iio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) b)) (Set.fintypeIio.{0} (Fin n) (PartialOrder.toPreorder.{0} (Fin n) (Fin.instPartialOrderFin n)) (instLocallyFiniteOrderBotFinToPreorderInstPartialOrderFin n) b)) (Fin.val n b)
Case conversion may be inaccurate. Consider using '#align fin.card_fintype_Iio Fin.card_fintypeIioₓ'. -/
@[simp]
theorem card_fintypeIio : Fintype.card (Set.Iio b) = b := by rw [Fintype.card_ofFinset, card_Iio]
#align fin.card_fintype_Iio Fin.card_fintypeIio

end Fin

