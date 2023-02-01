/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.pnat.interval
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Data.Pnat.Defs

/-!
# Finite intervals of positive naturals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that `ℕ+` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/


open Finset PNat

instance : LocallyFiniteOrder ℕ+ :=
  Subtype.locallyFiniteOrder _

namespace PNat

variable (a b : ℕ+)

/- warning: pnat.Icc_eq_finset_subtype -> PNat.Icc_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (fun (a : Nat) => Nat.decidableLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b)))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (fun (a : Nat) => Nat.decLt (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b)))
Case conversion may be inaccurate. Consider using '#align pnat.Icc_eq_finset_subtype PNat.Icc_eq_finset_subtypeₓ'. -/
theorem Icc_eq_finset_subtype : Icc a b = (Icc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Icc_eq_finset_subtype PNat.Icc_eq_finset_subtype

/- warning: pnat.Ico_eq_finset_subtype -> PNat.Ico_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (fun (a : Nat) => Nat.decidableLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b)))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (fun (a : Nat) => Nat.decLt (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b)))
Case conversion may be inaccurate. Consider using '#align pnat.Ico_eq_finset_subtype PNat.Ico_eq_finset_subtypeₓ'. -/
theorem Ico_eq_finset_subtype : Ico a b = (Ico (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ico_eq_finset_subtype PNat.Ico_eq_finset_subtype

/- warning: pnat.Ioc_eq_finset_subtype -> PNat.Ioc_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (fun (a : Nat) => Nat.decidableLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b)))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (fun (a : Nat) => Nat.decLt (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b)))
Case conversion may be inaccurate. Consider using '#align pnat.Ioc_eq_finset_subtype PNat.Ioc_eq_finset_subtypeₓ'. -/
theorem Ioc_eq_finset_subtype : Ioc a b = (Ioc (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioc_eq_finset_subtype PNat.Ioc_eq_finset_subtype

/- warning: pnat.Ioo_eq_finset_subtype -> PNat.Ioo_eq_finset_subtype is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n) (fun (a : Nat) => Nat.decidableLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b)))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} PNat) (Finset.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b) (Finset.subtype.{0} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n) (fun (a : Nat) => Nat.decLt (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b)))
Case conversion may be inaccurate. Consider using '#align pnat.Ioo_eq_finset_subtype PNat.Ioo_eq_finset_subtypeₓ'. -/
theorem Ioo_eq_finset_subtype : Ioo a b = (Ioo (a : ℕ) b).Subtype fun n : ℕ => 0 < n :=
  rfl
#align pnat.Ioo_eq_finset_subtype PNat.Ioo_eq_finset_subtype

/- warning: pnat.map_subtype_embedding_Icc -> PNat.map_subtype_embedding_Icc is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} PNat Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (Finset.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Finset.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (Finset.Icc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b))
Case conversion may be inaccurate. Consider using '#align pnat.map_subtype_embedding_Icc PNat.map_subtype_embedding_Iccₓ'. -/
theorem map_subtype_embedding_Icc : (Icc a b).map (Function.Embedding.subtype _) = Icc (a : ℕ) b :=
  map_subtype_embedding_Icc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Icc PNat.map_subtype_embedding_Icc

/- warning: pnat.map_subtype_embedding_Ico -> PNat.map_subtype_embedding_Ico is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} PNat Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (Finset.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Finset.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (Finset.Ico.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b))
Case conversion may be inaccurate. Consider using '#align pnat.map_subtype_embedding_Ico PNat.map_subtype_embedding_Icoₓ'. -/
theorem map_subtype_embedding_Ico : (Ico a b).map (Function.Embedding.subtype _) = Ico (a : ℕ) b :=
  map_subtype_embedding_Ico _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ico PNat.map_subtype_embedding_Ico

/- warning: pnat.map_subtype_embedding_Ioc -> PNat.map_subtype_embedding_Ioc is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} PNat Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (Finset.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Finset.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (Finset.Ioc.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b))
Case conversion may be inaccurate. Consider using '#align pnat.map_subtype_embedding_Ioc PNat.map_subtype_embedding_Iocₓ'. -/
theorem map_subtype_embedding_Ioc : (Ioc a b).map (Function.Embedding.subtype _) = Ioc (a : ℕ) b :=
  map_subtype_embedding_Ioc _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioc PNat.map_subtype_embedding_Ioc

/- warning: pnat.map_subtype_embedding_Ioo -> PNat.map_subtype_embedding_Ioo is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} PNat Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) n)) (Finset.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) Nat.locallyFiniteOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) Nat (Function.Embedding.subtype.{1} Nat (fun (n : Nat) => LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) n)) (Finset.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (Finset.Ioo.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) instLocallyFiniteOrderNatToPreorderToPartialOrderStrictOrderedSemiring (PNat.val a) (PNat.val b))
Case conversion may be inaccurate. Consider using '#align pnat.map_subtype_embedding_Ioo PNat.map_subtype_embedding_Iooₓ'. -/
theorem map_subtype_embedding_Ioo : (Ioo a b).map (Function.Embedding.subtype _) = Ioo (a : ℕ) b :=
  map_subtype_embedding_Ioo _ _ _ fun c _ x hx _ hc _ => hc.trans_le hx
#align pnat.map_subtype_embedding_Ioo PNat.map_subtype_embedding_Ioo

/- warning: pnat.card_Icc -> PNat.card_Icc is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (PNat.val b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.card_Icc PNat.card_Iccₓ'. -/
@[simp]
theorem card_Icc : (Icc a b).card = b + 1 - a := by
  rw [← Nat.card_Icc, ← map_subtype_embedding_Icc, card_map]
#align pnat.card_Icc PNat.card_Icc

/- warning: pnat.card_Ico -> PNat.card_Ico is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val b) (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.card_Ico PNat.card_Icoₓ'. -/
@[simp]
theorem card_Ico : (Ico a b).card = b - a := by
  rw [← Nat.card_Ico, ← map_subtype_embedding_Ico, card_map]
#align pnat.card_Ico PNat.card_Ico

/- warning: pnat.card_Ioc -> PNat.card_Ioc is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val b) (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.card_Ioc PNat.card_Iocₓ'. -/
@[simp]
theorem card_Ioc : (Ioc a b).card = b - a := by
  rw [← Nat.card_Ioc, ← map_subtype_embedding_Ioc, card_map]
#align pnat.card_Ioc PNat.card_Ioc

/- warning: pnat.card_Ioo -> PNat.card_Ioo is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Finset.card.{0} PNat (Finset.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val b) (PNat.val a)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pnat.card_Ioo PNat.card_Iooₓ'. -/
@[simp]
theorem card_Ioo : (Ioo a b).card = b - a - 1 := by
  rw [← Nat.card_Ioo, ← map_subtype_embedding_Ioo, card_map]
#align pnat.card_Ioo PNat.card_Ioo

/- warning: pnat.card_fintype_Icc -> PNat.card_fintype_Icc is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} PNat) Type (Set.hasCoeToSort.{0} PNat) (Set.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) a b)) (Set.fintypeIcc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} PNat (Set.Icc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) a b)) (Set.fintypeIcc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (PNat.val b) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.card_fintype_Icc PNat.card_fintype_Iccₓ'. -/
@[simp]
theorem card_fintype_Icc : Fintype.card (Set.Icc a b) = b + 1 - a := by
  rw [← card_Icc, Fintype.card_ofFinset]
#align pnat.card_fintype_Icc PNat.card_fintype_Icc

/- warning: pnat.card_fintype_Ico -> PNat.card_fintype_Ico is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} PNat) Type (Set.hasCoeToSort.{0} PNat) (Set.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) a b)) (Set.fintypeIco.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} PNat (Set.Ico.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) a b)) (Set.fintypeIco.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val b) (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.card_fintype_Ico PNat.card_fintype_Icoₓ'. -/
@[simp]
theorem card_fintype_Ico : Fintype.card (Set.Ico a b) = b - a := by
  rw [← card_Ico, Fintype.card_ofFinset]
#align pnat.card_fintype_Ico PNat.card_fintype_Ico

/- warning: pnat.card_fintype_Ioc -> PNat.card_fintype_Ioc is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} PNat) Type (Set.hasCoeToSort.{0} PNat) (Set.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) a b)) (Set.fintypeIoc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} PNat (Set.Ioc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) a b)) (Set.fintypeIoc.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val b) (PNat.val a))
Case conversion may be inaccurate. Consider using '#align pnat.card_fintype_Ioc PNat.card_fintype_Iocₓ'. -/
@[simp]
theorem card_fintype_Ioc : Fintype.card (Set.Ioc a b) = b - a := by
  rw [← card_Ioc, Fintype.card_ofFinset]
#align pnat.card_fintype_Ioc PNat.card_fintype_Ioc

/- warning: pnat.card_fintype_Ioo -> PNat.card_fintype_Ioo is a dubious translation:
lean 3 declaration is
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (coeSort.{1, 2} (Set.{0} PNat) Type (Set.hasCoeToSort.{0} PNat) (Set.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) a b)) (Set.fintypeIoo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (LinearOrder.toLattice.{0} PNat PNat.linearOrder)))) PNat.locallyFiniteOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) b) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) PNat Nat (HasLiftT.mk.{1, 1} PNat Nat (CoeTCₓ.coe.{1, 1} PNat Nat (coeBase.{1, 1} PNat Nat coePNatNat))) a)) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall (a : PNat) (b : PNat), Eq.{1} Nat (Fintype.card.{0} (Set.Elem.{0} PNat (Set.Ioo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) a b)) (Set.fintypeIoo.{0} PNat (PartialOrder.toPreorder.{0} PNat (SemilatticeInf.toPartialOrder.{0} PNat (Lattice.toSemilatticeInf.{0} PNat (DistribLattice.toLattice.{0} PNat (instDistribLattice.{0} PNat instPNatLinearOrder))))) instLocallyFiniteOrderPNatToPreorderToPartialOrderToSemilatticeInfToLatticeInstDistribLatticeInstPNatLinearOrder a b)) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (PNat.val b) (PNat.val a)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align pnat.card_fintype_Ioo PNat.card_fintype_Iooₓ'. -/
@[simp]
theorem card_fintype_Ioo : Fintype.card (Set.Ioo a b) = b - a - 1 := by
  rw [← card_Ioo, Fintype.card_ofFinset]
#align pnat.card_fintype_Ioo PNat.card_fintype_Ioo

end PNat

