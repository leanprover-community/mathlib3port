/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module data.real.enat_ennreal
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Enat.Basic
import Mathbin.Data.Real.Ennreal

/-!
# Coercion from `ℕ∞` to `ℝ≥0∞`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a coercion from `ℕ∞` to `ℝ≥0∞` and prove some basic lemmas about this map.
-/


open Classical NNReal ENNReal

noncomputable section

namespace ENat

variable {m n : ℕ∞}

/- warning: enat.has_coe_ennreal -> ENat.hasCoeENNReal is a dubious translation:
lean 3 declaration is
  CoeTCₓ.{1, 1} ENat ENNReal
but is expected to have type
  CoeTC.{1, 1} ENat ENNReal
Case conversion may be inaccurate. Consider using '#align enat.has_coe_ennreal ENat.hasCoeENNRealₓ'. -/
instance hasCoeENNReal : CoeTC ℕ∞ ℝ≥0∞ :=
  ⟨WithTop.map coe⟩
#align enat.has_coe_ennreal ENat.hasCoeENNReal

#print ENat.map_coe_nnreal /-
@[simp]
theorem map_coe_nnreal : WithTop.map (coe : ℕ → ℝ≥0) = (coe : ℕ∞ → ℝ≥0∞) :=
  rfl
#align enat.map_coe_nnreal ENat.map_coe_nnreal
-/

/- warning: enat.to_ennreal_order_embedding -> ENat.toENNRealOrderEmbedding is a dubious translation:
lean 3 declaration is
  OrderEmbedding.{0, 0} ENat ENNReal (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))
but is expected to have type
  OrderEmbedding.{0, 0} ENat ENNReal (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))
Case conversion may be inaccurate. Consider using '#align enat.to_ennreal_order_embedding ENat.toENNRealOrderEmbeddingₓ'. -/
/-- Coercion `ℕ∞ → ℝ≥0∞` as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def toENNRealOrderEmbedding : ℕ∞ ↪o ℝ≥0∞ :=
  Nat.castOrderEmbedding.withTop_map
#align enat.to_ennreal_order_embedding ENat.toENNRealOrderEmbedding

/- warning: enat.to_ennreal_ring_hom -> ENat.toENNRealRingHom is a dubious translation:
lean 3 declaration is
  RingHom.{0, 0} ENat ENNReal (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))) (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))
but is expected to have type
  RingHom.{0, 0} ENat ENNReal (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring)))) (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align enat.to_ennreal_ring_hom ENat.toENNRealRingHomₓ'. -/
/-- Coercion `ℕ∞ → ℝ≥0∞` as a ring homomorphism. -/
@[simps (config := { fullyApplied := false })]
def toENNRealRingHom : ℕ∞ →+* ℝ≥0∞ :=
  (Nat.castRingHom ℝ≥0).withTop_map Nat.cast_injective
#align enat.to_ennreal_ring_hom ENat.toENNRealRingHom

/- warning: enat.coe_ennreal_top -> ENat.toENNReal_top is a dubious translation:
lean 3 declaration is
  Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (Top.top.{0} ENat ENat.hasTop)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  Eq.{1} ENNReal (ENat.toENNReal (Top.top.{0} ENat instENatTop)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_top ENat.toENNReal_topₓ'. -/
@[simp, norm_cast]
theorem toENNReal_top : ((⊤ : ℕ∞) : ℝ≥0∞) = ⊤ :=
  rfl
#align enat.coe_ennreal_top ENat.toENNReal_top

#print ENat.toENNReal_coe /-
@[simp, norm_cast]
theorem toENNReal_coe (n : ℕ) : ((n : ℕ∞) : ℝ≥0∞) = n :=
  rfl
#align enat.coe_ennreal_coe ENat.toENNReal_coe
-/

/- warning: enat.coe_ennreal_le -> ENat.toENNReal_le is a dubious translation:
lean 3 declaration is
  forall {m : ENat} {n : ENat}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n)) (LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) m n)
but is expected to have type
  forall {m : ENat} {n : ENat}, Iff (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENat.toENNReal m) (ENat.toENNReal n)) (LE.le.{0} ENat (Preorder.toLE.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) m n)
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_le ENat.toENNReal_leₓ'. -/
@[simp, norm_cast]
theorem toENNReal_le : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  toENNRealOrderEmbedding.le_iff_le
#align enat.coe_ennreal_le ENat.toENNReal_le

/- warning: enat.coe_ennreal_lt -> ENat.toENNReal_lt is a dubious translation:
lean 3 declaration is
  forall {m : ENat} {n : ENat}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n)) (LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))) m n)
but is expected to have type
  forall {m : ENat} {n : ENat}, Iff (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (ENat.toENNReal m) (ENat.toENNReal n)) (LT.lt.{0} ENat (Preorder.toLT.{0} ENat (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring))))) m n)
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_lt ENat.toENNReal_ltₓ'. -/
@[simp, norm_cast]
theorem toENNReal_lt : (m : ℝ≥0∞) < n ↔ m < n :=
  toENNRealOrderEmbedding.lt_iff_lt
#align enat.coe_ennreal_lt ENat.toENNReal_lt

/- warning: enat.coe_ennreal_mono -> ENat.toENNReal_mono is a dubious translation:
lean 3 declaration is
  Monotone.{0, 0} ENat ENNReal (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring))))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)))
but is expected to have type
  Monotone.{0, 0} ENat ENNReal (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring)))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ENat.toENNReal
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_mono ENat.toENNReal_monoₓ'. -/
@[mono]
theorem toENNReal_mono : Monotone (coe : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.Monotone
#align enat.coe_ennreal_mono ENat.toENNReal_mono

/- warning: enat.coe_ennreal_strict_mono -> ENat.toENNReal_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{0, 0} ENat ENNReal (PartialOrder.toPreorder.{0} ENat (OrderedAddCommMonoid.toPartialOrder.{0} ENat (OrderedSemiring.toOrderedAddCommMonoid.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring))))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)))
but is expected to have type
  StrictMono.{0, 0} ENat ENNReal (PartialOrder.toPreorder.{0} ENat (OrderedSemiring.toPartialOrder.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring)))) (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) ENat.toENNReal
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_strict_mono ENat.toENNReal_strictMonoₓ'. -/
@[mono]
theorem toENNReal_strictMono : StrictMono (coe : ℕ∞ → ℝ≥0∞) :=
  toENNRealOrderEmbedding.StrictMono
#align enat.coe_ennreal_strict_mono ENat.toENNReal_strictMono

/- warning: enat.coe_ennreal_zero -> ENat.toENNReal_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (OfNat.ofNat.{0} ENat 0 (OfNat.mk.{0} ENat 0 (Zero.zero.{0} ENat ENat.hasZero)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  Eq.{1} ENNReal (ENat.toENNReal (OfNat.ofNat.{0} ENat 0 (Zero.toOfNat0.{0} ENat instENatZero))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_zero ENat.toENNReal_zeroₓ'. -/
@[simp, norm_cast]
theorem toENNReal_zero : ((0 : ℕ∞) : ℝ≥0∞) = 0 :=
  map_zero toENNRealRingHom
#align enat.coe_ennreal_zero ENat.toENNReal_zero

/- warning: enat.coe_ennreal_add -> ENat.toENNReal_add is a dubious translation:
lean 3 declaration is
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (HAdd.hAdd.{0, 0, 0} ENat ENat ENat (instHAdd.{0} ENat (Distrib.toHasAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))))) m n)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal (ENat.toENNReal (HAdd.hAdd.{0, 0, 0} ENat ENat ENat (instHAdd.{0} ENat (Distrib.toAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat instENatCanonicallyOrderedCommSemiring)))))))) m n)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (ENat.toENNReal m) (ENat.toENNReal n))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_add ENat.toENNReal_addₓ'. -/
@[simp]
theorem toENNReal_add (m n : ℕ∞) : ↑(m + n) = (m + n : ℝ≥0∞) :=
  map_add toENNRealRingHom m n
#align enat.coe_ennreal_add ENat.toENNReal_add

#print ENat.toENNReal_one /-
@[simp]
theorem toENNReal_one : ((1 : ℕ∞) : ℝ≥0∞) = 1 :=
  map_one toENNRealRingHom
#align enat.coe_ennreal_one ENat.toENNReal_one
-/

/- warning: enat.coe_ennreal_bit0 clashes with [anonymous] -> [anonymous]
warning: enat.coe_ennreal_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (bit0.{0} ENat (Distrib.toHasAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring))))))) n)) (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall {n : Type.{u}} {β : Type.{v}}, (Nat -> n -> β) -> Nat -> (List.{u} n) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_bit0 [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (n : ℕ∞) : ↑(bit0 n) = bit0 (n : ℝ≥0∞) :=
  toENNReal_add n n
#align enat.coe_ennreal_bit0 [anonymous]

/- warning: enat.coe_ennreal_bit1 clashes with [anonymous] -> [anonymous]
warning: enat.coe_ennreal_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (bit1.{0} ENat (AddMonoidWithOne.toOne.{0} ENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENat ENat.addCommMonoidWithOne)) (Distrib.toHasAdd.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring))))))) n)) (bit1.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)) (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall {n : Type.{u}} {β : Type.{v}}, (Nat -> n -> β) -> Nat -> (List.{u} n) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_bit1 [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (n : ℕ∞) : ↑(bit1 n) = bit1 (n : ℝ≥0∞) :=
  map_bit1 toENNRealRingHom n
#align enat.coe_ennreal_bit1 [anonymous]

/- warning: enat.coe_ennreal_mul -> ENat.toENNReal_mul is a dubious translation:
lean 3 declaration is
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (HMul.hMul.{0, 0, 0} ENat ENat ENat (instHMul.{0} ENat (Distrib.toHasMul.{0} ENat (NonUnitalNonAssocSemiring.toDistrib.{0} ENat (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENat (Semiring.toNonAssocSemiring.{0} ENat (OrderedSemiring.toSemiring.{0} ENat (OrderedCommSemiring.toOrderedSemiring.{0} ENat (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENat ENat.canonicallyOrderedCommSemiring)))))))) m n)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal (ENat.toENNReal (HMul.hMul.{0, 0, 0} ENat ENat ENat (instHMul.{0} ENat (CanonicallyOrderedCommSemiring.toMul.{0} ENat instENatCanonicallyOrderedCommSemiring)) m n)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (ENat.toENNReal m) (ENat.toENNReal n))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_mul ENat.toENNReal_mulₓ'. -/
@[simp]
theorem toENNReal_mul (m n : ℕ∞) : ↑(m * n) = (m * n : ℝ≥0∞) :=
  map_mul toENNRealRingHom m n
#align enat.coe_ennreal_mul ENat.toENNReal_mul

/- warning: enat.coe_ennreal_min -> ENat.toENNReal_min is a dubious translation:
lean 3 declaration is
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (LinearOrder.min.{0} ENat ENat.linearOrder m n)) (LinearOrder.min.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal (ENat.toENNReal (Min.min.{0} ENat (CanonicallyLinearOrderedAddMonoid.toMin.{0} ENat instENatCanonicallyLinearOrderedAddMonoid) m n)) (Min.min.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMin.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (ENat.toENNReal m) (ENat.toENNReal n))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_min ENat.toENNReal_minₓ'. -/
@[simp]
theorem toENNReal_min (m n : ℕ∞) : ↑(min m n) = (min m n : ℝ≥0∞) :=
  toENNReal_mono.map_min
#align enat.coe_ennreal_min ENat.toENNReal_min

/- warning: enat.coe_ennreal_max -> ENat.toENNReal_max is a dubious translation:
lean 3 declaration is
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (LinearOrder.max.{0} ENat ENat.linearOrder m n)) (LinearOrder.max.{0} ENNReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} ENNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} ENNReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} ENNReal ENNReal.completeLinearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal (ENat.toENNReal (Max.max.{0} ENat (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENat instENatCanonicallyLinearOrderedAddMonoid) m n)) (Max.max.{0} ENNReal (CanonicallyLinearOrderedAddMonoid.toMax.{0} ENNReal ENNReal.instCanonicallyLinearOrderedAddMonoidENNReal) (ENat.toENNReal m) (ENat.toENNReal n))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_max ENat.toENNReal_maxₓ'. -/
@[simp]
theorem toENNReal_max (m n : ℕ∞) : ↑(max m n) = (max m n : ℝ≥0∞) :=
  toENNReal_mono.map_max
#align enat.coe_ennreal_max ENat.toENNReal_max

/- warning: enat.coe_ennreal_sub -> ENat.toENNReal_sub is a dubious translation:
lean 3 declaration is
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) (HSub.hSub.{0, 0, 0} ENat ENat ENat (instHSub.{0} ENat ENat.hasSub) m n)) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENat ENNReal (HasLiftT.mk.{1, 1} ENat ENNReal (CoeTCₓ.coe.{1, 1} ENat ENNReal ENat.hasCoeENNReal)) n))
but is expected to have type
  forall (m : ENat) (n : ENat), Eq.{1} ENNReal (ENat.toENNReal (HSub.hSub.{0, 0, 0} ENat ENat ENat (instHSub.{0} ENat instENatSub) m n)) (HSub.hSub.{0, 0, 0} ENNReal ENNReal ENNReal (instHSub.{0} ENNReal ENNReal.instSub) (ENat.toENNReal m) (ENat.toENNReal n))
Case conversion may be inaccurate. Consider using '#align enat.coe_ennreal_sub ENat.toENNReal_subₓ'. -/
@[simp]
theorem toENNReal_sub (m n : ℕ∞) : ↑(m - n) = (m - n : ℝ≥0∞) :=
  WithTop.map_sub Nat.cast_tsub Nat.cast_zero m n
#align enat.coe_ennreal_sub ENat.toENNReal_sub

end ENat

