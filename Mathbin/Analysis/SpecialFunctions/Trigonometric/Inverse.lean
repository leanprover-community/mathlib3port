/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.inverse
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathbin.Topology.Algebra.Order.ProjIcc

/-!
# Inverse trigonometric functions.

See also `analysis.special_functions.trigonometric.arctan` for the inverse tan function.
(This is delayed as it is easier to set up after developing complex trigonometric functions.)

Basic inequalities on trigonometric functions.
-/


noncomputable section

open Classical Topology Filter

open Set Filter

open Real

namespace Real

#print Real.arcsin /-
/-- Inverse of the `sin` function, returns values in the range `-π / 2 ≤ arcsin x ≤ π / 2`.
It defaults to `-π / 2` on `(-∞, -1)` and to `π / 2` to `(1, ∞)`. -/
@[pp_nodot]
noncomputable def arcsin : ℝ → ℝ :=
  coe ∘ IccExtend (neg_le_self zero_le_one) sinOrderIso.symm
#align real.arcsin Real.arcsin
-/

/- warning: real.arcsin_mem_Icc -> Real.arcsin_mem_Icc is a dubious translation:
lean 3 declaration is
  forall (x : Real), Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (Real.arcsin x) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall (x : Real), Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (Real.arcsin x) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_mem_Icc Real.arcsin_mem_Iccₓ'. -/
theorem arcsin_mem_Icc (x : ℝ) : arcsin x ∈ Icc (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _
#align real.arcsin_mem_Icc Real.arcsin_mem_Icc

/- warning: real.range_arcsin -> Real.range_arcsin is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.arcsin) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.arcsin) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.range_arcsin Real.range_arcsinₓ'. -/
@[simp]
theorem range_arcsin : range arcsin = Icc (-(π / 2)) (π / 2) :=
  by
  rw [arcsin, range_comp coe]
  simp [Icc]
#align real.range_arcsin Real.range_arcsin

/- warning: real.arcsin_le_pi_div_two -> Real.arcsin_le_pi_div_two is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_le_pi_div_two Real.arcsin_le_pi_div_twoₓ'. -/
theorem arcsin_le_pi_div_two (x : ℝ) : arcsin x ≤ π / 2 :=
  (arcsin_mem_Icc x).2
#align real.arcsin_le_pi_div_two Real.arcsin_le_pi_div_two

/- warning: real.neg_pi_div_two_le_arcsin -> Real.neg_pi_div_two_le_arcsin is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Real.arcsin x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Real.arcsin x)
Case conversion may be inaccurate. Consider using '#align real.neg_pi_div_two_le_arcsin Real.neg_pi_div_two_le_arcsinₓ'. -/
theorem neg_pi_div_two_le_arcsin (x : ℝ) : -(π / 2) ≤ arcsin x :=
  (arcsin_mem_Icc x).1
#align real.neg_pi_div_two_le_arcsin Real.neg_pi_div_two_le_arcsin

/- warning: real.arcsin_proj_Icc -> Real.arcsin_projIcc is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.arcsin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (Neg.neg.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (Neg.neg.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (Neg.neg.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (Neg.neg.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (Neg.neg.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))))) (Set.projIcc.{0} Real Real.linearOrder (Neg.neg.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (neg_le_self.{0} Real Real.addGroup (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) (OrderedAddCommGroup.to_covariantClass_left_le.{0} Real Real.orderedAddCommGroup) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (zero_le_one.{0} Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (SubNegMonoid.toAddMonoid.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)))) Real.hasOne (Preorder.toHasLe.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder))))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) x))) (Real.arcsin x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.arcsin (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder))))) (Neg.neg.{0} Real (NegZeroClass.toNeg.{0} Real (SubNegZeroMonoid.toNegZeroClass.{0} Real (SubtractionMonoid.toSubNegZeroMonoid.{0} Real (AddGroup.toSubtractionMonoid.{0} Real Real.instAddGroupReal)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Set.projIcc.{0} Real Real.linearOrder (Neg.neg.{0} Real (NegZeroClass.toNeg.{0} Real (SubNegZeroMonoid.toNegZeroClass.{0} Real (SubtractionMonoid.toSubNegZeroMonoid.{0} Real (AddGroup.toSubtractionMonoid.{0} Real Real.instAddGroupReal)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (neg_le_self.{0} Real Real.instAddGroupReal (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder))))) (OrderedAddCommGroup.to_covariantClass_left_le.{0} Real Real.orderedAddCommGroup) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (zero_le_one.{0} Real (NegZeroClass.toZero.{0} Real (SubNegZeroMonoid.toNegZeroClass.{0} Real (SubtractionMonoid.toSubNegZeroMonoid.{0} Real (AddGroup.toSubtractionMonoid.{0} Real Real.instAddGroupReal)))) Real.instOneReal (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder)))))) (OrderedSemiring.zeroLEOneClass.{0} Real Real.orderedSemiring))) x))) (Real.arcsin x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_proj_Icc Real.arcsin_projIccₓ'. -/
theorem arcsin_projIcc (x : ℝ) : arcsin (projIcc (-1) 1 (neg_le_self zero_le_one) x) = arcsin x :=
  by rw [arcsin, Function.comp_apply, Icc_extend_coe, Function.comp_apply, Icc_extend]
#align real.arcsin_proj_Icc Real.arcsin_projIcc

/- warning: real.sin_arcsin' -> Real.sin_arcsin' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Eq.{1} Real (Real.sin (Real.arcsin x)) x)
but is expected to have type
  forall {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Eq.{1} Real (Real.sin (Real.arcsin x)) x)
Case conversion may be inaccurate. Consider using '#align real.sin_arcsin' Real.sin_arcsin'ₓ'. -/
theorem sin_arcsin' {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : sin (arcsin x) = x := by
  simpa [arcsin, Icc_extend_of_mem _ _ hx, -OrderIso.apply_symm_apply] using
    Subtype.ext_iff.1 (sin_order_iso.apply_symm_apply ⟨x, hx⟩)
#align real.sin_arcsin' Real.sin_arcsin'

/- warning: real.sin_arcsin -> Real.sin_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} Real (Real.sin (Real.arcsin x)) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} Real (Real.sin (Real.arcsin x)) x)
Case conversion may be inaccurate. Consider using '#align real.sin_arcsin Real.sin_arcsinₓ'. -/
theorem sin_arcsin {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : sin (arcsin x) = x :=
  sin_arcsin' ⟨hx₁, hx₂⟩
#align real.sin_arcsin Real.sin_arcsin

/- warning: real.arcsin_sin' -> Real.arcsin_sin' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Eq.{1} Real (Real.arcsin (Real.sin x)) x)
but is expected to have type
  forall {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Eq.{1} Real (Real.arcsin (Real.sin x)) x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_sin' Real.arcsin_sin'ₓ'. -/
theorem arcsin_sin' {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : arcsin (sin x) = x :=
  injOn_sin (arcsin_mem_Icc _) hx <| by rw [sin_arcsin (neg_one_le_sin _) (sin_le_one _)]
#align real.arcsin_sin' Real.arcsin_sin'

/- warning: real.arcsin_sin -> Real.arcsin_sin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LE.le.{0} Real Real.hasLe x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (Eq.{1} Real (Real.arcsin (Real.sin x)) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LE.le.{0} Real Real.instLEReal x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (Eq.{1} Real (Real.arcsin (Real.sin x)) x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_sin Real.arcsin_sinₓ'. -/
theorem arcsin_sin {x : ℝ} (hx₁ : -(π / 2) ≤ x) (hx₂ : x ≤ π / 2) : arcsin (sin x) = x :=
  arcsin_sin' ⟨hx₁, hx₂⟩
#align real.arcsin_sin Real.arcsin_sin

/- warning: real.strict_mono_on_arcsin -> Real.strictMonoOn_arcsin is a dubious translation:
lean 3 declaration is
  StrictMonoOn.{0, 0} Real Real Real.preorder Real.preorder Real.arcsin (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  StrictMonoOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.arcsin (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.strict_mono_on_arcsin Real.strictMonoOn_arcsinₓ'. -/
theorem strictMonoOn_arcsin : StrictMonoOn arcsin (Icc (-1) 1) :=
  (Subtype.strictMono_coe _).comp_strictMonoOn <|
    sinOrderIso.symm.StrictMono.strictMonoOn_IccExtend _
#align real.strict_mono_on_arcsin Real.strictMonoOn_arcsin

#print Real.monotone_arcsin /-
theorem monotone_arcsin : Monotone arcsin :=
  (Subtype.mono_coe _).comp <| sinOrderIso.symm.Monotone.IccExtend _
#align real.monotone_arcsin Real.monotone_arcsin
-/

/- warning: real.inj_on_arcsin -> Real.injOn_arcsin is a dubious translation:
lean 3 declaration is
  Set.InjOn.{0, 0} Real Real Real.arcsin (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.InjOn.{0, 0} Real Real Real.arcsin (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.inj_on_arcsin Real.injOn_arcsinₓ'. -/
theorem injOn_arcsin : InjOn arcsin (Icc (-1) 1) :=
  strictMonoOn_arcsin.InjOn
#align real.inj_on_arcsin Real.injOn_arcsin

/- warning: real.arcsin_inj -> Real.arcsin_inj is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) y) -> (LE.le.{0} Real Real.hasLe y (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (Eq.{1} Real (Real.arcsin x) (Real.arcsin y)) (Eq.{1} Real x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y) -> (LE.le.{0} Real Real.instLEReal y (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Iff (Eq.{1} Real (Real.arcsin x) (Real.arcsin y)) (Eq.{1} Real x y))
Case conversion may be inaccurate. Consider using '#align real.arcsin_inj Real.arcsin_injₓ'. -/
theorem arcsin_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    arcsin x = arcsin y ↔ x = y :=
  injOn_arcsin.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
#align real.arcsin_inj Real.arcsin_inj

#print Real.continuous_arcsin /-
@[continuity]
theorem continuous_arcsin : Continuous arcsin :=
  continuous_subtype_val.comp sinOrderIso.symm.Continuous.Icc_extend'
#align real.continuous_arcsin Real.continuous_arcsin
-/

#print Real.continuousAt_arcsin /-
theorem continuousAt_arcsin {x : ℝ} : ContinuousAt arcsin x :=
  continuous_arcsin.ContinuousAt
#align real.continuous_at_arcsin Real.continuousAt_arcsin
-/

/- warning: real.arcsin_eq_of_sin_eq -> Real.arcsin_eq_of_sin_eq is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Eq.{1} Real (Real.sin x) y) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Eq.{1} Real (Real.arcsin y) x)
but is expected to have type
  forall {x : Real} {y : Real}, (Eq.{1} Real (Real.sin x) y) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Eq.{1} Real (Real.arcsin y) x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_of_sin_eq Real.arcsin_eq_of_sin_eqₓ'. -/
theorem arcsin_eq_of_sin_eq {x y : ℝ} (h₁ : sin x = y) (h₂ : x ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin y = x := by
  subst y
  exact inj_on_sin (arcsin_mem_Icc _) h₂ (sin_arcsin' (sin_mem_Icc x))
#align real.arcsin_eq_of_sin_eq Real.arcsin_eq_of_sin_eq

/- warning: real.arcsin_zero -> Real.arcsin_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.arcsin (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.arcsin (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.arcsin_zero Real.arcsin_zeroₓ'. -/
@[simp]
theorem arcsin_zero : arcsin 0 = 0 :=
  arcsin_eq_of_sin_eq sin_zero ⟨neg_nonpos.2 pi_div_two_pos.le, pi_div_two_pos.le⟩
#align real.arcsin_zero Real.arcsin_zero

/- warning: real.arcsin_one -> Real.arcsin_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.arcsin (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Eq.{1} Real (Real.arcsin (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_one Real.arcsin_oneₓ'. -/
@[simp]
theorem arcsin_one : arcsin 1 = π / 2 :=
  arcsin_eq_of_sin_eq sin_pi_div_two <| right_mem_Icc.2 (neg_le_self pi_div_two_pos.le)
#align real.arcsin_one Real.arcsin_one

/- warning: real.arcsin_of_one_le -> Real.arcsin_of_one_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (Eq.{1} Real (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (Eq.{1} Real (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_of_one_le Real.arcsin_of_one_leₓ'. -/
theorem arcsin_of_one_le {x : ℝ} (hx : 1 ≤ x) : arcsin x = π / 2 := by
  rw [← arcsin_proj_Icc, proj_Icc_of_right_le _ hx, Subtype.coe_mk, arcsin_one]
#align real.arcsin_of_one_le Real.arcsin_of_one_le

/- warning: real.arcsin_neg_one -> Real.arcsin_neg_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.arcsin (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Eq.{1} Real (Real.arcsin (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_neg_one Real.arcsin_neg_oneₓ'. -/
theorem arcsin_neg_one : arcsin (-1) = -(π / 2) :=
  arcsin_eq_of_sin_eq (by rw [sin_neg, sin_pi_div_two]) <|
    left_mem_Icc.2 (neg_le_self pi_div_two_pos.le)
#align real.arcsin_neg_one Real.arcsin_neg_one

/- warning: real.arcsin_of_le_neg_one -> Real.arcsin_of_le_neg_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Eq.{1} Real (Real.arcsin x) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Eq.{1} Real (Real.arcsin x) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_of_le_neg_one Real.arcsin_of_le_neg_oneₓ'. -/
theorem arcsin_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arcsin x = -(π / 2) := by
  rw [← arcsin_proj_Icc, proj_Icc_of_le_left _ hx, Subtype.coe_mk, arcsin_neg_one]
#align real.arcsin_of_le_neg_one Real.arcsin_of_le_neg_one

/- warning: real.arcsin_neg -> Real.arcsin_neg is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.arcsin (Neg.neg.{0} Real Real.hasNeg x)) (Neg.neg.{0} Real Real.hasNeg (Real.arcsin x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.arcsin (Neg.neg.{0} Real Real.instNegReal x)) (Neg.neg.{0} Real Real.instNegReal (Real.arcsin x))
Case conversion may be inaccurate. Consider using '#align real.arcsin_neg Real.arcsin_negₓ'. -/
@[simp]
theorem arcsin_neg (x : ℝ) : arcsin (-x) = -arcsin x :=
  by
  cases' le_total x (-1) with hx₁ hx₁
  · rw [arcsin_of_le_neg_one hx₁, neg_neg, arcsin_of_one_le (le_neg.2 hx₁)]
  cases' le_total 1 x with hx₂ hx₂
  · rw [arcsin_of_one_le hx₂, arcsin_of_le_neg_one (neg_le_neg hx₂)]
  refine' arcsin_eq_of_sin_eq _ _
  · rw [sin_neg, sin_arcsin hx₁ hx₂]
  · exact ⟨neg_le_neg (arcsin_le_pi_div_two _), neg_le.2 (neg_pi_div_two_le_arcsin _)⟩
#align real.arcsin_neg Real.arcsin_neg

/- warning: real.arcsin_le_iff_le_sin -> Real.arcsin_le_iff_le_sin is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (LE.le.{0} Real Real.hasLe (Real.arcsin x) y) (LE.le.{0} Real Real.hasLe x (Real.sin y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.arcsin x) y) (LE.le.{0} Real Real.instLEReal x (Real.sin y)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_le_iff_le_sin Real.arcsin_le_iff_le_sinₓ'. -/
theorem arcsin_le_iff_le_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  rw [← arcsin_sin' hy, strict_mono_on_arcsin.le_iff_le hx (sin_mem_Icc _), arcsin_sin' hy]
#align real.arcsin_le_iff_le_sin Real.arcsin_le_iff_le_sin

/- warning: real.arcsin_le_iff_le_sin' -> Real.arcsin_le_iff_le_sin' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Ico.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (LE.le.{0} Real Real.hasLe (Real.arcsin x) y) (LE.le.{0} Real Real.hasLe x (Real.sin y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Ico.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.arcsin x) y) (LE.le.{0} Real Real.instLEReal x (Real.sin y)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_le_iff_le_sin' Real.arcsin_le_iff_le_sin'ₓ'. -/
theorem arcsin_le_iff_le_sin' {x y : ℝ} (hy : y ∈ Ico (-(π / 2)) (π / 2)) :
    arcsin x ≤ y ↔ x ≤ sin y := by
  cases' le_total x (-1) with hx₁ hx₁
  · simp [arcsin_of_le_neg_one hx₁, hy.1, hx₁.trans (neg_one_le_sin _)]
  cases' lt_or_le 1 x with hx₂ hx₂
  · simp [arcsin_of_one_le hx₂.le, hy.2.not_le, (sin_le_one y).trans_lt hx₂]
  exact arcsin_le_iff_le_sin ⟨hx₁, hx₂⟩ (mem_Icc_of_Ico hy)
#align real.arcsin_le_iff_le_sin' Real.arcsin_le_iff_le_sin'

/- warning: real.le_arcsin_iff_sin_le -> Real.le_arcsin_iff_sin_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.arcsin y)) (LE.le.{0} Real Real.hasLe (Real.sin x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.arcsin y)) (LE.le.{0} Real Real.instLEReal (Real.sin x) y))
Case conversion may be inaccurate. Consider using '#align real.le_arcsin_iff_sin_le Real.le_arcsin_iff_sin_leₓ'. -/
theorem le_arcsin_iff_sin_le {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg,
    arcsin_le_iff_le_sin ⟨neg_le_neg hy.2, neg_le.2 hy.1⟩ ⟨neg_le_neg hx.2, neg_le.2 hx.1⟩, sin_neg,
    neg_le_neg_iff]
#align real.le_arcsin_iff_sin_le Real.le_arcsin_iff_sin_le

/- warning: real.le_arcsin_iff_sin_le' -> Real.le_arcsin_iff_sin_le' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.arcsin y)) (LE.le.{0} Real Real.hasLe (Real.sin x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.arcsin y)) (LE.le.{0} Real Real.instLEReal (Real.sin x) y))
Case conversion may be inaccurate. Consider using '#align real.le_arcsin_iff_sin_le' Real.le_arcsin_iff_sin_le'ₓ'. -/
theorem le_arcsin_iff_sin_le' {x y : ℝ} (hx : x ∈ Ioc (-(π / 2)) (π / 2)) :
    x ≤ arcsin y ↔ sin x ≤ y := by
  rw [← neg_le_neg_iff, ← arcsin_neg, arcsin_le_iff_le_sin' ⟨neg_le_neg hx.2, neg_lt.2 hx.1⟩,
    sin_neg, neg_le_neg_iff]
#align real.le_arcsin_iff_sin_le' Real.le_arcsin_iff_sin_le'

/- warning: real.arcsin_lt_iff_lt_sin -> Real.arcsin_lt_iff_lt_sin is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.arcsin x) y) (LT.lt.{0} Real Real.hasLt x (Real.sin y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.arcsin x) y) (LT.lt.{0} Real Real.instLTReal x (Real.sin y)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_lt_iff_lt_sin Real.arcsin_lt_iff_lt_sinₓ'. -/
theorem arcsin_lt_iff_lt_sin {x y : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_le.symm.trans <| (not_congr <| le_arcsin_iff_sin_le hy hx).trans not_le
#align real.arcsin_lt_iff_lt_sin Real.arcsin_lt_iff_lt_sin

/- warning: real.arcsin_lt_iff_lt_sin' -> Real.arcsin_lt_iff_lt_sin' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Ioc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.arcsin x) y) (LT.lt.{0} Real Real.hasLt x (Real.sin y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Ioc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.arcsin x) y) (LT.lt.{0} Real Real.instLTReal x (Real.sin y)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_lt_iff_lt_sin' Real.arcsin_lt_iff_lt_sin'ₓ'. -/
theorem arcsin_lt_iff_lt_sin' {x y : ℝ} (hy : y ∈ Ioc (-(π / 2)) (π / 2)) :
    arcsin x < y ↔ x < sin y :=
  not_le.symm.trans <| (not_congr <| le_arcsin_iff_sin_le' hy).trans not_le
#align real.arcsin_lt_iff_lt_sin' Real.arcsin_lt_iff_lt_sin'

/- warning: real.lt_arcsin_iff_sin_lt -> Real.lt_arcsin_iff_sin_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Iff (LT.lt.{0} Real Real.hasLt x (Real.arcsin y)) (LT.lt.{0} Real Real.hasLt (Real.sin x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Iff (LT.lt.{0} Real Real.instLTReal x (Real.arcsin y)) (LT.lt.{0} Real Real.instLTReal (Real.sin x) y))
Case conversion may be inaccurate. Consider using '#align real.lt_arcsin_iff_sin_lt Real.lt_arcsin_iff_sin_ltₓ'. -/
theorem lt_arcsin_iff_sin_lt {x y : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) (hy : y ∈ Icc (-1 : ℝ) 1) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin hy hx).trans not_le
#align real.lt_arcsin_iff_sin_lt Real.lt_arcsin_iff_sin_lt

/- warning: real.lt_arcsin_iff_sin_lt' -> Real.lt_arcsin_iff_sin_lt' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ico.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (LT.lt.{0} Real Real.hasLt x (Real.arcsin y)) (LT.lt.{0} Real Real.hasLt (Real.sin x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ico.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (LT.lt.{0} Real Real.instLTReal x (Real.arcsin y)) (LT.lt.{0} Real Real.instLTReal (Real.sin x) y))
Case conversion may be inaccurate. Consider using '#align real.lt_arcsin_iff_sin_lt' Real.lt_arcsin_iff_sin_lt'ₓ'. -/
theorem lt_arcsin_iff_sin_lt' {x y : ℝ} (hx : x ∈ Ico (-(π / 2)) (π / 2)) :
    x < arcsin y ↔ sin x < y :=
  not_le.symm.trans <| (not_congr <| arcsin_le_iff_le_sin' hx).trans not_le
#align real.lt_arcsin_iff_sin_lt' Real.lt_arcsin_iff_sin_lt'

/- warning: real.arcsin_eq_iff_eq_sin -> Real.arcsin_eq_iff_eq_sin is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) y (Set.Ioo.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (Iff (Eq.{1} Real (Real.arcsin x) y) (Eq.{1} Real x (Real.sin y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) y (Set.Ioo.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (Iff (Eq.{1} Real (Real.arcsin x) y) (Eq.{1} Real x (Real.sin y)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_iff_eq_sin Real.arcsin_eq_iff_eq_sinₓ'. -/
theorem arcsin_eq_iff_eq_sin {x y : ℝ} (hy : y ∈ Ioo (-(π / 2)) (π / 2)) :
    arcsin x = y ↔ x = sin y := by
  simp only [le_antisymm_iff, arcsin_le_iff_le_sin' (mem_Ico_of_Ioo hy),
    le_arcsin_iff_sin_le' (mem_Ioc_of_Ioo hy)]
#align real.arcsin_eq_iff_eq_sin Real.arcsin_eq_iff_eq_sin

/- warning: real.arcsin_nonneg -> Real.arcsin_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.arcsin x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.arcsin x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_nonneg Real.arcsin_nonnegₓ'. -/
@[simp]
theorem arcsin_nonneg {x : ℝ} : 0 ≤ arcsin x ↔ 0 ≤ x :=
  (le_arcsin_iff_sin_le' ⟨neg_lt_zero.2 pi_div_two_pos, pi_div_two_pos.le⟩).trans <| by
    rw [sin_zero]
#align real.arcsin_nonneg Real.arcsin_nonneg

/- warning: real.arcsin_nonpos -> Real.arcsin_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.arcsin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.arcsin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_nonpos Real.arcsin_nonposₓ'. -/
@[simp]
theorem arcsin_nonpos {x : ℝ} : arcsin x ≤ 0 ↔ x ≤ 0 :=
  neg_nonneg.symm.trans <| arcsin_neg x ▸ arcsin_nonneg.trans neg_nonneg
#align real.arcsin_nonpos Real.arcsin_nonpos

/- warning: real.arcsin_eq_zero_iff -> Real.arcsin_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.arcsin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.arcsin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_zero_iff Real.arcsin_eq_zero_iffₓ'. -/
@[simp]
theorem arcsin_eq_zero_iff {x : ℝ} : arcsin x = 0 ↔ x = 0 := by simp [le_antisymm_iff]
#align real.arcsin_eq_zero_iff Real.arcsin_eq_zero_iff

/- warning: real.zero_eq_arcsin_iff -> Real.zero_eq_arcsin_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.arcsin x)) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.arcsin x)) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.zero_eq_arcsin_iff Real.zero_eq_arcsin_iffₓ'. -/
@[simp]
theorem zero_eq_arcsin_iff {x} : 0 = arcsin x ↔ x = 0 :=
  eq_comm.trans arcsin_eq_zero_iff
#align real.zero_eq_arcsin_iff Real.zero_eq_arcsin_iff

/- warning: real.arcsin_pos -> Real.arcsin_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.arcsin x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.arcsin x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_pos Real.arcsin_posₓ'. -/
@[simp]
theorem arcsin_pos {x : ℝ} : 0 < arcsin x ↔ 0 < x :=
  lt_iff_lt_of_le_iff_le arcsin_nonpos
#align real.arcsin_pos Real.arcsin_pos

/- warning: real.arcsin_lt_zero -> Real.arcsin_lt_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (Real.arcsin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (Real.arcsin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_lt_zero Real.arcsin_lt_zeroₓ'. -/
@[simp]
theorem arcsin_lt_zero {x : ℝ} : arcsin x < 0 ↔ x < 0 :=
  lt_iff_lt_of_le_iff_le arcsin_nonneg
#align real.arcsin_lt_zero Real.arcsin_lt_zero

/- warning: real.arcsin_lt_pi_div_two -> Real.arcsin_lt_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.arcsin_lt_pi_div_two Real.arcsin_lt_pi_div_twoₓ'. -/
@[simp]
theorem arcsin_lt_pi_div_two {x : ℝ} : arcsin x < π / 2 ↔ x < 1 :=
  (arcsin_lt_iff_lt_sin' (right_mem_Ioc.2 <| neg_lt_self pi_div_two_pos)).trans <| by
    rw [sin_pi_div_two]
#align real.arcsin_lt_pi_div_two Real.arcsin_lt_pi_div_two

/- warning: real.neg_pi_div_two_lt_arcsin -> Real.neg_pi_div_two_lt_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Real.arcsin x)) (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Real.arcsin x)) (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x)
Case conversion may be inaccurate. Consider using '#align real.neg_pi_div_two_lt_arcsin Real.neg_pi_div_two_lt_arcsinₓ'. -/
@[simp]
theorem neg_pi_div_two_lt_arcsin {x : ℝ} : -(π / 2) < arcsin x ↔ -1 < x :=
  (lt_arcsin_iff_sin_lt' <| left_mem_Ico.2 <| neg_lt_self pi_div_two_pos).trans <| by
    rw [sin_neg, sin_pi_div_two]
#align real.neg_pi_div_two_lt_arcsin Real.neg_pi_div_two_lt_arcsin

/- warning: real.arcsin_eq_pi_div_two -> Real.arcsin_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.arcsin x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_pi_div_two Real.arcsin_eq_pi_div_twoₓ'. -/
@[simp]
theorem arcsin_eq_pi_div_two {x : ℝ} : arcsin x = π / 2 ↔ 1 ≤ x :=
  ⟨fun h => not_lt.1 fun h' => (arcsin_lt_pi_div_two.2 h').Ne h, arcsin_of_one_le⟩
#align real.arcsin_eq_pi_div_two Real.arcsin_eq_pi_div_two

/- warning: real.pi_div_two_eq_arcsin -> Real.pi_div_two_eq_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Real.arcsin x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Real.arcsin x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)
Case conversion may be inaccurate. Consider using '#align real.pi_div_two_eq_arcsin Real.pi_div_two_eq_arcsinₓ'. -/
@[simp]
theorem pi_div_two_eq_arcsin {x} : π / 2 = arcsin x ↔ 1 ≤ x :=
  eq_comm.trans arcsin_eq_pi_div_two
#align real.pi_div_two_eq_arcsin Real.pi_div_two_eq_arcsin

/- warning: real.pi_div_two_le_arcsin -> Real.pi_div_two_le_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Real.arcsin x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Real.arcsin x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)
Case conversion may be inaccurate. Consider using '#align real.pi_div_two_le_arcsin Real.pi_div_two_le_arcsinₓ'. -/
@[simp]
theorem pi_div_two_le_arcsin {x} : π / 2 ≤ arcsin x ↔ 1 ≤ x :=
  (arcsin_le_pi_div_two x).le_iff_eq.trans pi_div_two_eq_arcsin
#align real.pi_div_two_le_arcsin Real.pi_div_two_le_arcsin

/- warning: real.arcsin_eq_neg_pi_div_two -> Real.arcsin_eq_neg_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.arcsin x) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (LE.le.{0} Real Real.hasLe x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.arcsin x) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (LE.le.{0} Real Real.instLEReal x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_neg_pi_div_two Real.arcsin_eq_neg_pi_div_twoₓ'. -/
@[simp]
theorem arcsin_eq_neg_pi_div_two {x : ℝ} : arcsin x = -(π / 2) ↔ x ≤ -1 :=
  ⟨fun h => not_lt.1 fun h' => (neg_pi_div_two_lt_arcsin.2 h').ne' h, arcsin_of_le_neg_one⟩
#align real.arcsin_eq_neg_pi_div_two Real.arcsin_eq_neg_pi_div_two

/- warning: real.neg_pi_div_two_eq_arcsin -> Real.neg_pi_div_two_eq_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Real.arcsin x)) (LE.le.{0} Real Real.hasLe x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Real.arcsin x)) (LE.le.{0} Real Real.instLEReal x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.neg_pi_div_two_eq_arcsin Real.neg_pi_div_two_eq_arcsinₓ'. -/
@[simp]
theorem neg_pi_div_two_eq_arcsin {x} : -(π / 2) = arcsin x ↔ x ≤ -1 :=
  eq_comm.trans arcsin_eq_neg_pi_div_two
#align real.neg_pi_div_two_eq_arcsin Real.neg_pi_div_two_eq_arcsin

/- warning: real.arcsin_le_neg_pi_div_two -> Real.arcsin_le_neg_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.arcsin x) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (LE.le.{0} Real Real.hasLe x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.arcsin x) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (LE.le.{0} Real Real.instLEReal x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_le_neg_pi_div_two Real.arcsin_le_neg_pi_div_twoₓ'. -/
@[simp]
theorem arcsin_le_neg_pi_div_two {x} : arcsin x ≤ -(π / 2) ↔ x ≤ -1 :=
  (neg_pi_div_two_le_arcsin x).le_iff_eq.trans arcsin_eq_neg_pi_div_two
#align real.arcsin_le_neg_pi_div_two Real.arcsin_le_neg_pi_div_two

/- warning: real.pi_div_four_le_arcsin -> Real.pi_div_four_le_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Real.arcsin x)) (LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (Real.arcsin x)) (LE.le.{0} Real Real.instLEReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) x)
Case conversion may be inaccurate. Consider using '#align real.pi_div_four_le_arcsin Real.pi_div_four_le_arcsinₓ'. -/
@[simp]
theorem pi_div_four_le_arcsin {x} : π / 4 ≤ arcsin x ↔ sqrt 2 / 2 ≤ x :=
  by
  rw [← sin_pi_div_four, le_arcsin_iff_sin_le']
  have := pi_pos
  constructor <;> linarith
#align real.pi_div_four_le_arcsin Real.pi_div_four_le_arcsin

/- warning: real.maps_to_sin_Ioo -> Real.mapsTo_sin_Ioo is a dubious translation:
lean 3 declaration is
  Set.MapsTo.{0, 0} Real Real Real.sin (Set.Ioo.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Set.Ioo.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.MapsTo.{0, 0} Real Real Real.sin (Set.Ioo.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Set.Ioo.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.maps_to_sin_Ioo Real.mapsTo_sin_Iooₓ'. -/
theorem mapsTo_sin_Ioo : MapsTo sin (Ioo (-(π / 2)) (π / 2)) (Ioo (-1) 1) := fun x h => by
  rwa [mem_Ioo, ← arcsin_lt_pi_div_two, ← neg_pi_div_two_lt_arcsin, arcsin_sin h.1.le h.2.le]
#align real.maps_to_sin_Ioo Real.mapsTo_sin_Ioo

#print Real.sinLocalHomeomorph /-
/-- `real.sin` as a `local_homeomorph` between `(-π / 2, π / 2)` and `(-1, 1)`. -/
@[simp]
def sinLocalHomeomorph : LocalHomeomorph ℝ ℝ
    where
  toFun := sin
  invFun := arcsin
  source := Ioo (-(π / 2)) (π / 2)
  target := Ioo (-1) 1
  map_source' := mapsTo_sin_Ioo
  map_target' y hy := ⟨neg_pi_div_two_lt_arcsin.2 hy.1, arcsin_lt_pi_div_two.2 hy.2⟩
  left_inv' x hx := arcsin_sin hx.1.le hx.2.le
  right_inv' y hy := sin_arcsin hy.1.le hy.2.le
  open_source := isOpen_Ioo
  open_target := isOpen_Ioo
  continuous_toFun := continuous_sin.ContinuousOn
  continuous_invFun := continuous_arcsin.ContinuousOn
#align real.sin_local_homeomorph Real.sinLocalHomeomorph
-/

/- warning: real.cos_arcsin_nonneg -> Real.cos_arcsin_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos (Real.arcsin x))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos (Real.arcsin x))
Case conversion may be inaccurate. Consider using '#align real.cos_arcsin_nonneg Real.cos_arcsin_nonnegₓ'. -/
theorem cos_arcsin_nonneg (x : ℝ) : 0 ≤ cos (arcsin x) :=
  cos_nonneg_of_mem_Icc ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩
#align real.cos_arcsin_nonneg Real.cos_arcsin_nonneg

/- warning: real.cos_arcsin -> Real.cos_arcsin is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.cos (Real.arcsin x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.cos (Real.arcsin x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.cos_arcsin Real.cos_arcsinₓ'. -/
-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
theorem cos_arcsin (x : ℝ) : cos (arcsin x) = sqrt (1 - x ^ 2) :=
  by
  by_cases hx₁ : -1 ≤ x; swap
  · rw [not_le] at hx₁
    rw [arcsin_of_le_neg_one hx₁.le, cos_neg, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x ≤ 1; swap
  · rw [not_le] at hx₂
    rw [arcsin_of_one_le hx₂.le, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
    nlinarith
  have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
  rw [← eq_sub_iff_add_eq', ← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))), sq,
    sqrt_mul_self (cos_arcsin_nonneg _)] at this
  rw [this, sin_arcsin hx₁ hx₂]
#align real.cos_arcsin Real.cos_arcsin

/- warning: real.tan_arcsin -> Real.tan_arcsin is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.tan (Real.arcsin x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.tan (Real.arcsin x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align real.tan_arcsin Real.tan_arcsinₓ'. -/
-- The junk values for `arcsin` and `sqrt` make this true even outside `[-1, 1]`.
theorem tan_arcsin (x : ℝ) : tan (arcsin x) = x / sqrt (1 - x ^ 2) :=
  by
  rw [tan_eq_sin_div_cos, cos_arcsin]
  by_cases hx₁ : -1 ≤ x; swap
  · have h : sqrt (1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x ≤ 1; swap
  · have h : sqrt (1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]
#align real.tan_arcsin Real.tan_arcsin

#print Real.arccos /-
/-- Inverse of the `cos` function, returns values in the range `0 ≤ arccos x` and `arccos x ≤ π`.
  It defaults to `π` on `(-∞, -1)` and to `0` to `(1, ∞)`. -/
@[pp_nodot]
noncomputable def arccos (x : ℝ) : ℝ :=
  π / 2 - arcsin x
#align real.arccos Real.arccos
-/

/- warning: real.arccos_eq_pi_div_two_sub_arcsin -> Real.arccos_eq_pi_div_two_sub_arcsin is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.arccos x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Real.arcsin x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.arccos x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Real.arcsin x))
Case conversion may be inaccurate. Consider using '#align real.arccos_eq_pi_div_two_sub_arcsin Real.arccos_eq_pi_div_two_sub_arcsinₓ'. -/
theorem arccos_eq_pi_div_two_sub_arcsin (x : ℝ) : arccos x = π / 2 - arcsin x :=
  rfl
#align real.arccos_eq_pi_div_two_sub_arcsin Real.arccos_eq_pi_div_two_sub_arcsin

/- warning: real.arcsin_eq_pi_div_two_sub_arccos -> Real.arcsin_eq_pi_div_two_sub_arccos is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.arcsin x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Real.arccos x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.arcsin x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Real.arccos x))
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_pi_div_two_sub_arccos Real.arcsin_eq_pi_div_two_sub_arccosₓ'. -/
theorem arcsin_eq_pi_div_two_sub_arccos (x : ℝ) : arcsin x = π / 2 - arccos x := by simp [arccos]
#align real.arcsin_eq_pi_div_two_sub_arccos Real.arcsin_eq_pi_div_two_sub_arccos

/- warning: real.arccos_le_pi -> Real.arccos_le_pi is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (Real.arccos x) Real.pi
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (Real.arccos x) Real.pi
Case conversion may be inaccurate. Consider using '#align real.arccos_le_pi Real.arccos_le_piₓ'. -/
theorem arccos_le_pi (x : ℝ) : arccos x ≤ π := by
  unfold arccos <;> linarith [neg_pi_div_two_le_arcsin x]
#align real.arccos_le_pi Real.arccos_le_pi

/- warning: real.arccos_nonneg -> Real.arccos_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.arccos x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.arccos x)
Case conversion may be inaccurate. Consider using '#align real.arccos_nonneg Real.arccos_nonnegₓ'. -/
theorem arccos_nonneg (x : ℝ) : 0 ≤ arccos x := by
  unfold arccos <;> linarith [arcsin_le_pi_div_two x]
#align real.arccos_nonneg Real.arccos_nonneg

/- warning: real.arccos_pos -> Real.arccos_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.arccos x)) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.arccos x)) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.arccos_pos Real.arccos_posₓ'. -/
@[simp]
theorem arccos_pos {x : ℝ} : 0 < arccos x ↔ x < 1 := by simp [arccos]
#align real.arccos_pos Real.arccos_pos

/- warning: real.cos_arccos -> Real.cos_arccos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} Real (Real.cos (Real.arccos x)) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} Real (Real.cos (Real.arccos x)) x)
Case conversion may be inaccurate. Consider using '#align real.cos_arccos Real.cos_arccosₓ'. -/
theorem cos_arccos {x : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) : cos (arccos x) = x := by
  rw [arccos, cos_pi_div_two_sub, sin_arcsin hx₁ hx₂]
#align real.cos_arccos Real.cos_arccos

/- warning: real.arccos_cos -> Real.arccos_cos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x Real.pi) -> (Eq.{1} Real (Real.arccos (Real.cos x)) x)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x Real.pi) -> (Eq.{1} Real (Real.arccos (Real.cos x)) x)
Case conversion may be inaccurate. Consider using '#align real.arccos_cos Real.arccos_cosₓ'. -/
theorem arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x := by
  rw [arccos, ← sin_pi_div_two_sub, arcsin_sin] <;> simp [sub_eq_add_neg] <;> linarith
#align real.arccos_cos Real.arccos_cos

/- warning: real.strict_anti_on_arccos -> Real.strictAntiOn_arccos is a dubious translation:
lean 3 declaration is
  StrictAntiOn.{0, 0} Real Real Real.preorder Real.preorder Real.arccos (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  StrictAntiOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.arccos (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.strict_anti_on_arccos Real.strictAntiOn_arccosₓ'. -/
theorem strictAntiOn_arccos : StrictAntiOn arccos (Icc (-1) 1) := fun x hx y hy h =>
  sub_lt_sub_left (strictMonoOn_arcsin hx hy h) _
#align real.strict_anti_on_arccos Real.strictAntiOn_arccos

/- warning: real.arccos_inj_on -> Real.arccos_injOn is a dubious translation:
lean 3 declaration is
  Set.InjOn.{0, 0} Real Real Real.arccos (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.InjOn.{0, 0} Real Real Real.arccos (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.arccos_inj_on Real.arccos_injOnₓ'. -/
theorem arccos_injOn : InjOn arccos (Icc (-1) 1) :=
  strictAntiOn_arccos.InjOn
#align real.arccos_inj_on Real.arccos_injOn

/- warning: real.arccos_inj -> Real.arccos_inj is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) y) -> (LE.le.{0} Real Real.hasLe y (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (Eq.{1} Real (Real.arccos x) (Real.arccos y)) (Eq.{1} Real x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) y) -> (LE.le.{0} Real Real.instLEReal y (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Iff (Eq.{1} Real (Real.arccos x) (Real.arccos y)) (Eq.{1} Real x y))
Case conversion may be inaccurate. Consider using '#align real.arccos_inj Real.arccos_injₓ'. -/
theorem arccos_inj {x y : ℝ} (hx₁ : -1 ≤ x) (hx₂ : x ≤ 1) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) :
    arccos x = arccos y ↔ x = y :=
  arccos_injOn.eq_iff ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
#align real.arccos_inj Real.arccos_inj

/- warning: real.arccos_zero -> Real.arccos_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.arccos (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Eq.{1} Real (Real.arccos (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.arccos_zero Real.arccos_zeroₓ'. -/
@[simp]
theorem arccos_zero : arccos 0 = π / 2 := by simp [arccos]
#align real.arccos_zero Real.arccos_zero

/- warning: real.arccos_one -> Real.arccos_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.arccos (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.arccos (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.arccos_one Real.arccos_oneₓ'. -/
@[simp]
theorem arccos_one : arccos 1 = 0 := by simp [arccos]
#align real.arccos_one Real.arccos_one

/- warning: real.arccos_neg_one -> Real.arccos_neg_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.arccos (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real.pi
but is expected to have type
  Eq.{1} Real (Real.arccos (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) Real.pi
Case conversion may be inaccurate. Consider using '#align real.arccos_neg_one Real.arccos_neg_oneₓ'. -/
@[simp]
theorem arccos_neg_one : arccos (-1) = π := by simp [arccos, add_halves]
#align real.arccos_neg_one Real.arccos_neg_one

/- warning: real.arccos_eq_zero -> Real.arccos_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.arccos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x)
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.arccos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x)
Case conversion may be inaccurate. Consider using '#align real.arccos_eq_zero Real.arccos_eq_zeroₓ'. -/
@[simp]
theorem arccos_eq_zero {x} : arccos x = 0 ↔ 1 ≤ x := by simp [arccos, sub_eq_zero]
#align real.arccos_eq_zero Real.arccos_eq_zero

/- warning: real.arccos_eq_pi_div_two -> Real.arccos_eq_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.arccos_eq_pi_div_two Real.arccos_eq_pi_div_twoₓ'. -/
@[simp]
theorem arccos_eq_pi_div_two {x} : arccos x = π / 2 ↔ x = 0 := by simp [arccos]
#align real.arccos_eq_pi_div_two Real.arccos_eq_pi_div_two

/- warning: real.arccos_eq_pi -> Real.arccos_eq_pi is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.arccos x) Real.pi) (LE.le.{0} Real Real.hasLe x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.arccos x) Real.pi) (LE.le.{0} Real Real.instLEReal x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.arccos_eq_pi Real.arccos_eq_piₓ'. -/
@[simp]
theorem arccos_eq_pi {x} : arccos x = π ↔ x ≤ -1 := by
  rw [arccos, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', div_two_sub_self, neg_pi_div_two_eq_arcsin]
#align real.arccos_eq_pi Real.arccos_eq_pi

/- warning: real.arccos_neg -> Real.arccos_neg is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.arccos (Neg.neg.{0} Real Real.hasNeg x)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) Real.pi (Real.arccos x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.arccos (Neg.neg.{0} Real Real.instNegReal x)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) Real.pi (Real.arccos x))
Case conversion may be inaccurate. Consider using '#align real.arccos_neg Real.arccos_negₓ'. -/
theorem arccos_neg (x : ℝ) : arccos (-x) = π - arccos x := by
  rw [← add_halves π, arccos, arcsin_neg, arccos, add_sub_assoc, sub_sub_self, sub_neg_eq_add]
#align real.arccos_neg Real.arccos_neg

/- warning: real.arccos_of_one_le -> Real.arccos_of_one_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (Eq.{1} Real (Real.arccos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (Eq.{1} Real (Real.arccos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.arccos_of_one_le Real.arccos_of_one_leₓ'. -/
theorem arccos_of_one_le {x : ℝ} (hx : 1 ≤ x) : arccos x = 0 := by
  rw [arccos, arcsin_of_one_le hx, sub_self]
#align real.arccos_of_one_le Real.arccos_of_one_le

/- warning: real.arccos_of_le_neg_one -> Real.arccos_of_le_neg_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) -> (Eq.{1} Real (Real.arccos x) Real.pi)
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) -> (Eq.{1} Real (Real.arccos x) Real.pi)
Case conversion may be inaccurate. Consider using '#align real.arccos_of_le_neg_one Real.arccos_of_le_neg_oneₓ'. -/
theorem arccos_of_le_neg_one {x : ℝ} (hx : x ≤ -1) : arccos x = π := by
  rw [arccos, arcsin_of_le_neg_one hx, sub_neg_eq_add, add_halves']
#align real.arccos_of_le_neg_one Real.arccos_of_le_neg_one

/- warning: real.sin_arccos -> Real.sin_arccos is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.sin (Real.arccos x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.sin (Real.arccos x)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.sin_arccos Real.sin_arccosₓ'. -/
-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
theorem sin_arccos (x : ℝ) : sin (arccos x) = sqrt (1 - x ^ 2) :=
  by
  by_cases hx₁ : -1 ≤ x; swap
  · rw [not_le] at hx₁
    rw [arccos_of_le_neg_one hx₁.le, sin_pi, sqrt_eq_zero_of_nonpos]
    nlinarith
  by_cases hx₂ : x ≤ 1; swap
  · rw [not_le] at hx₂
    rw [arccos_of_one_le hx₂.le, sin_zero, sqrt_eq_zero_of_nonpos]
    nlinarith
  rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin]
#align real.sin_arccos Real.sin_arccos

/- warning: real.arccos_le_pi_div_two -> Real.arccos_le_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.arccos_le_pi_div_two Real.arccos_le_pi_div_twoₓ'. -/
@[simp]
theorem arccos_le_pi_div_two {x} : arccos x ≤ π / 2 ↔ 0 ≤ x := by simp [arccos]
#align real.arccos_le_pi_div_two Real.arccos_le_pi_div_two

/- warning: real.arccos_lt_pi_div_two -> Real.arccos_lt_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} Real Real.hasLt (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} Real Real.instLTReal (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align real.arccos_lt_pi_div_two Real.arccos_lt_pi_div_twoₓ'. -/
@[simp]
theorem arccos_lt_pi_div_two {x : ℝ} : arccos x < π / 2 ↔ 0 < x := by simp [arccos]
#align real.arccos_lt_pi_div_two Real.arccos_lt_pi_div_two

/- warning: real.arccos_le_pi_div_four -> Real.arccos_le_pi_div_four is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} Real Real.hasLe (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} Real Real.instLEReal (Real.arccos x) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (LE.le.{0} Real Real.instLEReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) x)
Case conversion may be inaccurate. Consider using '#align real.arccos_le_pi_div_four Real.arccos_le_pi_div_fourₓ'. -/
@[simp]
theorem arccos_le_pi_div_four {x} : arccos x ≤ π / 4 ↔ sqrt 2 / 2 ≤ x :=
  by
  rw [arccos, ← pi_div_four_le_arcsin]
  constructor <;>
    · intro
      linarith
#align real.arccos_le_pi_div_four Real.arccos_le_pi_div_four

#print Real.continuous_arccos /-
@[continuity]
theorem continuous_arccos : Continuous arccos :=
  continuous_const.sub continuous_arcsin
#align real.continuous_arccos Real.continuous_arccos
-/

/- warning: real.tan_arccos -> Real.tan_arccos is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.tan (Real.arccos x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))) x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.tan (Real.arccos x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))) x)
Case conversion may be inaccurate. Consider using '#align real.tan_arccos Real.tan_arccosₓ'. -/
-- The junk values for `arccos` and `sqrt` make this true even outside `[-1, 1]`.
theorem tan_arccos (x : ℝ) : tan (arccos x) = sqrt (1 - x ^ 2) / x := by
  rw [arccos, tan_pi_div_two_sub, tan_arcsin, inv_div]
#align real.tan_arccos Real.tan_arccos

/- warning: real.arccos_eq_arcsin -> Real.arccos_eq_arcsin is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.arccos x) (Real.arcsin (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.arccos x) (Real.arcsin (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align real.arccos_eq_arcsin Real.arccos_eq_arcsinₓ'. -/
-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
theorem arccos_eq_arcsin {x : ℝ} (h : 0 ≤ x) : arccos x = arcsin (sqrt (1 - x ^ 2)) :=
  (arcsin_eq_of_sin_eq (sin_arccos _)
      ⟨(Left.neg_nonpos_iff.2 (div_nonneg pi_pos.le (by norm_num))).trans (arccos_nonneg _),
        arccos_le_pi_div_two.2 h⟩).symm
#align real.arccos_eq_arcsin Real.arccos_eq_arcsin

/- warning: real.arcsin_eq_arccos -> Real.arcsin_eq_arccos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.arcsin x) (Real.arccos (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.arcsin x) (Real.arccos (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align real.arcsin_eq_arccos Real.arcsin_eq_arccosₓ'. -/
-- The junk values for `arcsin` and `sqrt` make this true even for `1 < x`.
theorem arcsin_eq_arccos {x : ℝ} (h : 0 ≤ x) : arcsin x = arccos (sqrt (1 - x ^ 2)) :=
  by
  rw [eq_comm, ← cos_arcsin]
  exact
    arccos_cos (arcsin_nonneg.2 h)
      ((arcsin_le_pi_div_two _).trans (div_le_self pi_pos.le one_le_two))
#align real.arcsin_eq_arccos Real.arcsin_eq_arccos

end Real

