/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.asymptotics.specific_asymptotics
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Order.Basic
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developped in `analysis.asymptotics.asymptotics`.
-/


open Filter Asymptotics

open Topology

section NormedField

/- warning: filter.is_bounded_under.is_o_sub_self_inv -> Filter.IsBoundedUnder.isLittleO_sub_self_inv is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_2 : Norm.{u2} E] {a : 𝕜} {f : 𝕜 -> E}, (Filter.IsBoundedUnder.{0, u1} Real 𝕜 (LE.le.{0} Real Real.hasLe) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) a (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.booleanAlgebra.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.hasSingleton.{u1} 𝕜) a))) (Function.comp.{succ u1, succ u2, 1} 𝕜 E Real (Norm.norm.{u2} E _inst_2) f)) -> (Asymptotics.IsLittleO.{u1, u2, u1} 𝕜 E 𝕜 _inst_2 (NormedField.toHasNorm.{u1} 𝕜 _inst_1) (nhdsWithin.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) a (HasCompl.compl.{u1} (Set.{u1} 𝕜) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} 𝕜) (Set.booleanAlgebra.{u1} 𝕜)) (Singleton.singleton.{u1, u1} 𝕜 (Set.{u1} 𝕜) (Set.hasSingleton.{u1} 𝕜) a))) f (fun (x : 𝕜) => Inv.inv.{u1} 𝕜 (DivInvMonoid.toHasInv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 _inst_1)))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))))) x a)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : NormedField.{u2} 𝕜] [_inst_2 : Norm.{u1} E] {a : 𝕜} {f : 𝕜 -> E}, (Filter.IsBoundedUnder.{0, u2} Real 𝕜 (fun (x._@.Mathlib.Analysis.Asymptotics.SpecificAsymptotics._hyg.26 : Real) (x._@.Mathlib.Analysis.Asymptotics.SpecificAsymptotics._hyg.28 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Analysis.Asymptotics.SpecificAsymptotics._hyg.26 x._@.Mathlib.Analysis.Asymptotics.SpecificAsymptotics._hyg.28) (nhdsWithin.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_1)))))) a (HasCompl.compl.{u2} (Set.{u2} 𝕜) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} 𝕜) (Set.instBooleanAlgebraSet.{u2} 𝕜)) (Singleton.singleton.{u2, u2} 𝕜 (Set.{u2} 𝕜) (Set.instSingletonSet.{u2} 𝕜) a))) (Function.comp.{succ u2, succ u1, 1} 𝕜 E Real (Norm.norm.{u1} E _inst_2) f)) -> (Asymptotics.IsLittleO.{u2, u1, u2} 𝕜 E 𝕜 _inst_2 (NormedField.toNorm.{u2} 𝕜 _inst_1) (nhdsWithin.{u2} 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_1)))))) a (HasCompl.compl.{u2} (Set.{u2} 𝕜) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} 𝕜) (Set.instBooleanAlgebraSet.{u2} 𝕜)) (Singleton.singleton.{u2, u2} 𝕜 (Set.{u2} 𝕜) (Set.instSingletonSet.{u2} 𝕜) a))) f (fun (x : 𝕜) => Inv.inv.{u2} 𝕜 (Field.toInv.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 _inst_1)) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 _inst_1))))) x a)))
Case conversion may be inaccurate. Consider using '#align filter.is_bounded_under.is_o_sub_self_inv Filter.IsBoundedUnder.isLittleO_sub_self_invₓ'. -/
/-- If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)⁻¹)` as
`x → a`, `x ≠ a`. -/
theorem Filter.IsBoundedUnder.isLittleO_sub_self_inv {𝕜 E : Type _} [NormedField 𝕜] [Norm E] {a : 𝕜}
    {f : 𝕜 → E} (h : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (norm ∘ f)) :
    f =o[𝓝[≠] a] fun x => (x - a)⁻¹ :=
  by
  refine' (h.is_O_const (one_ne_zero' ℝ)).trans_isLittleO (is_o_const_left.2 <| Or.inr _)
  simp only [(· ∘ ·), norm_inv]
  exact (tendsto_norm_sub_self_punctured_nhds a).inv_tendsto_zero
#align filter.is_bounded_under.is_o_sub_self_inv Filter.IsBoundedUnder.isLittleO_sub_self_inv

end NormedField

section LinearOrderedField

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

/- warning: pow_div_pow_eventually_eq_at_top -> pow_div_pow_eventuallyEq_atTop is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {p : Nat} {q : Nat}, Filter.EventuallyEq.{u1, u1} 𝕜 𝕜 (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x q)) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) x (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) q)))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {p : Nat} {q : Nat}, Filter.EventuallyEq.{u1, u1} 𝕜 𝕜 (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x q)) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) x (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (Nat.cast.{0} Int instNatCastInt p) (Nat.cast.{0} Int instNatCastInt q)))
Case conversion may be inaccurate. Consider using '#align pow_div_pow_eventually_eq_at_top pow_div_pow_eventuallyEq_atTopₓ'. -/
theorem pow_div_pow_eventuallyEq_atTop {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ ((p : ℤ) - q) :=
  by
  apply (eventually_gt_at_top (0 : 𝕜)).mono fun x hx => _
  simp [zpow_sub₀ hx.ne']
#align pow_div_pow_eventually_eq_at_top pow_div_pow_eventuallyEq_atTop

/- warning: pow_div_pow_eventually_eq_at_bot -> pow_div_pow_eventuallyEq_atBot is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {p : Nat} {q : Nat}, Filter.EventuallyEq.{u1, u1} 𝕜 𝕜 (Filter.atBot.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x q)) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) x (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) p) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) q)))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {p : Nat} {q : Nat}, Filter.EventuallyEq.{u1, u1} 𝕜 𝕜 (Filter.atBot.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x q)) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Int 𝕜 (instHPow.{u1, 0} 𝕜 Int (DivInvMonoid.Pow.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) x (HSub.hSub.{0, 0, 0} Int Int Int (instHSub.{0} Int Int.instSubInt) (Nat.cast.{0} Int instNatCastInt p) (Nat.cast.{0} Int instNatCastInt q)))
Case conversion may be inaccurate. Consider using '#align pow_div_pow_eventually_eq_at_bot pow_div_pow_eventuallyEq_atBotₓ'. -/
theorem pow_div_pow_eventuallyEq_atBot {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atBot] fun x => x ^ ((p : ℤ) - q) :=
  by
  apply (eventually_lt_at_bot (0 : 𝕜)).mono fun x hx => _
  simp [zpow_sub₀ hx.ne]
#align pow_div_pow_eventually_eq_at_bot pow_div_pow_eventuallyEq_atBot

#print tendsto_zpow_atTop_atTop /-
theorem tendsto_zpow_atTop_atTop {n : ℤ} (hn : 0 < n) : Tendsto (fun x : 𝕜 => x ^ n) atTop atTop :=
  by
  lift n to ℕ using hn.le
  simp only [zpow_ofNat]
  exact tendsto_pow_at_top (nat.cast_pos.mp hn).ne'
#align tendsto_zpow_at_top_at_top tendsto_zpow_atTop_atTop
-/

/- warning: tendsto_pow_div_pow_at_top_at_top -> tendsto_pow_div_pow_atTop_atTop is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {p : Nat} {q : Nat}, (LT.lt.{0} Nat Nat.hasLt q p) -> (Filter.Tendsto.{u1, u1} 𝕜 𝕜 (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x q)) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {p : Nat} {q : Nat}, (LT.lt.{0} Nat instLTNat q p) -> (Filter.Tendsto.{u1, u1} 𝕜 𝕜 (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x q)) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_div_pow_at_top_at_top tendsto_pow_div_pow_atTop_atTopₓ'. -/
theorem tendsto_pow_div_pow_atTop_atTop {p q : ℕ} (hpq : q < p) :
    Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop atTop :=
  by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_atTop
  linarith
#align tendsto_pow_div_pow_at_top_at_top tendsto_pow_div_pow_atTop_atTop

/- warning: tendsto_pow_div_pow_at_top_zero -> tendsto_pow_div_pow_atTop_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : TopologicalSpace.{u1} 𝕜] [_inst_3 : OrderTopology.{u1} 𝕜 _inst_2 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))] {p : Nat} {q : Nat}, (LT.lt.{0} Nat Nat.hasLt p q) -> (Filter.Tendsto.{u1, u1} 𝕜 𝕜 (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))) x q)) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (nhds.{u1} 𝕜 _inst_2 (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : TopologicalSpace.{u1} 𝕜] [_inst_3 : OrderTopology.{u1} 𝕜 _inst_2 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))] {p : Nat} {q : Nat}, (LT.lt.{0} Nat instLTNat p q) -> (Filter.Tendsto.{u1, u1} 𝕜 𝕜 (fun (x : 𝕜) => HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (LinearOrderedField.toDiv.{u1} 𝕜 _inst_1)) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x p) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))))) x q)) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (nhds.{u1} 𝕜 _inst_2 (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align tendsto_pow_div_pow_at_top_zero tendsto_pow_div_pow_atTop_zeroₓ'. -/
theorem tendsto_pow_div_pow_atTop_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ}
    (hpq : p < q) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0) :=
  by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_zero
  linarith
#align tendsto_pow_div_pow_at_top_zero tendsto_pow_div_pow_atTop_zero

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type _} [NormedLinearOrderedField 𝕜]

/- warning: asymptotics.is_o_pow_pow_at_top_of_lt -> Asymptotics.isLittleO_pow_pow_atTop_of_lt is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedLinearOrderedField.{u1} 𝕜] [_inst_2 : OrderTopology.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toNormedField.{u1} 𝕜 _inst_1))))))) (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toLinearOrderedField.{u1} 𝕜 _inst_1)))))))] {p : Nat} {q : Nat}, (LT.lt.{0} Nat Nat.hasLt p q) -> (Asymptotics.IsLittleO.{u1, u1, u1} 𝕜 𝕜 𝕜 (NormedLinearOrderedField.toHasNorm.{u1} 𝕜 _inst_1) (NormedLinearOrderedField.toHasNorm.{u1} 𝕜 _inst_1) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toLinearOrderedField.{u1} 𝕜 _inst_1)))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toNormedField.{u1} 𝕜 _inst_1))))))) x p) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toNormedField.{u1} 𝕜 _inst_1))))))) x q))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NormedLinearOrderedField.{u1} 𝕜] [_inst_2 : OrderTopology.{u1} 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toNormedField.{u1} 𝕜 _inst_1))))))) (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toLinearOrderedField.{u1} 𝕜 _inst_1))))))] {p : Nat} {q : Nat}, (LT.lt.{0} Nat instLTNat p q) -> (Asymptotics.IsLittleO.{u1, u1, u1} 𝕜 𝕜 𝕜 (NormedLinearOrderedField.toNorm.{u1} 𝕜 _inst_1) (NormedLinearOrderedField.toNorm.{u1} 𝕜 _inst_1) (Filter.atTop.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 (NormedLinearOrderedField.toLinearOrderedField.{u1} 𝕜 _inst_1))))))) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 (NormedLinearOrderedField.toLinearOrderedField.{u1} 𝕜 _inst_1)))))))))) x p) (fun (x : 𝕜) => HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (MonoidWithZero.toMonoid.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (StrictOrderedSemiring.toSemiring.{u1} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 (NormedLinearOrderedField.toLinearOrderedField.{u1} 𝕜 _inst_1)))))))))) x q))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_pow_pow_at_top_of_lt Asymptotics.isLittleO_pow_pow_atTop_of_ltₓ'. -/
theorem Asymptotics.isLittleO_pow_pow_atTop_of_lt [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    (fun x : 𝕜 => x ^ p) =o[atTop] fun x => x ^ q :=
  by
  refine' (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_at_top 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim
#align asymptotics.is_o_pow_pow_at_top_of_lt Asymptotics.isLittleO_pow_pow_atTop_of_lt

#print Asymptotics.IsBigO.trans_tendsto_norm_atTop /-
theorem Asymptotics.IsBigO.trans_tendsto_norm_atTop {α : Type _} {u v : α → 𝕜} {l : Filter α}
    (huv : u =O[l] v) (hu : Tendsto (fun x => ‖u x‖) l atTop) : Tendsto (fun x => ‖v x‖) l atTop :=
  by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [is_O_with] at hcuv
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu)
  ext x
  rw [mul_div_cancel_left _ hc.ne.symm]
#align asymptotics.is_O.trans_tendsto_norm_at_top Asymptotics.IsBigO.trans_tendsto_norm_atTop
-/

end NormedLinearOrderedField

section Real

open BigOperators

open Finset

/- warning: asymptotics.is_o.sum_range -> Asymptotics.IsLittleO.sum_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} α] {f : Nat -> α} {g : Nat -> Real}, (Asymptotics.IsLittleO.{0, u1, 0} Nat α Real (NormedAddCommGroup.toHasNorm.{u1} α _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f g) -> (LE.le.{0} (Nat -> Real) (Pi.hasLe.{0, 0} Nat (fun (ᾰ : Nat) => Real) (fun (i : Nat) => Real.hasLe)) (OfNat.ofNat.{0} (Nat -> Real) 0 (OfNat.mk.{0} (Nat -> Real) 0 (Zero.zero.{0} (Nat -> Real) (Pi.instZero.{0, 0} Nat (fun (ᾰ : Nat) => Real) (fun (i : Nat) => Real.hasZero))))) g) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => g i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (Filter.atTop.{0} Real Real.preorder)) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat α Real (NormedAddCommGroup.toHasNorm.{u1} α _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (i : Nat) => f i)) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => g i)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} α] {f : Nat -> α} {g : Nat -> Real}, (Asymptotics.IsLittleO.{0, u1, 0} Nat α Real (NormedAddCommGroup.toNorm.{u1} α _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f g) -> (LE.le.{0} (Nat -> Real) (Pi.hasLe.{0, 0} Nat (fun (ᾰ : Nat) => Real) (fun (i : Nat) => Real.instLEReal)) (OfNat.ofNat.{0} (Nat -> Real) 0 (Zero.toOfNat0.{0} (Nat -> Real) (Pi.instZero.{0, 0} Nat (fun (a._@.Mathlib.Analysis.Asymptotics.SpecificAsymptotics._hyg.838 : Nat) => Real) (fun (i : Nat) => Real.instZeroReal)))) g) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => g i)) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (Filter.atTop.{0} Real Real.instPreorderReal)) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat α Real (NormedAddCommGroup.toNorm.{u1} α _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (i : Nat) => f i)) (fun (n : Nat) => Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => g i)))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o.sum_range Asymptotics.IsLittleO.sum_rangeₓ'. -/
theorem Asymptotics.IsLittleO.sum_range {α : Type _} [NormedAddCommGroup α] {f : ℕ → α} {g : ℕ → ℝ}
    (h : f =o[atTop] g) (hg : 0 ≤ g) (h'g : Tendsto (fun n => ∑ i in range n, g i) atTop atTop) :
    (fun n => ∑ i in range n, f i) =o[atTop] fun n => ∑ i in range n, g i :=
  by
  have A : ∀ i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : ∀ n, ‖∑ i in range n, g i‖ = ∑ i in range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply is_o_iff.2 fun ε εpos => _
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ‖f b‖ ≤ ε / 2 * g b := by
    simpa only [A, eventually_at_top] using is_o_iff.mp h (half_pos εpos)
  have : (fun n : ℕ => ∑ i in range N, f i) =o[at_top] fun n : ℕ => ∑ i in range n, g i :=
    by
    apply is_o_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [is_o_iff.1 this (half_pos εpos), Ici_mem_at_top N]with n hn Nn
  calc
    ‖∑ i in range n, f i‖ = ‖(∑ i in range N, f i) + ∑ i in Ico N n, f i‖ := by
      rw [sum_range_add_sum_Ico _ Nn]
    _ ≤ ‖∑ i in range N, f i‖ + ‖∑ i in Ico N n, f i‖ := (norm_add_le _ _)
    _ ≤ ‖∑ i in range N, f i‖ + ∑ i in Ico N n, ε / 2 * g i :=
      (add_le_add le_rfl (norm_sum_le_of_le _ fun i hi => hN _ (mem_Ico.1 hi).1))
    _ ≤ ‖∑ i in range N, f i‖ + ∑ i in range n, ε / 2 * g i :=
      by
      refine' add_le_add le_rfl _
      apply sum_le_sum_of_subset_of_nonneg
      · rw [range_eq_Ico]
        exact Ico_subset_Ico (zero_le _) le_rfl
      · intro i hi hident
        exact mul_nonneg (half_pos εpos).le (hg i)
    _ ≤ ε / 2 * ‖∑ i in range n, g i‖ + ε / 2 * ∑ i in range n, g i :=
      by
      rw [← mul_sum]
      exact add_le_add hn (mul_le_mul_of_nonneg_left le_rfl (half_pos εpos).le)
    _ = ε * ‖∑ i in range n, g i‖ := by
      simp [B]
      ring
    
#align asymptotics.is_o.sum_range Asymptotics.IsLittleO.sum_range

/- warning: asymptotics.is_o_sum_range_of_tendsto_zero -> Asymptotics.isLittleO_sum_range_of_tendsto_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} α] {f : Nat -> α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (AddZeroClass.toHasZero.{u1} α (AddMonoid.toAddZeroClass.{u1} α (SubNegMonoid.toAddMonoid.{u1} α (AddGroup.toSubNegMonoid.{u1} α (NormedAddGroup.toAddGroup.{u1} α (NormedAddCommGroup.toNormedAddGroup.{u1} α _inst_1))))))))))) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat α Real (NormedAddCommGroup.toHasNorm.{u1} α _inst_1) Real.hasNorm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (i : Nat) => f i)) (fun (n : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} α] {f : Nat -> α}, (Filter.Tendsto.{0, u1} Nat α f (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} α (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} α (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (NegZeroClass.toZero.{u1} α (SubNegZeroMonoid.toNegZeroClass.{u1} α (SubtractionMonoid.toSubNegZeroMonoid.{u1} α (SubtractionCommMonoid.toSubtractionMonoid.{u1} α (AddCommGroup.toDivisionAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)))))))))) -> (Asymptotics.IsLittleO.{0, u1, 0} Nat α Real (NormedAddCommGroup.toNorm.{u1} α _inst_1) Real.norm (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α _inst_1)) (Finset.range n) (fun (i : Nat) => f i)) (fun (n : Nat) => Nat.cast.{0} Real Real.natCast n))
Case conversion may be inaccurate. Consider using '#align asymptotics.is_o_sum_range_of_tendsto_zero Asymptotics.isLittleO_sum_range_of_tendsto_zeroₓ'. -/
theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type _} [NormedAddCommGroup α]
    {f : ℕ → α} (h : Tendsto f atTop (𝓝 0)) :
    (fun n => ∑ i in range n, f i) =o[atTop] fun n => (n : ℝ) :=
  by
  have := ((is_o_one_iff ℝ).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_coe] at this
  exact this tendsto_nat_cast_atTop_atTop
#align asymptotics.is_o_sum_range_of_tendsto_zero Asymptotics.isLittleO_sum_range_of_tendsto_zero

/- warning: filter.tendsto.cesaro_smul -> Filter.Tendsto.cesaro_smul is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] {u : Nat -> E} {l : E}, (Filter.Tendsto.{0, u1} Nat E u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) l)) -> (Filter.Tendsto.{0, u1} Nat E (fun (n : Nat) => SMul.smul.{0, u1} Real E (SMulZeroClass.toHasSmul.{0, u1} Real E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real E (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2))))) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) (Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => u i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) l))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] {u : Nat -> E} {l : E}, (Filter.Tendsto.{0, u1} Nat E u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) l)) -> (Filter.Tendsto.{0, u1} Nat E (fun (n : Nat) => HSMul.hSMul.{0, u1, u1} Real E E (instHSMul.{0, u1} Real E (SMulZeroClass.toSMul.{0, u1} Real E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real E Real.instZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)))))) (Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast n)) (Finset.sum.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (Finset.range n) (fun (i : Nat) => u i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) l))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.cesaro_smul Filter.Tendsto.cesaro_smulₓ'. -/
/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℕ → E}
    {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i in range n, u i) atTop (𝓝 l) :=
  by
  rw [← tendsto_sub_nhds_zero_iff, ← is_o_one_iff ℝ]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((is_O_refl (fun n : ℕ => (n : ℝ)⁻¹) at_top).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_at_top 1]with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj]
    rw [nsmul_eq_smul_cast ℝ, smul_smul, inv_mul_cancel nposℝ.ne', one_smul]
  · filter_upwards [Ici_mem_at_top 1]with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    rw [Algebra.id.smul_eq_mul, inv_mul_cancel nposℝ.ne']
#align filter.tendsto.cesaro_smul Filter.Tendsto.cesaro_smul

/- warning: filter.tendsto.cesaro -> Filter.Tendsto.cesaro is a dubious translation:
lean 3 declaration is
  forall {u : Nat -> Real} {l : Real}, (Filter.Tendsto.{0, 0} Nat Real u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) (Finset.sum.{0, 0} Real Nat Real.addCommMonoid (Finset.range n) (fun (i : Nat) => u i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l))
but is expected to have type
  forall {u : Nat -> Real} {l : Real}, (Filter.Tendsto.{0, 0} Nat Real u (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l)) -> (Filter.Tendsto.{0, 0} Nat Real (fun (n : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inv.inv.{0} Real Real.instInvReal (Nat.cast.{0} Real Real.natCast n)) (Finset.sum.{0, 0} Real Nat Real.instAddCommMonoidReal (Finset.range n) (fun (i : Nat) => u i))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) l))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.cesaro Filter.Tendsto.cesaroₓ'. -/
/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i in range n, u i) atTop (𝓝 l) :=
  h.cesaro_smul
#align filter.tendsto.cesaro Filter.Tendsto.cesaro

end Real

