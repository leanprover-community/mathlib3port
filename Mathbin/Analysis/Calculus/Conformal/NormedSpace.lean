/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang

! This file was ported from Lean 3 source module analysis.calculus.conformal.normed_space
! leanprover-community/mathlib commit e3fb84046afd187b710170887195d50bada934ee
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.ConformalLinearMap
import Mathbin.Analysis.Calculus.Fderiv.Add
import Mathbin.Analysis.Calculus.Fderiv.Mul
import Mathbin.Analysis.Calculus.Fderiv.Equiv
import Mathbin.Analysis.Calculus.Fderiv.RestrictScalars

/-!
# Conformal Maps

A continuous linear map between real normed spaces `X` and `Y` is `conformal_at` some point `x`
if it is real differentiable at that point and its differential `is_conformal_linear_map`.

## Main definitions

* `conformal_at`: the main definition of conformal maps
* `conformal`: maps that are conformal at every point
* `conformal_factor_at`: the conformal factor of a conformal map at some point

## Main results
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by nonzero constants
* `conformal_at_iff_is_conformal_map_fderiv`: an equivalent definition of the conformality of a map

In `analysis.calculus.conformal.inner_product`:
* `conformal_at_iff`: an equivalent definition of the conformality of a map

In `geometry.euclidean.angle.unoriented.conformal`:
* `conformal_at.preserves_angle`: if a map is conformal at `x`, then its differential
                                  preserves all angles at `x`

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the complex conjugate are considered to be conformal.
-/


noncomputable section

variable {X Y Z : Type _} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z]

section LocConformality

open LinearIsometry ContinuousLinearMap

#print ConformalAt /-
/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
def ConformalAt (f : X → Y) (x : X) :=
  ∃ f' : X →L[ℝ] Y, HasFDerivAt f f' x ∧ IsConformalMap f'
#align conformal_at ConformalAt
-/

#print conformalAt_id /-
theorem conformalAt_id (x : X) : ConformalAt id x :=
  ⟨id ℝ X, hasFDerivAt_id _, isConformalMap_id⟩
#align conformal_at_id conformalAt_id
-/

/- warning: conformal_at_const_smul -> conformalAt_const_smul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall (x : X), ConformalAt.{u1, u1} X X _inst_1 _inst_1 _inst_4 _inst_4 (fun (x' : X) => SMul.smul.{0, u1} Real X (SMulZeroClass.toHasSmul.{0, u1} Real X (AddZeroClass.toHasZero.{u1} X (AddMonoid.toAddZeroClass.{u1} X (AddCommMonoid.toAddMonoid.{u1} X (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real X (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} X (AddMonoid.toAddZeroClass.{u1} X (AddCommMonoid.toAddMonoid.{u1} X (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real X (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} X (AddMonoid.toAddZeroClass.{u1} X (AddCommMonoid.toAddMonoid.{u1} X (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real X (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1))) (NormedSpace.toModule.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1) _inst_4))))) c x') x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall (x : X), ConformalAt.{u1, u1} X X _inst_1 _inst_1 _inst_4 _inst_4 (fun (x' : X) => HSMul.hSMul.{0, u1, u1} Real X X (instHSMul.{0, u1} Real X (SMulZeroClass.toSMul.{0, u1} Real X (NegZeroClass.toZero.{u1} X (SubNegZeroMonoid.toNegZeroClass.{u1} X (SubtractionMonoid.toSubNegZeroMonoid.{u1} X (SubtractionCommMonoid.toSubtractionMonoid.{u1} X (AddCommGroup.toDivisionAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real X Real.instZeroReal (NegZeroClass.toZero.{u1} X (SubNegZeroMonoid.toNegZeroClass.{u1} X (SubtractionMonoid.toSubNegZeroMonoid.{u1} X (SubtractionCommMonoid.toSubtractionMonoid.{u1} X (AddCommGroup.toDivisionAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real X Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} X (SubNegZeroMonoid.toNegZeroClass.{u1} X (SubtractionMonoid.toSubNegZeroMonoid.{u1} X (SubtractionCommMonoid.toSubtractionMonoid.{u1} X (AddCommGroup.toDivisionAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real X Real.semiring (AddCommGroup.toAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)) (NormedSpace.toModule.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1) _inst_4)))))) c x') x)
Case conversion may be inaccurate. Consider using '#align conformal_at_const_smul conformalAt_const_smulₓ'. -/
theorem conformalAt_const_smul {c : ℝ} (h : c ≠ 0) (x : X) : ConformalAt (fun x' : X => c • x') x :=
  ⟨c • ContinuousLinearMap.id ℝ X, (hasFDerivAt_id x).const_smul c, isConformalMap_const_smul h⟩
#align conformal_at_const_smul conformalAt_const_smul

/- warning: subsingleton.conformal_at -> Subsingleton.conformalAt is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] [_inst_7 : Subsingleton.{succ u1} X] (f : X -> Y) (x : X), ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] [_inst_7 : Subsingleton.{succ u2} X] (f : X -> Y) (x : X), ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x
Case conversion may be inaccurate. Consider using '#align subsingleton.conformal_at Subsingleton.conformalAtₓ'. -/
@[nontriviality]
theorem Subsingleton.conformalAt [Subsingleton X] (f : X → Y) (x : X) : ConformalAt f x :=
  ⟨0, hasFDerivAt_of_subsingleton _ _, isConformalMap_of_subsingleton _⟩
#align subsingleton.conformal_at Subsingleton.conformalAt

/- warning: conformal_at_iff_is_conformal_map_fderiv -> conformalAt_iff_isConformalMap_fderiv is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y} {x : X}, Iff (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) (IsConformalMap.{0, u1, u2} Real X Y (NontriviallyNormedField.toNormedField.{0} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2) _inst_4 _inst_5 (fderiv.{0, u1, u2} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) X _inst_1 _inst_4 Y _inst_2 _inst_5 f x))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y} {x : X}, Iff (ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) (IsConformalMap.{0, u2, u1} Real X Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2) _inst_4 _inst_5 (fderiv.{0, u2, u1} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) X _inst_1 _inst_4 Y _inst_2 _inst_5 f x))
Case conversion may be inaccurate. Consider using '#align conformal_at_iff_is_conformal_map_fderiv conformalAt_iff_isConformalMap_fderivₓ'. -/
/-- A function is a conformal map if and only if its differential is a conformal linear map-/
theorem conformalAt_iff_isConformalMap_fderiv {f : X → Y} {x : X} :
    ConformalAt f x ↔ IsConformalMap (fderiv ℝ f x) :=
  by
  constructor
  · rintro ⟨f', hf, hf'⟩
    rwa [hf.fderiv]
  · intro H
    by_cases h : DifferentiableAt ℝ f x
    · exact ⟨fderiv ℝ f x, h.has_fderiv_at, H⟩
    · nontriviality X
      exact absurd (fderiv_zero_of_not_differentiableAt h) H.ne_zero
#align conformal_at_iff_is_conformal_map_fderiv conformalAt_iff_isConformalMap_fderiv

namespace ConformalAt

/- warning: conformal_at.differentiable_at -> ConformalAt.differentiableAt is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y} {x : X}, (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (DifferentiableAt.{0, u1, u2} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) X _inst_1 _inst_4 Y _inst_2 _inst_5 f x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y} {x : X}, (ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (DifferentiableAt.{0, u2, u1} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) X _inst_1 _inst_4 Y _inst_2 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align conformal_at.differentiable_at ConformalAt.differentiableAtₓ'. -/
theorem differentiableAt {f : X → Y} {x : X} (h : ConformalAt f x) : DifferentiableAt ℝ f x :=
  let ⟨_, h₁, _⟩ := h
  h₁.DifferentiableAt
#align conformal_at.differentiable_at ConformalAt.differentiableAt

/- warning: conformal_at.congr -> ConformalAt.congr is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y} {g : X -> Y} {x : X} {u : Set.{u1} X}, (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x u) -> (IsOpen.{u1} X (UniformSpace.toTopologicalSpace.{u1} X (PseudoMetricSpace.toUniformSpace.{u1} X (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))) u) -> (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (forall (x : X), (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x u) -> (Eq.{succ u2} Y (g x) (f x))) -> (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 g x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y} {g : X -> Y} {x : X} {u : Set.{u2} X}, (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x u) -> (IsOpen.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoMetricSpace.toUniformSpace.{u2} X (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)))) u) -> (ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (forall (x : X), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) x u) -> (Eq.{succ u1} Y (g x) (f x))) -> (ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 g x)
Case conversion may be inaccurate. Consider using '#align conformal_at.congr ConformalAt.congrₓ'. -/
theorem congr {f g : X → Y} {x : X} {u : Set X} (hx : x ∈ u) (hu : IsOpen u) (hf : ConformalAt f x)
    (h : ∀ x : X, x ∈ u → g x = f x) : ConformalAt g x :=
  let ⟨f', hfderiv, hf'⟩ := hf
  ⟨f', hfderiv.congr_of_eventuallyEq ((hu.eventually_mem hx).mono h), hf'⟩
#align conformal_at.congr ConformalAt.congr

/- warning: conformal_at.comp -> ConformalAt.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_3 : NormedAddCommGroup.{u3} Z] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] [_inst_6 : NormedSpace.{0, u3} Real Z Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} Z _inst_3)] {f : X -> Y} {g : Y -> Z} (x : X), (ConformalAt.{u2, u3} Y Z _inst_2 _inst_3 _inst_5 _inst_6 g (f x)) -> (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (ConformalAt.{u1, u3} X Z _inst_1 _inst_3 _inst_4 _inst_6 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f) x)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u3}} {Z : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u3} Y] [_inst_3 : NormedAddCommGroup.{u2} Z] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u3} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} Y _inst_2)] [_inst_6 : NormedSpace.{0, u2} Real Z Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Z _inst_3)] {f : X -> Y} {g : Y -> Z} (x : X), (ConformalAt.{u3, u2} Y Z _inst_2 _inst_3 _inst_5 _inst_6 g (f x)) -> (ConformalAt.{u1, u3} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (ConformalAt.{u1, u2} X Z _inst_1 _inst_3 _inst_4 _inst_6 (Function.comp.{succ u1, succ u3, succ u2} X Y Z g f) x)
Case conversion may be inaccurate. Consider using '#align conformal_at.comp ConformalAt.compₓ'. -/
theorem comp {f : X → Y} {g : Y → Z} (x : X) (hg : ConformalAt g (f x)) (hf : ConformalAt f x) :
    ConformalAt (g ∘ f) x := by
  rcases hf with ⟨f', hf₁, cf⟩
  rcases hg with ⟨g', hg₁, cg⟩
  exact ⟨g'.comp f', hg₁.comp x hf₁, cg.comp cf⟩
#align conformal_at.comp ConformalAt.comp

/- warning: conformal_at.const_smul -> ConformalAt.const_smul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y} {x : X} {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 (SMul.smul.{0, max u1 u2} Real (X -> Y) (Function.hasSMul.{u1, 0, u2} X Real Y (SMulZeroClass.toHasSmul.{0, u2} Real Y (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real Y (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real Y (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)))))) (Module.toMulActionWithZero.{0, u2} Real Y (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2))) (NormedSpace.toModule.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2) _inst_5)))))) c f) x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y} {x : X} {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x) -> (ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 (HSMul.hSMul.{0, max u2 u1, max u2 u1} Real (X -> Y) (X -> Y) (instHSMul.{0, max u2 u1} Real (X -> Y) (Pi.instSMul.{u2, u1, 0} X Real (fun (a._@.Mathlib.Analysis.Calculus.Conformal.NormedSpace._hyg.767 : X) => Y) (fun (i : X) => SMulZeroClass.toSMul.{0, u1} Real Y (NegZeroClass.toZero.{u1} Y (SubNegZeroMonoid.toNegZeroClass.{u1} Y (SubtractionMonoid.toSubNegZeroMonoid.{u1} Y (SubtractionCommMonoid.toSubtractionMonoid.{u1} Y (AddCommGroup.toDivisionAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real Y Real.instZeroReal (NegZeroClass.toZero.{u1} Y (SubNegZeroMonoid.toNegZeroClass.{u1} Y (SubtractionMonoid.toSubNegZeroMonoid.{u1} Y (SubtractionCommMonoid.toSubtractionMonoid.{u1} Y (AddCommGroup.toDivisionAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real Y Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} Y (SubNegZeroMonoid.toNegZeroClass.{u1} Y (SubtractionMonoid.toSubNegZeroMonoid.{u1} Y (SubtractionCommMonoid.toSubtractionMonoid.{u1} Y (AddCommGroup.toDivisionAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)))))) (Module.toMulActionWithZero.{0, u1} Real Y Real.semiring (AddCommGroup.toAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)) (NormedSpace.toModule.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2) _inst_5))))))) c f) x)
Case conversion may be inaccurate. Consider using '#align conformal_at.const_smul ConformalAt.const_smulₓ'. -/
theorem const_smul {f : X → Y} {x : X} {c : ℝ} (hc : c ≠ 0) (hf : ConformalAt f x) :
    ConformalAt (c • f) x :=
  (conformalAt_const_smul hc <| f x).comp x hf
#align conformal_at.const_smul ConformalAt.const_smul

end ConformalAt

end LocConformality

section GlobalConformality

#print Conformal /-
/-- A map `f` is conformal if it's conformal at every point. -/
def Conformal (f : X → Y) :=
  ∀ x : X, ConformalAt f x
#align conformal Conformal
-/

#print conformal_id /-
theorem conformal_id : Conformal (id : X → X) := fun x => conformalAt_id x
#align conformal_id conformal_id
-/

/- warning: conformal_const_smul -> conformal_const_smul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Conformal.{u1, u1} X X _inst_1 _inst_1 _inst_4 _inst_4 (fun (x : X) => SMul.smul.{0, u1} Real X (SMulZeroClass.toHasSmul.{0, u1} Real X (AddZeroClass.toHasZero.{u1} X (AddMonoid.toAddZeroClass.{u1} X (AddCommMonoid.toAddMonoid.{u1} X (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real X (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} X (AddMonoid.toAddZeroClass.{u1} X (AddCommMonoid.toAddMonoid.{u1} X (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real X (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} X (AddMonoid.toAddZeroClass.{u1} X (AddCommMonoid.toAddMonoid.{u1} X (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real X (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} X (SeminormedAddCommGroup.toAddCommGroup.{u1} X (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1))) (NormedSpace.toModule.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1) _inst_4))))) c x))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Conformal.{u1, u1} X X _inst_1 _inst_1 _inst_4 _inst_4 (fun (x : X) => HSMul.hSMul.{0, u1, u1} Real X X (instHSMul.{0, u1} Real X (SMulZeroClass.toSMul.{0, u1} Real X (NegZeroClass.toZero.{u1} X (SubNegZeroMonoid.toNegZeroClass.{u1} X (SubtractionMonoid.toSubNegZeroMonoid.{u1} X (SubtractionCommMonoid.toSubtractionMonoid.{u1} X (AddCommGroup.toDivisionAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real X Real.instZeroReal (NegZeroClass.toZero.{u1} X (SubNegZeroMonoid.toNegZeroClass.{u1} X (SubtractionMonoid.toSubNegZeroMonoid.{u1} X (SubtractionCommMonoid.toSubtractionMonoid.{u1} X (AddCommGroup.toDivisionAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real X Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} X (SubNegZeroMonoid.toNegZeroClass.{u1} X (SubtractionMonoid.toSubNegZeroMonoid.{u1} X (SubtractionCommMonoid.toSubtractionMonoid.{u1} X (AddCommGroup.toDivisionAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)))))) (Module.toMulActionWithZero.{0, u1} Real X Real.semiring (AddCommGroup.toAddCommMonoid.{u1} X (NormedAddCommGroup.toAddCommGroup.{u1} X _inst_1)) (NormedSpace.toModule.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1) _inst_4)))))) c x))
Case conversion may be inaccurate. Consider using '#align conformal_const_smul conformal_const_smulₓ'. -/
theorem conformal_const_smul {c : ℝ} (h : c ≠ 0) : Conformal fun x : X => c • x := fun x =>
  conformalAt_const_smul h x
#align conformal_const_smul conformal_const_smul

namespace Conformal

/- warning: conformal.conformal_at -> Conformal.conformalAt is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y}, (Conformal.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (forall (x : X), ConformalAt.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y}, (Conformal.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (forall (x : X), ConformalAt.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f x)
Case conversion may be inaccurate. Consider using '#align conformal.conformal_at Conformal.conformalAtₓ'. -/
theorem conformalAt {f : X → Y} (h : Conformal f) (x : X) : ConformalAt f x :=
  h x
#align conformal.conformal_at Conformal.conformalAt

/- warning: conformal.differentiable -> Conformal.differentiable is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y}, (Conformal.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (Differentiable.{0, u1, u2} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) X _inst_1 _inst_4 Y _inst_2 _inst_5 f)
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y}, (Conformal.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (Differentiable.{0, u2, u1} Real (DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) X _inst_1 _inst_4 Y _inst_2 _inst_5 f)
Case conversion may be inaccurate. Consider using '#align conformal.differentiable Conformal.differentiableₓ'. -/
theorem differentiable {f : X → Y} (h : Conformal f) : Differentiable ℝ f := fun x =>
  (h x).DifferentiableAt
#align conformal.differentiable Conformal.differentiable

/- warning: conformal.comp -> Conformal.comp is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} {Z : Type.{u3}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_3 : NormedAddCommGroup.{u3} Z] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] [_inst_6 : NormedSpace.{0, u3} Real Z Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} Z _inst_3)] {f : X -> Y} {g : Y -> Z}, (Conformal.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (Conformal.{u2, u3} Y Z _inst_2 _inst_3 _inst_5 _inst_6 g) -> (Conformal.{u1, u3} X Z _inst_1 _inst_3 _inst_4 _inst_6 (Function.comp.{succ u1, succ u2, succ u3} X Y Z g f))
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} {Z : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u3} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_3 : NormedAddCommGroup.{u1} Z] [_inst_4 : NormedSpace.{0, u3} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] [_inst_6 : NormedSpace.{0, u1} Real Z Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Z _inst_3)] {f : X -> Y} {g : Y -> Z}, (Conformal.{u3, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (Conformal.{u2, u1} Y Z _inst_2 _inst_3 _inst_5 _inst_6 g) -> (Conformal.{u3, u1} X Z _inst_1 _inst_3 _inst_4 _inst_6 (Function.comp.{succ u3, succ u2, succ u1} X Y Z g f))
Case conversion may be inaccurate. Consider using '#align conformal.comp Conformal.compₓ'. -/
theorem comp {f : X → Y} {g : Y → Z} (hf : Conformal f) (hg : Conformal g) : Conformal (g ∘ f) :=
  fun x => (hg <| f x).comp x (hf x)
#align conformal.comp Conformal.comp

/- warning: conformal.const_smul -> Conformal.const_smul is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} X] [_inst_2 : NormedAddCommGroup.{u2} Y] [_inst_4 : NormedSpace.{0, u1} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} X _inst_1)] [_inst_5 : NormedSpace.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)] {f : X -> Y}, (Conformal.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (forall {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Conformal.{u1, u2} X Y _inst_1 _inst_2 _inst_4 _inst_5 (SMul.smul.{0, max u1 u2} Real (X -> Y) (Function.hasSMul.{u1, 0, u2} X Real Y (SMulZeroClass.toHasSmul.{0, u2} Real Y (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real Y (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real Y (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} Y (AddMonoid.toAddZeroClass.{u2} Y (AddCommMonoid.toAddMonoid.{u2} Y (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2)))))) (Module.toMulActionWithZero.{0, u2} Real Y (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} Y (SeminormedAddCommGroup.toAddCommGroup.{u2} Y (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2))) (NormedSpace.toModule.{0, u2} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} Y _inst_2) _inst_5)))))) c f)))
but is expected to have type
  forall {X : Type.{u2}} {Y : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} X] [_inst_2 : NormedAddCommGroup.{u1} Y] [_inst_4 : NormedSpace.{0, u2} Real X Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} X _inst_1)] [_inst_5 : NormedSpace.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2)] {f : X -> Y}, (Conformal.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 f) -> (forall {c : Real}, (Ne.{1} Real c (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Conformal.{u2, u1} X Y _inst_1 _inst_2 _inst_4 _inst_5 (HSMul.hSMul.{0, max u2 u1, max u2 u1} Real (X -> Y) (X -> Y) (instHSMul.{0, max u2 u1} Real (X -> Y) (Pi.instSMul.{u2, u1, 0} X Real (fun (a._@.Mathlib.Analysis.Calculus.Conformal.NormedSpace._hyg.1142 : X) => Y) (fun (i : X) => SMulZeroClass.toSMul.{0, u1} Real Y (NegZeroClass.toZero.{u1} Y (SubNegZeroMonoid.toNegZeroClass.{u1} Y (SubtractionMonoid.toSubNegZeroMonoid.{u1} Y (SubtractionCommMonoid.toSubtractionMonoid.{u1} Y (AddCommGroup.toDivisionAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real Y Real.instZeroReal (NegZeroClass.toZero.{u1} Y (SubNegZeroMonoid.toNegZeroClass.{u1} Y (SubtractionMonoid.toSubNegZeroMonoid.{u1} Y (SubtractionCommMonoid.toSubtractionMonoid.{u1} Y (AddCommGroup.toDivisionAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real Y Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} Y (SubNegZeroMonoid.toNegZeroClass.{u1} Y (SubtractionMonoid.toSubNegZeroMonoid.{u1} Y (SubtractionCommMonoid.toSubtractionMonoid.{u1} Y (AddCommGroup.toDivisionAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)))))) (Module.toMulActionWithZero.{0, u1} Real Y Real.semiring (AddCommGroup.toAddCommMonoid.{u1} Y (NormedAddCommGroup.toAddCommGroup.{u1} Y _inst_2)) (NormedSpace.toModule.{0, u1} Real Y Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} Y _inst_2) _inst_5))))))) c f)))
Case conversion may be inaccurate. Consider using '#align conformal.const_smul Conformal.const_smulₓ'. -/
theorem const_smul {f : X → Y} (hf : Conformal f) {c : ℝ} (hc : c ≠ 0) : Conformal (c • f) :=
  fun x => (hf x).const_smul hc
#align conformal.const_smul Conformal.const_smul

end Conformal

end GlobalConformality

