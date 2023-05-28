/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module analysis.convex.side
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Between
import Mathbin.Analysis.Convex.Normed
import Mathbin.Analysis.Normed.Group.AddTorsor

/-!
# Sides of affine subspaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines notions of two points being on the same or opposite sides of an affine subspace.

## Main definitions

* `s.w_same_side x y`: The points `x` and `y` are weakly on the same side of the affine
  subspace `s`.
* `s.s_same_side x y`: The points `x` and `y` are strictly on the same side of the affine
  subspace `s`.
* `s.w_opp_side x y`: The points `x` and `y` are weakly on opposite sides of the affine
  subspace `s`.
* `s.s_opp_side x y`: The points `x` and `y` are strictly on opposite sides of the affine
  subspace `s`.

-/


variable {R V V' P P' : Type _}

open AffineEquiv AffineMap

namespace AffineSubspace

section StrictOrderedCommRing

variable [StrictOrderedCommRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

include V

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (p₁ p₂ «expr ∈ » s) -/
#print AffineSubspace.WSameSide /-
/-- The points `x` and `y` are weakly on the same side of `s`. -/
def WSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ (p₁ : _)(_ : p₁ ∈ s)(p₂ : _)(_ : p₂ ∈ s), SameRay R (x -ᵥ p₁) (y -ᵥ p₂)
#align affine_subspace.w_same_side AffineSubspace.WSameSide
-/

#print AffineSubspace.SSameSide /-
/-- The points `x` and `y` are strictly on the same side of `s`. -/
def SSameSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WSameSide x y ∧ x ∉ s ∧ y ∉ s
#align affine_subspace.s_same_side AffineSubspace.SSameSide
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (p₁ p₂ «expr ∈ » s) -/
#print AffineSubspace.WOppSide /-
/-- The points `x` and `y` are weakly on opposite sides of `s`. -/
def WOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  ∃ (p₁ : _)(_ : p₁ ∈ s)(p₂ : _)(_ : p₂ ∈ s), SameRay R (x -ᵥ p₁) (p₂ -ᵥ y)
#align affine_subspace.w_opp_side AffineSubspace.WOppSide
-/

#print AffineSubspace.SOppSide /-
/-- The points `x` and `y` are strictly on opposite sides of `s`. -/
def SOppSide (s : AffineSubspace R P) (x y : P) : Prop :=
  s.WOppSide x y ∧ x ∉ s ∧ y ∉ s
#align affine_subspace.s_opp_side AffineSubspace.SOppSide
-/

include V'

/- warning: affine_subspace.w_same_side.map -> AffineSubspace.WSameSide.map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.map AffineSubspace.WSameSide.mapₓ'. -/
theorem WSameSide.map {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WSameSide (f x) (f y) :=
  by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine' ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩
  simp_rw [← linear_map_vsub]
  exact h.map f.linear
#align affine_subspace.w_same_side.map AffineSubspace.WSameSide.map

/- warning: function.injective.w_same_side_map_iff -> Function.Injective.wSameSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align function.injective.w_same_side_map_iff Function.Injective.wSameSide_map_iffₓ'. -/
theorem Function.Injective.wSameSide_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  by
  refine' ⟨fun h => _, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine' ⟨p₁, hp₁, p₂, hp₂, _⟩
  simp_rw [← linear_map_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h
#align function.injective.w_same_side_map_iff Function.Injective.wSameSide_map_iff

/- warning: function.injective.s_same_side_map_iff -> Function.Injective.sSameSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align function.injective.s_same_side_map_iff Function.Injective.sSameSide_map_iffₓ'. -/
theorem Function.Injective.sSameSide_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).SSameSide (f x) (f y) ↔ s.SSameSide x y := by
  simp_rw [s_same_side, hf.w_same_side_map_iff, mem_map_iff_mem_of_injective hf]
#align function.injective.s_same_side_map_iff Function.Injective.sSameSide_map_iff

/- warning: affine_equiv.w_same_side_map_iff -> AffineEquiv.wSameSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.w_same_side_map_iff AffineEquiv.wSameSide_map_iffₓ'. -/
@[simp]
theorem AffineEquiv.wSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WSameSide (f x) (f y) ↔ s.WSameSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).wSameSide_map_iff
#align affine_equiv.w_same_side_map_iff AffineEquiv.wSameSide_map_iff

/- warning: affine_equiv.s_same_side_map_iff -> AffineEquiv.sSameSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.s_same_side_map_iff AffineEquiv.sSameSide_map_iffₓ'. -/
@[simp]
theorem AffineEquiv.sSameSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SSameSide (f x) (f y) ↔ s.SSameSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).sSameSide_map_iff
#align affine_equiv.s_same_side_map_iff AffineEquiv.sSameSide_map_iff

/- warning: affine_subspace.w_opp_side.map -> AffineSubspace.WOppSide.map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.map AffineSubspace.WOppSide.mapₓ'. -/
theorem WOppSide.map {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) (f : P →ᵃ[R] P') :
    (s.map f).WOppSide (f x) (f y) :=
  by
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h⟩
  refine' ⟨f p₁, mem_map_of_mem f hp₁, f p₂, mem_map_of_mem f hp₂, _⟩
  simp_rw [← linear_map_vsub]
  exact h.map f.linear
#align affine_subspace.w_opp_side.map AffineSubspace.WOppSide.map

/- warning: function.injective.w_opp_side_map_iff -> Function.Injective.wOppSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align function.injective.w_opp_side_map_iff Function.Injective.wOppSide_map_iffₓ'. -/
theorem Function.Injective.wOppSide_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  by
  refine' ⟨fun h => _, fun h => h.map _⟩
  rcases h with ⟨fp₁, hfp₁, fp₂, hfp₂, h⟩
  rw [mem_map] at hfp₁ hfp₂
  rcases hfp₁ with ⟨p₁, hp₁, rfl⟩
  rcases hfp₂ with ⟨p₂, hp₂, rfl⟩
  refine' ⟨p₁, hp₁, p₂, hp₂, _⟩
  simp_rw [← linear_map_vsub, (f.linear_injective_iff.2 hf).sameRay_map_iff] at h
  exact h
#align function.injective.w_opp_side_map_iff Function.Injective.wOppSide_map_iff

/- warning: function.injective.s_opp_side_map_iff -> Function.Injective.sOppSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align function.injective.s_opp_side_map_iff Function.Injective.sOppSide_map_iffₓ'. -/
theorem Function.Injective.sOppSide_map_iff {s : AffineSubspace R P} {x y : P} {f : P →ᵃ[R] P'}
    (hf : Function.Injective f) : (s.map f).SOppSide (f x) (f y) ↔ s.SOppSide x y := by
  simp_rw [s_opp_side, hf.w_opp_side_map_iff, mem_map_iff_mem_of_injective hf]
#align function.injective.s_opp_side_map_iff Function.Injective.sOppSide_map_iff

/- warning: affine_equiv.w_opp_side_map_iff -> AffineEquiv.wOppSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.w_opp_side_map_iff AffineEquiv.wOppSide_map_iffₓ'. -/
@[simp]
theorem AffineEquiv.wOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).WOppSide (f x) (f y) ↔ s.WOppSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).wOppSide_map_iff
#align affine_equiv.w_opp_side_map_iff AffineEquiv.wOppSide_map_iff

/- warning: affine_equiv.s_opp_side_map_iff -> AffineEquiv.sOppSide_map_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.s_opp_side_map_iff AffineEquiv.sOppSide_map_iffₓ'. -/
@[simp]
theorem AffineEquiv.sOppSide_map_iff {s : AffineSubspace R P} {x y : P} (f : P ≃ᵃ[R] P') :
    (s.map ↑f).SOppSide (f x) (f y) ↔ s.SOppSide x y :=
  (show Function.Injective f.toAffineMap from f.Injective).sOppSide_map_iff
#align affine_equiv.s_opp_side_map_iff AffineEquiv.sOppSide_map_iff

omit V'

/- warning: affine_subspace.w_same_side.nonempty -> AffineSubspace.WSameSide.nonempty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u3} P ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)))) s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.nonempty AffineSubspace.WSameSide.nonemptyₓ'. -/
theorem WSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.some, h.choose_spec.some⟩
#align affine_subspace.w_same_side.nonempty AffineSubspace.WSameSide.nonempty

/- warning: affine_subspace.s_same_side.nonempty -> AffineSubspace.SSameSide.nonempty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u3} P ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)))) s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.nonempty AffineSubspace.SSameSide.nonemptyₓ'. -/
theorem SSameSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.some, h.1.choose_spec.some⟩
#align affine_subspace.s_same_side.nonempty AffineSubspace.SSameSide.nonempty

/- warning: affine_subspace.w_opp_side.nonempty -> AffineSubspace.WOppSide.nonempty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u3} P ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)))) s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.nonempty AffineSubspace.WOppSide.nonemptyₓ'. -/
theorem WOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.some, h.choose_spec.some⟩
#align affine_subspace.w_opp_side.nonempty AffineSubspace.WOppSide.nonempty

/- warning: affine_subspace.s_opp_side.nonempty -> AffineSubspace.SOppSide.nonempty is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u3} P ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)))) s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.nonempty AffineSubspace.SOppSide.nonemptyₓ'. -/
theorem SOppSide.nonempty {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    (s : Set P).Nonempty :=
  ⟨h.1.some, h.1.choose_spec.some⟩
#align affine_subspace.s_opp_side.nonempty AffineSubspace.SOppSide.nonempty

/- warning: affine_subspace.s_same_side.w_same_side -> AffineSubspace.SSameSide.wSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.w_same_side AffineSubspace.SSameSide.wSameSideₓ'. -/
theorem SSameSide.wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    s.WSameSide x y :=
  h.1
#align affine_subspace.s_same_side.w_same_side AffineSubspace.SSameSide.wSameSide

/- warning: affine_subspace.s_same_side.left_not_mem -> AffineSubspace.SSameSide.left_not_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.left_not_mem AffineSubspace.SSameSide.left_not_memₓ'. -/
theorem SSameSide.left_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : x ∉ s :=
  h.2.1
#align affine_subspace.s_same_side.left_not_mem AffineSubspace.SSameSide.left_not_mem

/- warning: affine_subspace.s_same_side.right_not_mem -> AffineSubspace.SSameSide.right_not_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.right_not_mem AffineSubspace.SSameSide.right_not_memₓ'. -/
theorem SSameSide.right_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) : y ∉ s :=
  h.2.2
#align affine_subspace.s_same_side.right_not_mem AffineSubspace.SSameSide.right_not_mem

/- warning: affine_subspace.s_opp_side.w_opp_side -> AffineSubspace.SOppSide.wOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.w_opp_side AffineSubspace.SOppSide.wOppSideₓ'. -/
theorem SOppSide.wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    s.WOppSide x y :=
  h.1
#align affine_subspace.s_opp_side.w_opp_side AffineSubspace.SOppSide.wOppSide

/- warning: affine_subspace.s_opp_side.left_not_mem -> AffineSubspace.SOppSide.left_not_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.left_not_mem AffineSubspace.SOppSide.left_not_memₓ'. -/
theorem SOppSide.left_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : x ∉ s :=
  h.2.1
#align affine_subspace.s_opp_side.left_not_mem AffineSubspace.SOppSide.left_not_mem

/- warning: affine_subspace.s_opp_side.right_not_mem -> AffineSubspace.SOppSide.right_not_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.right_not_mem AffineSubspace.SOppSide.right_not_memₓ'. -/
theorem SOppSide.right_not_mem {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) : y ∉ s :=
  h.2.2
#align affine_subspace.s_opp_side.right_not_mem AffineSubspace.SOppSide.right_not_mem

/- warning: affine_subspace.w_same_side_comm -> AffineSubspace.wSameSide_comm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_comm AffineSubspace.wSameSide_commₓ'. -/
theorem wSameSide_comm {s : AffineSubspace R P} {x y : P} : s.WSameSide x y ↔ s.WSameSide y x :=
  ⟨fun ⟨p₁, hp₁, p₂, hp₂, h⟩ => ⟨p₂, hp₂, p₁, hp₁, h.symm⟩, fun ⟨p₁, hp₁, p₂, hp₂, h⟩ =>
    ⟨p₂, hp₂, p₁, hp₁, h.symm⟩⟩
#align affine_subspace.w_same_side_comm AffineSubspace.wSameSide_comm

/- warning: affine_subspace.w_same_side.symm -> AffineSubspace.WSameSide.symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.symm AffineSubspace.WSameSide.symmₓ'. -/
alias w_same_side_comm ↔ w_same_side.symm _
#align affine_subspace.w_same_side.symm AffineSubspace.WSameSide.symm

/- warning: affine_subspace.s_same_side_comm -> AffineSubspace.sSameSide_comm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_comm AffineSubspace.sSameSide_commₓ'. -/
theorem sSameSide_comm {s : AffineSubspace R P} {x y : P} : s.SSameSide x y ↔ s.SSameSide y x := by
  rw [s_same_side, s_same_side, w_same_side_comm, and_comm' (x ∉ s)]
#align affine_subspace.s_same_side_comm AffineSubspace.sSameSide_comm

/- warning: affine_subspace.s_same_side.symm -> AffineSubspace.SSameSide.symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.symm AffineSubspace.SSameSide.symmₓ'. -/
alias s_same_side_comm ↔ s_same_side.symm _
#align affine_subspace.s_same_side.symm AffineSubspace.SSameSide.symm

/- warning: affine_subspace.w_opp_side_comm -> AffineSubspace.wOppSide_comm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_comm AffineSubspace.wOppSide_commₓ'. -/
theorem wOppSide_comm {s : AffineSubspace R P} {x y : P} : s.WOppSide x y ↔ s.WOppSide y x :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
#align affine_subspace.w_opp_side_comm AffineSubspace.wOppSide_comm

/- warning: affine_subspace.w_opp_side.symm -> AffineSubspace.WOppSide.symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.symm AffineSubspace.WOppSide.symmₓ'. -/
alias w_opp_side_comm ↔ w_opp_side.symm _
#align affine_subspace.w_opp_side.symm AffineSubspace.WOppSide.symm

/- warning: affine_subspace.s_opp_side_comm -> AffineSubspace.sOppSide_comm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_comm AffineSubspace.sOppSide_commₓ'. -/
theorem sOppSide_comm {s : AffineSubspace R P} {x y : P} : s.SOppSide x y ↔ s.SOppSide y x := by
  rw [s_opp_side, s_opp_side, w_opp_side_comm, and_comm' (x ∉ s)]
#align affine_subspace.s_opp_side_comm AffineSubspace.sOppSide_comm

/- warning: affine_subspace.s_opp_side.symm -> AffineSubspace.SOppSide.symm is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.symm AffineSubspace.SOppSide.symmₓ'. -/
alias s_opp_side_comm ↔ s_opp_side.symm _
#align affine_subspace.s_opp_side.symm AffineSubspace.SOppSide.symm

/- warning: affine_subspace.not_w_same_side_bot -> AffineSubspace.not_wSameSide_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toHasBot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.completeLattice.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toBot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.instCompleteLatticeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.not_w_same_side_bot AffineSubspace.not_wSameSide_botₓ'. -/
theorem not_wSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WSameSide x y := by
  simp [w_same_side, not_mem_bot]
#align affine_subspace.not_w_same_side_bot AffineSubspace.not_wSameSide_bot

/- warning: affine_subspace.not_s_same_side_bot -> AffineSubspace.not_sSameSide_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toHasBot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.completeLattice.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toBot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.instCompleteLatticeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.not_s_same_side_bot AffineSubspace.not_sSameSide_botₓ'. -/
theorem not_sSameSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SSameSide x y := fun h =>
  not_wSameSide_bot x y h.WSameSide
#align affine_subspace.not_s_same_side_bot AffineSubspace.not_sSameSide_bot

/- warning: affine_subspace.not_w_opp_side_bot -> AffineSubspace.not_wOppSide_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toHasBot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.completeLattice.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toBot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.instCompleteLatticeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.not_w_opp_side_bot AffineSubspace.not_wOppSide_botₓ'. -/
theorem not_wOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).WOppSide x y := by
  simp [w_opp_side, not_mem_bot]
#align affine_subspace.not_w_opp_side_bot AffineSubspace.not_wOppSide_bot

/- warning: affine_subspace.not_s_opp_side_bot -> AffineSubspace.not_sOppSide_bot is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toHasBot.{u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.completeLattice.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (x : P) (y : P), Not (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 (Bot.bot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (CompleteLattice.toBot.{u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (AffineSubspace.instCompleteLatticeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4))) x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.not_s_opp_side_bot AffineSubspace.not_sOppSide_botₓ'. -/
theorem not_sOppSide_bot (x y : P) : ¬(⊥ : AffineSubspace R P).SOppSide x y := fun h =>
  not_wOppSide_bot x y h.WOppSide
#align affine_subspace.not_s_opp_side_bot AffineSubspace.not_sOppSide_bot

/- warning: affine_subspace.w_same_side_self_iff -> AffineSubspace.wSameSide_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P}, Iff (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x x) (Set.Nonempty.{u3} P ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)))) s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P}, Iff (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x x) (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_self_iff AffineSubspace.wSameSide_self_iffₓ'. -/
@[simp]
theorem wSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.WSameSide x x ↔ (s : Set P).Nonempty :=
  ⟨fun h => h.Nonempty, fun ⟨p, hp⟩ => ⟨p, hp, p, hp, SameRay.rfl⟩⟩
#align affine_subspace.w_same_side_self_iff AffineSubspace.wSameSide_self_iff

/- warning: affine_subspace.s_same_side_self_iff -> AffineSubspace.sSameSide_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P}, Iff (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x x) (And (Set.Nonempty.{u3} P ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (HasLiftT.mk.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (CoeTCₓ.coe.{succ u3, succ u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (Set.{u3} P) (SetLike.Set.hasCoeT.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)))) s)) (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s)))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P}, Iff (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x x) (And (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) s)) (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_self_iff AffineSubspace.sSameSide_self_iffₓ'. -/
theorem sSameSide_self_iff {s : AffineSubspace R P} {x : P} :
    s.SSameSide x x ↔ (s : Set P).Nonempty ∧ x ∉ s :=
  ⟨fun ⟨h, hx, _⟩ => ⟨wSameSide_self_iff.1 h, hx⟩, fun ⟨h, hx⟩ => ⟨wSameSide_self_iff.2 h, hx, hx⟩⟩
#align affine_subspace.s_same_side_self_iff AffineSubspace.sSameSide_self_iff

/- warning: affine_subspace.w_same_side_of_left_mem -> AffineSubspace.wSameSide_of_left_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} (y : P), (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} (y : P), (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_of_left_mem AffineSubspace.wSameSide_of_left_memₓ'. -/
theorem wSameSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WSameSide x y := by
  refine' ⟨x, hx, x, hx, _⟩
  simp
#align affine_subspace.w_same_side_of_left_mem AffineSubspace.wSameSide_of_left_mem

/- warning: affine_subspace.w_same_side_of_right_mem -> AffineSubspace.wSameSide_of_right_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} (x : P) {y : P}, (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} (x : P) {y : P}, (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_of_right_mem AffineSubspace.wSameSide_of_right_memₓ'. -/
theorem wSameSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WSameSide x y :=
  (wSameSide_of_left_mem x hy).symm
#align affine_subspace.w_same_side_of_right_mem AffineSubspace.wSameSide_of_right_mem

/- warning: affine_subspace.w_opp_side_of_left_mem -> AffineSubspace.wOppSide_of_left_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} (y : P), (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} (y : P), (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_of_left_mem AffineSubspace.wOppSide_of_left_memₓ'. -/
theorem wOppSide_of_left_mem {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide x y := by
  refine' ⟨x, hx, x, hx, _⟩
  simp
#align affine_subspace.w_opp_side_of_left_mem AffineSubspace.wOppSide_of_left_mem

/- warning: affine_subspace.w_opp_side_of_right_mem -> AffineSubspace.wOppSide_of_right_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} (x : P) {y : P}, (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} (x : P) {y : P}, (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_of_right_mem AffineSubspace.wOppSide_of_right_memₓ'. -/
theorem wOppSide_of_right_mem {s : AffineSubspace R P} (x : P) {y : P} (hy : y ∈ s) :
    s.WOppSide x y :=
  (wOppSide_of_left_mem x hy).symm
#align affine_subspace.w_opp_side_of_right_mem AffineSubspace.wOppSide_of_right_mem

/- warning: affine_subspace.w_same_side_vadd_left_iff -> AffineSubspace.wSameSide_vadd_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v x) y) (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v x) y) (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_vadd_left_iff AffineSubspace.wSameSide_vadd_left_iffₓ'. -/
theorem wSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WSameSide (v +ᵥ x) y ↔ s.WSameSide x y :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine'
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩
    rwa [vadd_vsub_vadd_cancel_left]
#align affine_subspace.w_same_side_vadd_left_iff AffineSubspace.wSameSide_vadd_left_iff

/- warning: affine_subspace.w_same_side_vadd_right_iff -> AffineSubspace.wSameSide_vadd_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v y)) (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v y)) (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_vadd_right_iff AffineSubspace.wSameSide_vadd_right_iffₓ'. -/
theorem wSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WSameSide x (v +ᵥ y) ↔ s.WSameSide x y := by
  rw [w_same_side_comm, w_same_side_vadd_left_iff hv, w_same_side_comm]
#align affine_subspace.w_same_side_vadd_right_iff AffineSubspace.wSameSide_vadd_right_iff

/- warning: affine_subspace.s_same_side_vadd_left_iff -> AffineSubspace.sSameSide_vadd_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v x) y) (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v x) y) (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_vadd_left_iff AffineSubspace.sSameSide_vadd_left_iffₓ'. -/
theorem sSameSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SSameSide (v +ᵥ x) y ↔ s.SSameSide x y := by
  rw [s_same_side, s_same_side, w_same_side_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
#align affine_subspace.s_same_side_vadd_left_iff AffineSubspace.sSameSide_vadd_left_iff

/- warning: affine_subspace.s_same_side_vadd_right_iff -> AffineSubspace.sSameSide_vadd_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v y)) (AffineSubspace.SSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v y)) (AffineSubspace.SSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_vadd_right_iff AffineSubspace.sSameSide_vadd_right_iffₓ'. -/
theorem sSameSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SSameSide x (v +ᵥ y) ↔ s.SSameSide x y := by
  rw [s_same_side_comm, s_same_side_vadd_left_iff hv, s_same_side_comm]
#align affine_subspace.s_same_side_vadd_right_iff AffineSubspace.sSameSide_vadd_right_iff

/- warning: affine_subspace.w_opp_side_vadd_left_iff -> AffineSubspace.wOppSide_vadd_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v x) y) (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v x) y) (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_vadd_left_iff AffineSubspace.wOppSide_vadd_left_iffₓ'. -/
theorem wOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide (v +ᵥ x) y ↔ s.WOppSide x y :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine'
      ⟨-v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ hv) hp₁, p₂, hp₂, _⟩
    rwa [vsub_vadd_eq_vsub_sub, sub_neg_eq_add, add_comm, ← vadd_vsub_assoc]
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    refine' ⟨v +ᵥ p₁, AffineSubspace.vadd_mem_of_mem_direction hv hp₁, p₂, hp₂, _⟩
    rwa [vadd_vsub_vadd_cancel_left]
#align affine_subspace.w_opp_side_vadd_left_iff AffineSubspace.wOppSide_vadd_left_iff

/- warning: affine_subspace.w_opp_side_vadd_right_iff -> AffineSubspace.wOppSide_vadd_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v y)) (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v y)) (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_vadd_right_iff AffineSubspace.wOppSide_vadd_right_iffₓ'. -/
theorem wOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.WOppSide x (v +ᵥ y) ↔ s.WOppSide x y := by
  rw [w_opp_side_comm, w_opp_side_vadd_left_iff hv, w_opp_side_comm]
#align affine_subspace.w_opp_side_vadd_right_iff AffineSubspace.wOppSide_vadd_right_iff

/- warning: affine_subspace.s_opp_side_vadd_left_iff -> AffineSubspace.sOppSide_vadd_left_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v x) y) (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v x) y) (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_vadd_left_iff AffineSubspace.sOppSide_vadd_left_iffₓ'. -/
theorem sOppSide_vadd_left_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide (v +ᵥ x) y ↔ s.SOppSide x y := by
  rw [s_opp_side, s_opp_side, w_opp_side_vadd_left_iff hv, vadd_mem_iff_mem_of_mem_direction hv]
#align affine_subspace.s_opp_side_vadd_left_iff AffineSubspace.sOppSide_vadd_left_iff

/- warning: affine_subspace.s_opp_side_vadd_right_iff -> AffineSubspace.sOppSide_vadd_right_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.Mem.{u2, u2} V (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (VAdd.vadd.{u2, u3} V P (AddAction.toHasVadd.{u2, u3} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4)) v y)) (AffineSubspace.SOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {v : V}, (Membership.mem.{u2, u2} V (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) (SetLike.instMembership.{u2, u2} (Submodule.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3) V (Submodule.setLike.{u3, u2} R V (Ring.toSemiring.{u3} R (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2) _inst_3)) v (AffineSubspace.direction.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s)) -> (Iff (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x (HVAdd.hVAdd.{u2, u1, u1} V P P (instHVAdd.{u2, u1} V P (AddAction.toVAdd.{u2, u1} V P (SubNegMonoid.toAddMonoid.{u2} V (AddGroup.toSubNegMonoid.{u2} V (AddCommGroup.toAddGroup.{u2} V _inst_2))) (AddTorsor.toAddAction.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2) _inst_4))) v y)) (AffineSubspace.SOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_vadd_right_iff AffineSubspace.sOppSide_vadd_right_iffₓ'. -/
theorem sOppSide_vadd_right_iff {s : AffineSubspace R P} {x y : P} {v : V} (hv : v ∈ s.direction) :
    s.SOppSide x (v +ᵥ y) ↔ s.SOppSide x y := by
  rw [s_opp_side_comm, s_opp_side_vadd_left_iff hv, s_opp_side_comm]
#align affine_subspace.s_opp_side_vadd_right_iff AffineSubspace.sOppSide_vadd_right_iff

/- warning: affine_subspace.w_same_side_smul_vsub_vadd_left -> AffineSubspace.wSameSide_smul_vsub_vadd_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_smul_vsub_vadd_left AffineSubspace.wSameSide_smul_vsub_vadd_leftₓ'. -/
theorem wSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
  rw [vadd_vsub]
  exact SameRay.sameRay_nonneg_smul_left _ ht
#align affine_subspace.w_same_side_smul_vsub_vadd_left AffineSubspace.wSameSide_smul_vsub_vadd_left

/- warning: affine_subspace.w_same_side_smul_vsub_vadd_right -> AffineSubspace.wSameSide_smul_vsub_vadd_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_smul_vsub_vadd_right AffineSubspace.wSameSide_smul_vsub_vadd_rightₓ'. -/
theorem wSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : 0 ≤ t) : s.WSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wSameSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm
#align affine_subspace.w_same_side_smul_vsub_vadd_right AffineSubspace.wSameSide_smul_vsub_vadd_right

/- warning: affine_subspace.w_same_side_line_map_left -> AffineSubspace.wSameSide_lineMap_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_line_map_left AffineSubspace.wSameSide_lineMap_leftₓ'. -/
theorem wSameSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide (lineMap x y t) y :=
  wSameSide_smul_vsub_vadd_left y h h ht
#align affine_subspace.w_same_side_line_map_left AffineSubspace.wSameSide_lineMap_left

/- warning: affine_subspace.w_same_side_line_map_right -> AffineSubspace.wSameSide_lineMap_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_line_map_right AffineSubspace.wSameSide_lineMap_rightₓ'. -/
theorem wSameSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : 0 ≤ t) : s.WSameSide y (lineMap x y t) :=
  (wSameSide_lineMap_left y h ht).symm
#align affine_subspace.w_same_side_line_map_right AffineSubspace.wSameSide_lineMap_right

/- warning: affine_subspace.w_opp_side_smul_vsub_vadd_left -> AffineSubspace.wOppSide_smul_vsub_vadd_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_smul_vsub_vadd_left AffineSubspace.wOppSide_smul_vsub_vadd_leftₓ'. -/
theorem wOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨p₂, hp₂, p₁, hp₁, _⟩
  rw [vadd_vsub, ← neg_neg t, neg_smul, ← smul_neg, neg_vsub_eq_vsub_rev]
  exact SameRay.sameRay_nonneg_smul_left _ (neg_nonneg.2 ht)
#align affine_subspace.w_opp_side_smul_vsub_vadd_left AffineSubspace.wOppSide_smul_vsub_vadd_left

/- warning: affine_subspace.w_opp_side_smul_vsub_vadd_right -> AffineSubspace.wOppSide_smul_vsub_vadd_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_smul_vsub_vadd_right AffineSubspace.wOppSide_smul_vsub_vadd_rightₓ'. -/
theorem wOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {p₁ p₂ : P} (x : P) (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) {t : R} (ht : t ≤ 0) : s.WOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (wOppSide_smul_vsub_vadd_left x hp₁ hp₂ ht).symm
#align affine_subspace.w_opp_side_smul_vsub_vadd_right AffineSubspace.wOppSide_smul_vsub_vadd_right

/- warning: affine_subspace.w_opp_side_line_map_left -> AffineSubspace.wOppSide_lineMap_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_line_map_left AffineSubspace.wOppSide_lineMap_leftₓ'. -/
theorem wOppSide_lineMap_left {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide (lineMap x y t) y :=
  wOppSide_smul_vsub_vadd_left y h h ht
#align affine_subspace.w_opp_side_line_map_left AffineSubspace.wOppSide_lineMap_left

/- warning: affine_subspace.w_opp_side_line_map_right -> AffineSubspace.wOppSide_lineMap_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_line_map_right AffineSubspace.wOppSide_lineMap_rightₓ'. -/
theorem wOppSide_lineMap_right {s : AffineSubspace R P} {x : P} (y : P) (h : x ∈ s) {t : R}
    (ht : t ≤ 0) : s.WOppSide y (lineMap x y t) :=
  (wOppSide_lineMap_left y h ht).symm
#align affine_subspace.w_opp_side_line_map_right AffineSubspace.wOppSide_lineMap_right

/- warning: wbtw.w_same_side₂₃ -> Wbtw.wSameSide₂₃ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y z)
Case conversion may be inaccurate. Consider using '#align wbtw.w_same_side₂₃ Wbtw.wSameSide₂₃ₓ'. -/
theorem Wbtw.wSameSide₂₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hx : x ∈ s) :
    s.WSameSide y z := by
  rcases h with ⟨t, ⟨ht0, -⟩, rfl⟩
  exact w_same_side_line_map_left z hx ht0
#align wbtw.w_same_side₂₃ Wbtw.wSameSide₂₃

/- warning: wbtw.w_same_side₃₂ -> Wbtw.wSameSide₃₂ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s z y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) x s) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s z y)
Case conversion may be inaccurate. Consider using '#align wbtw.w_same_side₃₂ Wbtw.wSameSide₃₂ₓ'. -/
theorem Wbtw.wSameSide₃₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hx : x ∈ s) :
    s.WSameSide z y :=
  (h.wSameSide₂₃ hx).symm
#align wbtw.w_same_side₃₂ Wbtw.wSameSide₃₂

/- warning: wbtw.w_same_side₁₂ -> Wbtw.wSameSide₁₂ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) z s) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) z s) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x y)
Case conversion may be inaccurate. Consider using '#align wbtw.w_same_side₁₂ Wbtw.wSameSide₁₂ₓ'. -/
theorem Wbtw.wSameSide₁₂ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hz : z ∈ s) :
    s.WSameSide x y :=
  h.symm.wSameSide₃₂ hz
#align wbtw.w_same_side₁₂ Wbtw.wSameSide₁₂

/- warning: wbtw.w_same_side₂₁ -> Wbtw.wSameSide₂₁ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) z s) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) z s) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s y x)
Case conversion may be inaccurate. Consider using '#align wbtw.w_same_side₂₁ Wbtw.wSameSide₂₁ₓ'. -/
theorem Wbtw.wSameSide₂₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hz : z ∈ s) :
    s.WSameSide y x :=
  h.symm.wSameSide₂₃ hz
#align wbtw.w_same_side₂₁ Wbtw.wSameSide₂₁

/- warning: wbtw.w_opp_side₁₃ -> Wbtw.wOppSide₁₃ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align wbtw.w_opp_side₁₃ Wbtw.wOppSide₁₃ₓ'. -/
theorem Wbtw.wOppSide₁₃ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hy : y ∈ s) :
    s.WOppSide x z := by
  rcases h with ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine' ⟨_, hy, _, hy, _⟩
  rcases ht1.lt_or_eq with (ht1' | rfl); swap; · simp
  rcases ht0.lt_or_eq with (ht0' | rfl); swap; · simp
  refine' Or.inr (Or.inr ⟨1 - t, t, sub_pos.2 ht1', ht0', _⟩)
  simp_rw [line_map_apply, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev z x,
    vsub_self, zero_sub, ← neg_one_smul R (z -ᵥ x), ← add_smul, smul_neg, ← neg_smul, smul_smul]
  ring_nf
#align wbtw.w_opp_side₁₃ Wbtw.wOppSide₁₃

/- warning: wbtw.w_opp_side₃₁ -> Wbtw.wOppSide₃₁ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : StrictOrderedCommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (StrictOrderedRing.toRing.{u1} R (StrictOrderedCommRing.toStrictOrderedRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P _inst_1 _inst_2 _inst_3 _inst_4 s z x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : StrictOrderedCommRing.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (StrictOrderedSemiring.toSemiring.{u3} R (StrictOrderedCommSemiring.toStrictOrderedSemiring.{u3} R (StrictOrderedCommRing.toStrictOrderedCommSemiring.{u3} R _inst_1))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 x y z) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (StrictOrderedRing.toRing.{u3} R (StrictOrderedCommRing.toStrictOrderedRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P _inst_1 _inst_2 _inst_3 _inst_4 s z x)
Case conversion may be inaccurate. Consider using '#align wbtw.w_opp_side₃₁ Wbtw.wOppSide₃₁ₓ'. -/
theorem Wbtw.wOppSide₃₁ {s : AffineSubspace R P} {x y z : P} (h : Wbtw R x y z) (hy : y ∈ s) :
    s.WOppSide z x :=
  h.symm.wOppSide₁₃ hy
#align wbtw.w_opp_side₃₁ Wbtw.wOppSide₃₁

end StrictOrderedCommRing

section LinearOrderedField

variable [LinearOrderedField R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

include V

variable {R}

/- warning: affine_subspace.w_opp_side_self_iff -> AffineSubspace.wOppSide_self_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P}, Iff (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x x) (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) x s)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P}, Iff (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x x) (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) x s)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_self_iff AffineSubspace.wOppSide_self_iffₓ'. -/
@[simp]
theorem wOppSide_self_iff {s : AffineSubspace R P} {x : P} : s.WOppSide x x ↔ x ∈ s :=
  by
  constructor
  · rintro ⟨p₁, hp₁, p₂, hp₂, h⟩
    obtain ⟨a, -, -, -, -, h₁, -⟩ := h.exists_eq_smul_add
    rw [add_comm, vsub_add_vsub_cancel, ← eq_vadd_iff_vsub_eq] at h₁
    rw [h₁]
    exact s.smul_vsub_vadd_mem a hp₂ hp₁ hp₁
  · exact fun h => ⟨x, h, x, h, SameRay.rfl⟩
#align affine_subspace.w_opp_side_self_iff AffineSubspace.wOppSide_self_iff

/- warning: affine_subspace.not_s_opp_side_self -> AffineSubspace.not_sOppSide_self is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (x : P), Not (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x x)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] (s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (x : P), Not (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x x)
Case conversion may be inaccurate. Consider using '#align affine_subspace.not_s_opp_side_self AffineSubspace.not_sOppSide_selfₓ'. -/
theorem not_sOppSide_self (s : AffineSubspace R P) (x : P) : ¬s.SOppSide x x := by simp [s_opp_side]
#align affine_subspace.not_s_opp_side_self AffineSubspace.not_sOppSide_self

/- warning: affine_subspace.w_same_side_iff_exists_left -> AffineSubspace.wSameSide_iff_exists_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_iff_exists_left AffineSubspace.wSameSide_iff_exists_leftₓ'. -/
theorem wSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WSameSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine' Or.inr ⟨p₂', hp₂', _⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine'
        Or.inr
          ⟨(r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
            Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩
      rw [vsub_vadd_eq_vsub_sub, smul_sub, ← hr, smul_smul, mul_div_cancel' _ hr₂.ne.symm, ←
        smul_sub, vsub_sub_vsub_cancel_right]
  · rintro (h' | h')
    · exact w_same_side_of_left_mem y h'
    · exact ⟨p₁, h, h'⟩
#align affine_subspace.w_same_side_iff_exists_left AffineSubspace.wSameSide_iff_exists_left

/- warning: affine_subspace.w_same_side_iff_exists_right -> AffineSubspace.wSameSide_iff_exists_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_iff_exists_right AffineSubspace.wSameSide_iff_exists_rightₓ'. -/
theorem wSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WSameSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  rw [w_same_side_comm, w_same_side_iff_exists_left h]
  simp_rw [SameRay.sameRay_comm]
#align affine_subspace.w_same_side_iff_exists_right AffineSubspace.wSameSide_iff_exists_right

/- warning: affine_subspace.s_same_side_iff_exists_left -> AffineSubspace.sSameSide_iff_exists_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_iff_exists_left AffineSubspace.sSameSide_iff_exists_leftₓ'. -/
theorem sSameSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  rw [s_same_side, and_comm', w_same_side_iff_exists_left h, and_assoc', and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]
#align affine_subspace.s_same_side_iff_exists_left AffineSubspace.sSameSide_iff_exists_left

/- warning: affine_subspace.s_same_side_iff_exists_right -> AffineSubspace.sSameSide_iff_exists_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_iff_exists_right AffineSubspace.sSameSide_iff_exists_rightₓ'. -/
theorem sSameSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SSameSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (y -ᵥ p₂) :=
  by
  rw [s_same_side_comm, s_same_side_iff_exists_left h, ← and_assoc', and_comm' (y ∉ s), and_assoc']
  simp_rw [SameRay.sameRay_comm]
#align affine_subspace.s_same_side_iff_exists_right AffineSubspace.sSameSide_iff_exists_right

/- warning: affine_subspace.w_opp_side_iff_exists_left -> AffineSubspace.wOppSide_iff_exists_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_iff_exists_left AffineSubspace.wOppSide_iff_exists_leftₓ'. -/
theorem wOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.WOppSide x y ↔ x ∈ s ∨ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  constructor
  · rintro ⟨p₁', hp₁', p₂', hp₂', h0 | h0 | ⟨r₁, r₂, hr₁, hr₂, hr⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h0
      rw [h0]
      exact Or.inl hp₁'
    · refine' Or.inr ⟨p₂', hp₂', _⟩
      rw [h0]
      exact SameRay.zero_right _
    · refine'
        Or.inr
          ⟨(-r₁ / r₂) • (p₁ -ᵥ p₁') +ᵥ p₂', s.smul_vsub_vadd_mem _ h hp₁' hp₂',
            Or.inr (Or.inr ⟨r₁, r₂, hr₁, hr₂, _⟩)⟩
      rw [vadd_vsub_assoc, smul_add, ← hr, smul_smul, neg_div, mul_neg,
        mul_div_cancel' _ hr₂.ne.symm, neg_smul, neg_add_eq_sub, ← smul_sub,
        vsub_sub_vsub_cancel_right]
  · rintro (h' | h')
    · exact w_opp_side_of_left_mem y h'
    · exact ⟨p₁, h, h'⟩
#align affine_subspace.w_opp_side_iff_exists_left AffineSubspace.wOppSide_iff_exists_left

/- warning: affine_subspace.w_opp_side_iff_exists_right -> AffineSubspace.wOppSide_iff_exists_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_iff_exists_right AffineSubspace.wOppSide_iff_exists_rightₓ'. -/
theorem wOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.WOppSide x y ↔ y ∈ s ∨ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  rw [w_opp_side_comm, w_opp_side_iff_exists_left h]
  constructor
  · rintro (hy | ⟨p, hp, hr⟩); · exact Or.inl hy
    refine' Or.inr ⟨p, hp, _⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
  · rintro (hy | ⟨p, hp, hr⟩); · exact Or.inl hy
    refine' Or.inr ⟨p, hp, _⟩
    rwa [SameRay.sameRay_comm, ← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev]
#align affine_subspace.w_opp_side_iff_exists_right AffineSubspace.wOppSide_iff_exists_right

/- warning: affine_subspace.s_opp_side_iff_exists_left -> AffineSubspace.sOppSide_iff_exists_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_iff_exists_left AffineSubspace.sOppSide_iff_exists_leftₓ'. -/
theorem sOppSide_iff_exists_left {s : AffineSubspace R P} {x y p₁ : P} (h : p₁ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₂ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  rw [s_opp_side, and_comm', w_opp_side_iff_exists_left h, and_assoc', and_congr_right_iff]
  intro hx
  rw [or_iff_right hx]
#align affine_subspace.s_opp_side_iff_exists_left AffineSubspace.sOppSide_iff_exists_left

/- warning: affine_subspace.s_opp_side_iff_exists_right -> AffineSubspace.sOppSide_iff_exists_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_iff_exists_right AffineSubspace.sOppSide_iff_exists_rightₓ'. -/
theorem sOppSide_iff_exists_right {s : AffineSubspace R P} {x y p₂ : P} (h : p₂ ∈ s) :
    s.SOppSide x y ↔ x ∉ s ∧ y ∉ s ∧ ∃ p₁ ∈ s, SameRay R (x -ᵥ p₁) (p₂ -ᵥ y) :=
  by
  rw [s_opp_side, and_comm', w_opp_side_iff_exists_right h, and_assoc', and_congr_right_iff,
    and_congr_right_iff]
  rintro hx hy
  rw [or_iff_right hy]
#align affine_subspace.s_opp_side_iff_exists_right AffineSubspace.sOppSide_iff_exists_right

/- warning: affine_subspace.w_same_side.trans -> AffineSubspace.WSameSide.trans is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.trans AffineSubspace.WSameSide.transₓ'. -/
theorem WSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WSameSide x z :=
  by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [w_same_side_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  refine' fun h => False.elim _
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)
#align affine_subspace.w_same_side.trans AffineSubspace.WSameSide.trans

/- warning: affine_subspace.w_same_side.trans_s_same_side -> AffineSubspace.WSameSide.trans_sSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.trans_s_same_side AffineSubspace.WSameSide.trans_sSameSideₓ'. -/
theorem WSameSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SSameSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
#align affine_subspace.w_same_side.trans_s_same_side AffineSubspace.WSameSide.trans_sSameSide

/- warning: affine_subspace.w_same_side.trans_w_opp_side -> AffineSubspace.WSameSide.trans_wOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.trans_w_opp_side AffineSubspace.WSameSide.trans_wOppSideₓ'. -/
theorem WSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [w_opp_side_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  refine' fun h => False.elim _
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h.symm ▸ hp₂)
#align affine_subspace.w_same_side.trans_w_opp_side AffineSubspace.WSameSide.trans_wOppSide

/- warning: affine_subspace.w_same_side.trans_s_opp_side -> AffineSubspace.WSameSide.trans_sOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.trans_s_opp_side AffineSubspace.WSameSide.trans_sOppSideₓ'. -/
theorem WSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WSameSide x y)
    (hyz : s.SOppSide y z) : s.WOppSide x z :=
  hxy.trans_wOppSide hyz.1 hyz.2.1
#align affine_subspace.w_same_side.trans_s_opp_side AffineSubspace.WSameSide.trans_sOppSide

/- warning: affine_subspace.s_same_side.trans_w_same_side -> AffineSubspace.SSameSide.trans_wSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.trans_w_same_side AffineSubspace.SSameSide.trans_wSameSideₓ'. -/
theorem SSameSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WSameSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sSameSide hxy.symm).symm
#align affine_subspace.s_same_side.trans_w_same_side AffineSubspace.SSameSide.trans_wSameSide

/- warning: affine_subspace.s_same_side.trans -> AffineSubspace.SSameSide.trans is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.trans AffineSubspace.SSameSide.transₓ'. -/
theorem SSameSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SSameSide y z) : s.SSameSide x z :=
  ⟨hxy.WSameSide.trans_sSameSide hyz, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_same_side.trans AffineSubspace.SSameSide.trans

/- warning: affine_subspace.s_same_side.trans_w_opp_side -> AffineSubspace.SSameSide.trans_wOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.trans_w_opp_side AffineSubspace.SSameSide.trans_wOppSideₓ'. -/
theorem SSameSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.WOppSide y z) : s.WOppSide x z :=
  hxy.WSameSide.trans_wOppSide hyz hxy.2.2
#align affine_subspace.s_same_side.trans_w_opp_side AffineSubspace.SSameSide.trans_wOppSide

/- warning: affine_subspace.s_same_side.trans_s_opp_side -> AffineSubspace.SSameSide.trans_sOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.trans_s_opp_side AffineSubspace.SSameSide.trans_sOppSideₓ'. -/
theorem SSameSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SSameSide x y)
    (hyz : s.SOppSide y z) : s.SOppSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_same_side.trans_s_opp_side AffineSubspace.SSameSide.trans_sOppSide

/- warning: affine_subspace.w_opp_side.trans_w_same_side -> AffineSubspace.WOppSide.trans_wSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.trans_w_same_side AffineSubspace.WOppSide.trans_wSameSideₓ'. -/
theorem WOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WSameSide y z) (hy : y ∉ s) : s.WOppSide x z :=
  (hyz.symm.trans_wOppSide hxy.symm hy).symm
#align affine_subspace.w_opp_side.trans_w_same_side AffineSubspace.WOppSide.trans_wSameSide

/- warning: affine_subspace.w_opp_side.trans_s_same_side -> AffineSubspace.WOppSide.trans_sSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.trans_s_same_side AffineSubspace.WOppSide.trans_sSameSideₓ'. -/
theorem WOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SSameSide y z) : s.WOppSide x z :=
  hxy.trans_wSameSide hyz.1 hyz.2.1
#align affine_subspace.w_opp_side.trans_s_same_side AffineSubspace.WOppSide.trans_sSameSide

/- warning: affine_subspace.w_opp_side.trans -> AffineSubspace.WOppSide.trans is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s)) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.trans AffineSubspace.WOppSide.transₓ'. -/
theorem WOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.WOppSide y z) (hy : y ∉ s) : s.WSameSide x z :=
  by
  rcases hxy with ⟨p₁, hp₁, p₂, hp₂, hxy⟩
  rw [w_opp_side_iff_exists_left hp₂, or_iff_right hy] at hyz
  rcases hyz with ⟨p₃, hp₃, hyz⟩
  rw [← sameRay_neg_iff, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hyz
  refine' ⟨p₁, hp₁, p₃, hp₃, hxy.trans hyz _⟩
  refine' fun h => False.elim _
  rw [vsub_eq_zero_iff_eq] at h
  exact hy (h ▸ hp₂)
#align affine_subspace.w_opp_side.trans AffineSubspace.WOppSide.trans

/- warning: affine_subspace.w_opp_side.trans_s_opp_side -> AffineSubspace.WOppSide.trans_sOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.trans_s_opp_side AffineSubspace.WOppSide.trans_sOppSideₓ'. -/
theorem WOppSide.trans_sOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.WOppSide x y)
    (hyz : s.SOppSide y z) : s.WSameSide x z :=
  hxy.trans hyz.1 hyz.2.1
#align affine_subspace.w_opp_side.trans_s_opp_side AffineSubspace.WOppSide.trans_sOppSide

/- warning: affine_subspace.s_opp_side.trans_w_same_side -> AffineSubspace.SOppSide.trans_wSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.trans_w_same_side AffineSubspace.SOppSide.trans_wSameSideₓ'. -/
theorem SOppSide.trans_wSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WSameSide y z) : s.WOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_w_same_side AffineSubspace.SOppSide.trans_wSameSide

/- warning: affine_subspace.s_opp_side.trans_s_same_side -> AffineSubspace.SOppSide.trans_sSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.trans_s_same_side AffineSubspace.SOppSide.trans_sSameSideₓ'. -/
theorem SOppSide.trans_sSameSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SSameSide y z) : s.SOppSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_s_same_side AffineSubspace.SOppSide.trans_sSameSide

/- warning: affine_subspace.s_opp_side.trans_w_opp_side -> AffineSubspace.SOppSide.trans_wOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.trans_w_opp_side AffineSubspace.SOppSide.trans_wOppSideₓ'. -/
theorem SOppSide.trans_wOppSide {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.WOppSide y z) : s.WSameSide x z :=
  (hyz.symm.trans_sOppSide hxy.symm).symm
#align affine_subspace.s_opp_side.trans_w_opp_side AffineSubspace.SOppSide.trans_wOppSide

/- warning: affine_subspace.s_opp_side.trans -> AffineSubspace.SOppSide.trans is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s y z) -> (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.trans AffineSubspace.SOppSide.transₓ'. -/
theorem SOppSide.trans {s : AffineSubspace R P} {x y z : P} (hxy : s.SOppSide x y)
    (hyz : s.SOppSide y z) : s.SSameSide x z :=
  ⟨hxy.trans_wOppSide hyz.1, hxy.2.1, hyz.2.2⟩
#align affine_subspace.s_opp_side.trans AffineSubspace.SOppSide.trans

/- warning: affine_subspace.w_same_side_and_w_opp_side_iff -> AffineSubspace.wSameSide_and_wOppSide_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (And (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y)) (Or (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) x s) (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (And (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y)) (Or (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) x s) (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side_and_w_opp_side_iff AffineSubspace.wSameSide_and_wOppSide_iffₓ'. -/
theorem wSameSide_and_wOppSide_iff {s : AffineSubspace R P} {x y : P} :
    s.WSameSide x y ∧ s.WOppSide x y ↔ x ∈ s ∨ y ∈ s :=
  by
  constructor
  · rintro ⟨hs, ho⟩
    rw [w_opp_side_comm] at ho
    by_contra h
    rw [not_or] at h
    exact h.1 (w_opp_side_self_iff.1 (hs.trans_w_opp_side ho h.2))
  · rintro (h | h)
    · exact ⟨w_same_side_of_left_mem y h, w_opp_side_of_left_mem y h⟩
    · exact ⟨w_same_side_of_right_mem x h, w_opp_side_of_right_mem x h⟩
#align affine_subspace.w_same_side_and_w_opp_side_iff AffineSubspace.wSameSide_and_wOppSide_iff

/- warning: affine_subspace.w_same_side.not_s_opp_side -> AffineSubspace.WSameSide.not_sOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_same_side.not_s_opp_side AffineSubspace.WSameSide.not_sOppSideₓ'. -/
theorem WSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.WSameSide x y) :
    ¬s.SOppSide x y := by
  intro ho
  have hxy := w_same_side_and_w_opp_side_iff.1 ⟨h, ho.1⟩
  rcases hxy with (hx | hy)
  · exact ho.2.1 hx
  · exact ho.2.2 hy
#align affine_subspace.w_same_side.not_s_opp_side AffineSubspace.WSameSide.not_sOppSide

/- warning: affine_subspace.s_same_side.not_w_opp_side -> AffineSubspace.SSameSide.not_wOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.not_w_opp_side AffineSubspace.SSameSide.not_wOppSideₓ'. -/
theorem SSameSide.not_wOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.WOppSide x y := by
  intro ho
  have hxy := w_same_side_and_w_opp_side_iff.1 ⟨h.1, ho⟩
  rcases hxy with (hx | hy)
  · exact h.2.1 hx
  · exact h.2.2 hy
#align affine_subspace.s_same_side.not_w_opp_side AffineSubspace.SSameSide.not_wOppSide

/- warning: affine_subspace.s_same_side.not_s_opp_side -> AffineSubspace.SSameSide.not_sOppSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side.not_s_opp_side AffineSubspace.SSameSide.not_sOppSideₓ'. -/
theorem SSameSide.not_sOppSide {s : AffineSubspace R P} {x y : P} (h : s.SSameSide x y) :
    ¬s.SOppSide x y := fun ho => h.not_wOppSide ho.1
#align affine_subspace.s_same_side.not_s_opp_side AffineSubspace.SSameSide.not_sOppSide

/- warning: affine_subspace.w_opp_side.not_s_same_side -> AffineSubspace.WOppSide.not_sSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side.not_s_same_side AffineSubspace.WOppSide.not_sSameSideₓ'. -/
theorem WOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.WOppSide x y) :
    ¬s.SSameSide x y := fun hs => hs.not_wOppSide h
#align affine_subspace.w_opp_side.not_s_same_side AffineSubspace.WOppSide.not_sSameSide

/- warning: affine_subspace.s_opp_side.not_w_same_side -> AffineSubspace.SOppSide.not_wSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.WSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.WSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.not_w_same_side AffineSubspace.SOppSide.not_wSameSideₓ'. -/
theorem SOppSide.not_wSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.WSameSide x y := fun hs => hs.not_sOppSide h
#align affine_subspace.s_opp_side.not_w_same_side AffineSubspace.SOppSide.not_wSameSide

/- warning: affine_subspace.s_opp_side.not_s_same_side -> AffineSubspace.SOppSide.not_sSameSide is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SSameSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Not (AffineSubspace.SSameSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.not_s_same_side AffineSubspace.SOppSide.not_sSameSideₓ'. -/
theorem SOppSide.not_sSameSide {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ¬s.SSameSide x y := fun hs => h.not_wSameSide hs.1
#align affine_subspace.s_opp_side.not_s_same_side AffineSubspace.SOppSide.not_sSameSide

/- warning: affine_subspace.w_opp_side_iff_exists_wbtw -> AffineSubspace.wOppSide_iff_exists_wbtw is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.WOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) (Exists.{succ u3} P (fun (p : P) => Exists.{0} (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) p s) (fun (H : Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) p s) => Wbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))) _inst_2 _inst_3 _inst_4 x p y)))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, Iff (AffineSubspace.WOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) (Exists.{succ u1} P (fun (p : P) => And (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) p s) (Wbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)))) _inst_2 _inst_3 _inst_4 x p y)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_iff_exists_wbtw AffineSubspace.wOppSide_iff_exists_wbtwₓ'. -/
theorem wOppSide_iff_exists_wbtw {s : AffineSubspace R P} {x y : P} :
    s.WOppSide x y ↔ ∃ p ∈ s, Wbtw R x p y :=
  by
  refine' ⟨fun h => _, fun ⟨p, hp, h⟩ => h.wOppSide₁₃ hp⟩
  rcases h with ⟨p₁, hp₁, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [h]
    exact ⟨p₁, hp₁, wbtw_self_left _ _ _⟩
  · rw [vsub_eq_zero_iff_eq] at h
    rw [← h]
    exact ⟨p₂, hp₂, wbtw_self_right _ _ _⟩
  · refine' ⟨line_map x y (r₂ / (r₁ + r₂)), _, _⟩
    · rw [line_map_apply, ← vsub_vadd x p₁, ← vsub_vadd y p₂, vsub_vadd_eq_vsub_sub,
        vadd_vsub_assoc, ← vadd_assoc, vadd_eq_add]
      convert s.smul_vsub_vadd_mem (r₂ / (r₁ + r₂)) hp₂ hp₁ hp₁
      rw [add_comm (y -ᵥ p₂), smul_sub, smul_add, add_sub_assoc, add_assoc, add_right_eq_self,
        div_eq_inv_mul, ← neg_vsub_eq_vsub_rev, smul_neg, ← smul_smul, ← h, smul_smul, ← neg_smul, ←
        sub_smul, ← div_eq_inv_mul, ← div_eq_inv_mul, ← neg_div, ← sub_div, sub_eq_add_neg, ←
        neg_add, neg_div, div_self (Left.add_pos hr₁ hr₂).Ne.symm, neg_one_smul, neg_add_self]
    ·
      exact
        Set.mem_image_of_mem _
          ⟨div_nonneg hr₂.le (Left.add_pos hr₁ hr₂).le,
            div_le_one_of_le (le_add_of_nonneg_left hr₁.le) (Left.add_pos hr₁ hr₂).le⟩
#align affine_subspace.w_opp_side_iff_exists_wbtw AffineSubspace.wOppSide_iff_exists_wbtw

/- warning: affine_subspace.s_opp_side.exists_sbtw -> AffineSubspace.SOppSide.exists_sbtw is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Exists.{succ u3} P (fun (p : P) => Exists.{0} (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) p s) (fun (H : Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) p s) => Sbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))) _inst_2 _inst_3 _inst_4 x p y)))
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P}, (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x y) -> (Exists.{succ u1} P (fun (p : P) => And (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) p s) (Sbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)))) _inst_2 _inst_3 _inst_4 x p y)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side.exists_sbtw AffineSubspace.SOppSide.exists_sbtwₓ'. -/
theorem SOppSide.exists_sbtw {s : AffineSubspace R P} {x y : P} (h : s.SOppSide x y) :
    ∃ p ∈ s, Sbtw R x p y :=
  by
  obtain ⟨p, hp, hw⟩ := w_opp_side_iff_exists_wbtw.1 h.w_opp_side
  refine' ⟨p, hp, hw, _, _⟩
  · rintro rfl
    exact h.2.1 hp
  · rintro rfl
    exact h.2.2 hp
#align affine_subspace.s_opp_side.exists_sbtw AffineSubspace.SOppSide.exists_sbtw

/- warning: sbtw.s_opp_side_of_not_mem_of_mem -> Sbtw.sOppSide_of_not_mem_of_mem is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {V : Type.{u2}} {P : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u1, u2} R V (Ring.toSemiring.{u1} R (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u3} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Sbtw.{u1, u2, u3} R V P (StrictOrderedRing.toOrderedRing.{u1} R (LinearOrderedRing.toStrictOrderedRing.{u1} R (LinearOrderedCommRing.toLinearOrderedRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)))) _inst_2 _inst_3 _inst_4 x y z) -> (Not (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) x s)) -> (Membership.Mem.{u3, u3} P (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.hasMem.{u3, u3} (AffineSubspace.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.setLike.{u1, u2, u3} R V P (DivisionRing.toRing.{u1} R (Field.toDivisionRing.{u1} R (LinearOrderedField.toField.{u1} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.SOppSide.{u1, u2, u3} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u1} R (LinearOrderedField.toLinearOrderedCommRing.{u1} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
but is expected to have type
  forall {R : Type.{u3}} {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} R] [_inst_2 : AddCommGroup.{u2} V] [_inst_3 : Module.{u3, u2} R V (DivisionSemiring.toSemiring.{u3} R (Semifield.toDivisionSemiring.{u3} R (LinearOrderedSemifield.toSemifield.{u3} R (LinearOrderedField.toLinearOrderedSemifield.{u3} R _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} V _inst_2)] [_inst_4 : AddTorsor.{u2, u1} V P (AddCommGroup.toAddGroup.{u2} V _inst_2)] {s : AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4} {x : P} {y : P} {z : P}, (Sbtw.{u3, u2, u1} R V P (OrderedCommRing.toOrderedRing.{u3} R (StrictOrderedCommRing.toOrderedCommRing.{u3} R (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)))) _inst_2 _inst_3 _inst_4 x y z) -> (Not (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) x s)) -> (Membership.mem.{u1, u1} P (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) (SetLike.instMembership.{u1, u1} (AffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4) P (AffineSubspace.instSetLikeAffineSubspace.{u3, u2, u1} R V P (DivisionRing.toRing.{u3} R (Field.toDivisionRing.{u3} R (LinearOrderedField.toField.{u3} R _inst_1))) _inst_2 _inst_3 _inst_4)) y s) -> (AffineSubspace.SOppSide.{u3, u2, u1} R V P (LinearOrderedCommRing.toStrictOrderedCommRing.{u3} R (LinearOrderedField.toLinearOrderedCommRing.{u3} R _inst_1)) _inst_2 _inst_3 _inst_4 s x z)
Case conversion may be inaccurate. Consider using '#align sbtw.s_opp_side_of_not_mem_of_mem Sbtw.sOppSide_of_not_mem_of_memₓ'. -/
theorem Sbtw.sOppSide_of_not_mem_of_mem {s : AffineSubspace R P} {x y z : P} (h : Sbtw R x y z)
    (hx : x ∉ s) (hy : y ∈ s) : s.SOppSide x z :=
  by
  refine' ⟨h.wbtw.w_opp_side₁₃ hy, hx, fun hz => hx _⟩
  rcases h with ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hyx, hyz⟩
  rw [line_map_apply] at hy
  have ht : t ≠ 1 := by rintro rfl; simpa [line_map_apply] using hyz
  have hy' := vsub_mem_direction hy hz
  rw [vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev z, ← neg_one_smul R (z -ᵥ x), ← add_smul, ←
    sub_eq_add_neg, s.direction.smul_mem_iff (sub_ne_zero_of_ne ht)] at hy'
  rwa [vadd_mem_iff_mem_of_mem_direction (Submodule.smul_mem _ _ hy')] at hy
#align sbtw.s_opp_side_of_not_mem_of_mem Sbtw.sOppSide_of_not_mem_of_mem

/- warning: affine_subspace.s_same_side_smul_vsub_vadd_left -> AffineSubspace.sSameSide_smul_vsub_vadd_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_smul_vsub_vadd_left AffineSubspace.sSameSide_smul_vsub_vadd_leftₓ'. -/
theorem sSameSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨w_same_side_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx _, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne.symm,
    vsub_right_mem_direction_iff_mem hp₁] at h
#align affine_subspace.s_same_side_smul_vsub_vadd_left AffineSubspace.sSameSide_smul_vsub_vadd_left

/- warning: affine_subspace.s_same_side_smul_vsub_vadd_right -> AffineSubspace.sSameSide_smul_vsub_vadd_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_smul_vsub_vadd_right AffineSubspace.sSameSide_smul_vsub_vadd_rightₓ'. -/
theorem sSameSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : 0 < t) : s.SSameSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sSameSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm
#align affine_subspace.s_same_side_smul_vsub_vadd_right AffineSubspace.sSameSide_smul_vsub_vadd_right

/- warning: affine_subspace.s_same_side_line_map_left -> AffineSubspace.sSameSide_lineMap_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_line_map_left AffineSubspace.sSameSide_lineMap_leftₓ'. -/
theorem sSameSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide (lineMap x y t) y :=
  sSameSide_smul_vsub_vadd_left hy hx hx ht
#align affine_subspace.s_same_side_line_map_left AffineSubspace.sSameSide_lineMap_left

/- warning: affine_subspace.s_same_side_line_map_right -> AffineSubspace.sSameSide_lineMap_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_same_side_line_map_right AffineSubspace.sSameSide_lineMap_rightₓ'. -/
theorem sSameSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : 0 < t) : s.SSameSide y (lineMap x y t) :=
  (sSameSide_lineMap_left hx hy ht).symm
#align affine_subspace.s_same_side_line_map_right AffineSubspace.sSameSide_lineMap_right

/- warning: affine_subspace.s_opp_side_smul_vsub_vadd_left -> AffineSubspace.sOppSide_smul_vsub_vadd_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_smul_vsub_vadd_left AffineSubspace.sOppSide_smul_vsub_vadd_leftₓ'. -/
theorem sOppSide_smul_vsub_vadd_left {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide (t • (x -ᵥ p₁) +ᵥ p₂) x :=
  by
  refine' ⟨w_opp_side_smul_vsub_vadd_left x hp₁ hp₂ ht.le, fun h => hx _, hx⟩
  rwa [vadd_mem_iff_mem_direction _ hp₂, s.direction.smul_mem_iff ht.ne,
    vsub_right_mem_direction_iff_mem hp₁] at h
#align affine_subspace.s_opp_side_smul_vsub_vadd_left AffineSubspace.sOppSide_smul_vsub_vadd_left

/- warning: affine_subspace.s_opp_side_smul_vsub_vadd_right -> AffineSubspace.sOppSide_smul_vsub_vadd_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_smul_vsub_vadd_right AffineSubspace.sOppSide_smul_vsub_vadd_rightₓ'. -/
theorem sOppSide_smul_vsub_vadd_right {s : AffineSubspace R P} {x p₁ p₂ : P} (hx : x ∉ s)
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) {t : R} (ht : t < 0) : s.SOppSide x (t • (x -ᵥ p₁) +ᵥ p₂) :=
  (sOppSide_smul_vsub_vadd_left hx hp₁ hp₂ ht).symm
#align affine_subspace.s_opp_side_smul_vsub_vadd_right AffineSubspace.sOppSide_smul_vsub_vadd_right

/- warning: affine_subspace.s_opp_side_line_map_left -> AffineSubspace.sOppSide_lineMap_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_line_map_left AffineSubspace.sOppSide_lineMap_leftₓ'. -/
theorem sOppSide_lineMap_left {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide (lineMap x y t) y :=
  sOppSide_smul_vsub_vadd_left hy hx hx ht
#align affine_subspace.s_opp_side_line_map_left AffineSubspace.sOppSide_lineMap_left

/- warning: affine_subspace.s_opp_side_line_map_right -> AffineSubspace.sOppSide_lineMap_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_line_map_right AffineSubspace.sOppSide_lineMap_rightₓ'. -/
theorem sOppSide_lineMap_right {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) {t : R}
    (ht : t < 0) : s.SOppSide y (lineMap x y t) :=
  (sOppSide_lineMap_left hx hy ht).symm
#align affine_subspace.s_opp_side_line_map_right AffineSubspace.sOppSide_lineMap_right

/- warning: affine_subspace.set_of_w_same_side_eq_image2 -> AffineSubspace.setOf_wSameSide_eq_image2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.set_of_w_same_side_eq_image2 AffineSubspace.setOf_wSameSide_eq_image2ₓ'. -/
theorem setOf_wSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ici 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Ici, mem_coe]
  constructor
  · rw [w_same_side_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine' ⟨0, p₂, le_refl _, hp₂, _⟩
      simp [h]
    · refine' ⟨r₁ / r₂, p₂, (div_pos hr₁ hr₂).le, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact w_same_side_smul_vsub_vadd_right x hp hp' ht
#align affine_subspace.set_of_w_same_side_eq_image2 AffineSubspace.setOf_wSameSide_eq_image2

/- warning: affine_subspace.set_of_s_same_side_eq_image2 -> AffineSubspace.setOf_sSameSide_eq_image2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.set_of_s_same_side_eq_image2 AffineSubspace.setOf_sSameSide_eq_image2ₓ'. -/
theorem setOf_sSameSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SSameSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Ioi 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Ioi, mem_coe]
  constructor
  · rw [s_same_side_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h.symm ▸ hp₂))
    · refine' ⟨r₁ / r₂, p₂, div_pos hr₁ hr₂, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, h, smul_smul, inv_mul_cancel hr₂.ne.symm, one_smul,
        vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact s_same_side_smul_vsub_vadd_right hx hp hp' ht
#align affine_subspace.set_of_s_same_side_eq_image2 AffineSubspace.setOf_sSameSide_eq_image2

/- warning: affine_subspace.set_of_w_opp_side_eq_image2 -> AffineSubspace.setOf_wOppSide_eq_image2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.set_of_w_opp_side_eq_image2 AffineSubspace.setOf_wOppSide_eq_image2ₓ'. -/
theorem setOf_wOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.WOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iic 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Iic, mem_coe]
  constructor
  · rw [w_opp_side_iff_exists_left hp, or_iff_right hx]
    rintro ⟨p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      refine' ⟨0, p₂, le_refl _, hp₂, _⟩
      simp [h]
    · refine' ⟨-r₁ / r₂, p₂, (div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂).le, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul, inv_mul_cancel hr₂.ne.symm,
        one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact w_opp_side_smul_vsub_vadd_right x hp hp' ht
#align affine_subspace.set_of_w_opp_side_eq_image2 AffineSubspace.setOf_wOppSide_eq_image2

/- warning: affine_subspace.set_of_s_opp_side_eq_image2 -> AffineSubspace.setOf_sOppSide_eq_image2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.set_of_s_opp_side_eq_image2 AffineSubspace.setOf_sOppSide_eq_image2ₓ'. -/
theorem setOf_sOppSide_eq_image2 {s : AffineSubspace R P} {x p : P} (hx : x ∉ s) (hp : p ∈ s) :
    { y | s.SOppSide x y } = Set.image2 (fun (t : R) q => t • (x -ᵥ p) +ᵥ q) (Set.Iio 0) s :=
  by
  ext y
  simp_rw [Set.mem_setOf, Set.mem_image2, Set.mem_Iio, mem_coe]
  constructor
  · rw [s_opp_side_iff_exists_left hp]
    rintro ⟨-, hy, p₂, hp₂, h | h | ⟨r₁, r₂, hr₁, hr₂, h⟩⟩
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hx (h.symm ▸ hp))
    · rw [vsub_eq_zero_iff_eq] at h
      exact False.elim (hy (h ▸ hp₂))
    · refine' ⟨-r₁ / r₂, p₂, div_neg_of_neg_of_pos (Left.neg_neg_iff.2 hr₁) hr₂, hp₂, _⟩
      rw [div_eq_inv_mul, ← smul_smul, neg_smul, h, smul_neg, smul_smul, inv_mul_cancel hr₂.ne.symm,
        one_smul, neg_vsub_eq_vsub_rev, vsub_vadd]
  · rintro ⟨t, p', ht, hp', rfl⟩
    exact s_opp_side_smul_vsub_vadd_right hx hp hp' ht
#align affine_subspace.set_of_s_opp_side_eq_image2 AffineSubspace.setOf_sOppSide_eq_image2

/- warning: affine_subspace.w_opp_side_point_reflection -> AffineSubspace.wOppSide_pointReflection is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.w_opp_side_point_reflection AffineSubspace.wOppSide_pointReflectionₓ'. -/
theorem wOppSide_pointReflection {s : AffineSubspace R P} {x : P} (y : P) (hx : x ∈ s) :
    s.WOppSide y (pointReflection R x y) :=
  (wbtw_pointReflection R _ _).wOppSide₁₃ hx
#align affine_subspace.w_opp_side_point_reflection AffineSubspace.wOppSide_pointReflection

/- warning: affine_subspace.s_opp_side_point_reflection -> AffineSubspace.sOppSide_pointReflection is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.s_opp_side_point_reflection AffineSubspace.sOppSide_pointReflectionₓ'. -/
theorem sOppSide_pointReflection {s : AffineSubspace R P} {x y : P} (hx : x ∈ s) (hy : y ∉ s) :
    s.SOppSide y (pointReflection R x y) :=
  by
  refine' (sbtw_pointReflection_of_ne R fun h => hy _).sOppSide_of_not_mem_of_mem hy hx
  rwa [← h]
#align affine_subspace.s_opp_side_point_reflection AffineSubspace.sOppSide_pointReflection

end LinearOrderedField

section Normed

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]

variable [NormedAddTorsor V P]

include V

/- warning: affine_subspace.is_connected_set_of_w_same_side -> AffineSubspace.isConnected_setOf_wSameSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)} (x : P), (Set.Nonempty.{u2} P ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (HasLiftT.mk.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (CoeTCₓ.coe.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (SetLike.Set.hasCoeT.{u2, u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.setLike.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4))))) s)) -> (IsConnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.WSameSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)} (x : P), (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.instSetLikeAffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) s)) -> (IsConnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.WSameSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_connected_set_of_w_same_side AffineSubspace.isConnected_setOf_wSameSideₓ'. -/
theorem isConnected_setOf_wSameSide {s : AffineSubspace ℝ P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WSameSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x ∈ s
  · convert isConnected_univ
    · simp [w_same_side_of_left_mem, hx]
    · exact AddTorsor.connectedSpace V P
  · rw [set_of_w_same_side_eq_image2 hx hp, ← Set.image_prod]
    refine'
      (is_connected_Ici.prod (isConnected_iff_connectedSpace.2 _)).image _
        ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
    convert AddTorsor.connectedSpace s.direction s
#align affine_subspace.is_connected_set_of_w_same_side AffineSubspace.isConnected_setOf_wSameSide

/- warning: affine_subspace.is_preconnected_set_of_w_same_side -> AffineSubspace.isPreconnected_setOf_wSameSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.WSameSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.WSameSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_preconnected_set_of_w_same_side AffineSubspace.isPreconnected_setOf_wSameSideₓ'. -/
theorem isPreconnected_setOf_wSameSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WSameSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert isPreconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_w_same_side_bot]
    rfl
  · exact (is_connected_set_of_w_same_side x h).IsPreconnected
#align affine_subspace.is_preconnected_set_of_w_same_side AffineSubspace.isPreconnected_setOf_wSameSide

/- warning: affine_subspace.is_connected_set_of_s_same_side -> AffineSubspace.isConnected_setOf_sSameSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)} {x : P}, (Not (Membership.Mem.{u2, u2} P (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (SetLike.hasMem.{u2, u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.setLike.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4))) x s)) -> (Set.Nonempty.{u2} P ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (HasLiftT.mk.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (CoeTCₓ.coe.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (SetLike.Set.hasCoeT.{u2, u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.setLike.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4))))) s)) -> (IsConnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.SSameSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)} {x : P}, (Not (Membership.mem.{u1, u1} P (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) (SetLike.instMembership.{u1, u1} (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.instSetLikeAffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4))) x s)) -> (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.instSetLikeAffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) s)) -> (IsConnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.SSameSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_connected_set_of_s_same_side AffineSubspace.isConnected_setOf_sSameSideₓ'. -/
theorem isConnected_setOf_sSameSide {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SSameSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [set_of_s_same_side_eq_image2 hx hp, ← Set.image_prod]
  refine'
    (is_connected_Ioi.prod (isConnected_iff_connectedSpace.2 _)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
  convert AddTorsor.connectedSpace s.direction s
#align affine_subspace.is_connected_set_of_s_same_side AffineSubspace.isConnected_setOf_sSameSide

/- warning: affine_subspace.is_preconnected_set_of_s_same_side -> AffineSubspace.isPreconnected_setOf_sSameSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.SSameSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.SSameSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_preconnected_set_of_s_same_side AffineSubspace.isPreconnected_setOf_sSameSideₓ'. -/
theorem isPreconnected_setOf_sSameSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SSameSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert isPreconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_s_same_side_bot]
    rfl
  · by_cases hx : x ∈ s
    · convert isPreconnected_empty
      simp only [hx, s_same_side, not_true, false_and_iff, and_false_iff]
      rfl
    · exact (is_connected_set_of_s_same_side hx h).IsPreconnected
#align affine_subspace.is_preconnected_set_of_s_same_side AffineSubspace.isPreconnected_setOf_sSameSide

/- warning: affine_subspace.is_connected_set_of_w_opp_side -> AffineSubspace.isConnected_setOf_wOppSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)} (x : P), (Set.Nonempty.{u2} P ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (HasLiftT.mk.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (CoeTCₓ.coe.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (SetLike.Set.hasCoeT.{u2, u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.setLike.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4))))) s)) -> (IsConnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.WOppSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)} (x : P), (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.instSetLikeAffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) s)) -> (IsConnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.WOppSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_connected_set_of_w_opp_side AffineSubspace.isConnected_setOf_wOppSideₓ'. -/
theorem isConnected_setOf_wOppSide {s : AffineSubspace ℝ P} (x : P) (h : (s : Set P).Nonempty) :
    IsConnected { y | s.WOppSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  by_cases hx : x ∈ s
  · convert isConnected_univ
    · simp [w_opp_side_of_left_mem, hx]
    · exact AddTorsor.connectedSpace V P
  · rw [set_of_w_opp_side_eq_image2 hx hp, ← Set.image_prod]
    refine'
      (is_connected_Iic.prod (isConnected_iff_connectedSpace.2 _)).image _
        ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
    convert AddTorsor.connectedSpace s.direction s
#align affine_subspace.is_connected_set_of_w_opp_side AffineSubspace.isConnected_setOf_wOppSide

/- warning: affine_subspace.is_preconnected_set_of_w_opp_side -> AffineSubspace.isPreconnected_setOf_wOppSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.WOppSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.WOppSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_preconnected_set_of_w_opp_side AffineSubspace.isPreconnected_setOf_wOppSideₓ'. -/
theorem isPreconnected_setOf_wOppSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.WOppSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert isPreconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_w_opp_side_bot]
    rfl
  · exact (is_connected_set_of_w_opp_side x h).IsPreconnected
#align affine_subspace.is_preconnected_set_of_w_opp_side AffineSubspace.isPreconnected_setOf_wOppSide

/- warning: affine_subspace.is_connected_set_of_s_opp_side -> AffineSubspace.isConnected_setOf_sOppSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)} {x : P}, (Not (Membership.Mem.{u2, u2} P (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (SetLike.hasMem.{u2, u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.setLike.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4))) x s)) -> (Set.Nonempty.{u2} P ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (HasLiftT.mk.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (CoeTCₓ.coe.{succ u2, succ u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (Set.{u2} P) (SetLike.Set.hasCoeT.{u2, u2} (AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.setLike.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4))))) s)) -> (IsConnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.SOppSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y)))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] {s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)} {x : P}, (Not (Membership.mem.{u1, u1} P (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) (SetLike.instMembership.{u1, u1} (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.instSetLikeAffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4))) x s)) -> (Set.Nonempty.{u1} P (SetLike.coe.{u1, u1} (AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) P (AffineSubspace.instSetLikeAffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) s)) -> (IsConnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.SOppSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y)))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_connected_set_of_s_opp_side AffineSubspace.isConnected_setOf_sOppSideₓ'. -/
theorem isConnected_setOf_sOppSide {s : AffineSubspace ℝ P} {x : P} (hx : x ∉ s)
    (h : (s : Set P).Nonempty) : IsConnected { y | s.SOppSide x y } :=
  by
  obtain ⟨p, hp⟩ := h
  haveI : Nonempty s := ⟨⟨p, hp⟩⟩
  rw [set_of_s_opp_side_eq_image2 hx hp, ← Set.image_prod]
  refine'
    (is_connected_Iio.prod (isConnected_iff_connectedSpace.2 _)).image _
      ((continuous_fst.smul continuous_const).vadd continuous_snd).ContinuousOn
  convert AddTorsor.connectedSpace s.direction s
#align affine_subspace.is_connected_set_of_s_opp_side AffineSubspace.isConnected_setOf_sOppSide

/- warning: affine_subspace.is_preconnected_set_of_s_opp_side -> AffineSubspace.isPreconnected_setOf_sOppSide is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u1} V] [_inst_2 : NormedSpace.{0, u1} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u1, u2} Real V P Real.ring (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u2} P (UniformSpace.toTopologicalSpace.{u2} P (PseudoMetricSpace.toUniformSpace.{u2} P _inst_3)) (setOf.{u2} P (fun (y : P) => AffineSubspace.SOppSide.{0, u1, u2} Real V P Real.strictOrderedCommRing (SeminormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} V P _inst_1 _inst_3 _inst_4) s x y))
but is expected to have type
  forall {V : Type.{u2}} {P : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u2} V] [_inst_2 : NormedSpace.{0, u2} Real V Real.normedField _inst_1] [_inst_3 : PseudoMetricSpace.{u1} P] [_inst_4 : NormedAddTorsor.{u2, u1} V P _inst_1 _inst_3] (s : AffineSubspace.{0, u2, u1} Real V P Real.instRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4)) (x : P), IsPreconnected.{u1} P (UniformSpace.toTopologicalSpace.{u1} P (PseudoMetricSpace.toUniformSpace.{u1} P _inst_3)) (setOf.{u1} P (fun (y : P) => AffineSubspace.SOppSide.{0, u2, u1} Real V P Real.instStrictOrderedCommRingReal (SeminormedAddCommGroup.toAddCommGroup.{u2} V _inst_1) (NormedSpace.toModule.{0, u2} Real V Real.normedField _inst_1 _inst_2) (NormedAddTorsor.toAddTorsor.{u2, u1} V P _inst_1 _inst_3 _inst_4) s x y))
Case conversion may be inaccurate. Consider using '#align affine_subspace.is_preconnected_set_of_s_opp_side AffineSubspace.isPreconnected_setOf_sOppSideₓ'. -/
theorem isPreconnected_setOf_sOppSide (s : AffineSubspace ℝ P) (x : P) :
    IsPreconnected { y | s.SOppSide x y } :=
  by
  rcases Set.eq_empty_or_nonempty (s : Set P) with (h | h)
  · convert isPreconnected_empty
    rw [coe_eq_bot_iff] at h
    simp only [h, not_s_opp_side_bot]
    rfl
  · by_cases hx : x ∈ s
    · convert isPreconnected_empty
      simp only [hx, s_opp_side, not_true, false_and_iff, and_false_iff]
      rfl
    · exact (is_connected_set_of_s_opp_side hx h).IsPreconnected
#align affine_subspace.is_preconnected_set_of_s_opp_side AffineSubspace.isPreconnected_setOf_sOppSide

end Normed

end AffineSubspace

