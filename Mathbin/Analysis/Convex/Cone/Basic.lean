/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.convex.cone.basic
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Hull
import Mathbin.Data.Real.Basic
import Mathbin.LinearAlgebra.LinearPmap

/-!
# Convex cones

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In a `𝕜`-module `E`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `complete_lattice`, and define their
images (`convex_cone.map`) and preimages (`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We define `convex.to_cone` to be the minimal cone that includes a given convex set.

## Main statements

We prove two extension theorems:
* `riesz_extension`:
  [M. Riesz extension theorem](https://en.wikipedia.org/wiki/M._Riesz_extension_theorem) says that
  if `s` is a convex cone in a real vector space `E`, `p` is a submodule of `E`
  such that `p + s = E`, and `f` is a linear function `p → ℝ` which is
  nonnegative on `p ∩ s`, then there exists a globally defined linear function
  `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.
* `exists_extension_of_le_sublinear`:
  Hahn-Banach theorem: if `N : E → ℝ` is a sublinear map, `f` is a linear map
  defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
  then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
  for all `x`

We prove the following theorems:
* `convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `K` in a complete, real inner product space `H`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).
* `convex_cone.inner_dual_cone_of_inner_dual_cone_eq_self`:

## Implementation notes

While `convex 𝕜` is a predicate on sets, `convex_cone 𝕜 E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/


assert_not_exists NormedSpace

open Set LinearMap

open Classical Pointwise

variable {𝕜 E F G : Type _}

/-! ### Definition of `convex_cone` and basic properties -/


section Definitions

variable (𝕜 E) [OrderedSemiring 𝕜]

#print ConvexCone /-
/-- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure ConvexCone [AddCommMonoid E] [SMul 𝕜 E] where
  carrier : Set E
  smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (hx : x ∈ carrier) ⦃y⦄ (hy : y ∈ carrier), x + y ∈ carrier
#align convex_cone ConvexCone
-/

end Definitions

variable {𝕜 E}

namespace ConvexCone

section OrderedSemiring

variable [OrderedSemiring 𝕜] [AddCommMonoid E]

section SMul

variable [SMul 𝕜 E] (S T : ConvexCone 𝕜 E)

instance : SetLike (ConvexCone 𝕜 E) E where
  coe := carrier
  coe_injective' S T h := by cases S <;> cases T <;> congr

/- warning: convex_cone.coe_mk -> ConvexCone.coe_mk is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {s : Set.{u2} E} {h₁ : forall {{c : 𝕜}}, (LT.lt.{u1} 𝕜 (Preorder.toHasLt.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommMonoid.toPartialOrder.{u1} 𝕜 (OrderedSemiring.toOrderedAddCommMonoid.{u1} 𝕜 _inst_1)))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)))))))) c) -> (forall {{x : E}}, (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s) -> (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (SMul.smul.{u1, u2} 𝕜 E _inst_3 c x) s))} {h₂ : forall {{x : E}}, (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s) -> (forall {{y : E}}, (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) y s) -> (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))) x y) s))}, Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (ConvexCone.mk.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 s h₁ h₂)) s
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {s : Set.{u2} E} {h₁ : forall {{c : 𝕜}}, (LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedSemiring.toPartialOrder.{u1} 𝕜 _inst_1))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) c) -> (forall {{x : E}}, (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s) -> (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E _inst_3) c x) s))} {h₂ : forall {{x : E}}, (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s) -> (forall {{y : E}}, (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) y s) -> (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))) x y) s))}, Eq.{succ u2} (Set.{u2} E) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.mk.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 s h₁ h₂)) s
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_mk ConvexCone.coe_mkₓ'. -/
@[simp]
theorem coe_mk {s : Set E} {h₁ h₂} : ↑(@mk 𝕜 _ _ _ _ s h₁ h₂) = s :=
  rfl
#align convex_cone.coe_mk ConvexCone.coe_mk

/- warning: convex_cone.mem_mk -> ConvexCone.mem_mk is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {s : Set.{u2} E} {h₁ : forall {{c : 𝕜}}, (LT.lt.{u1} 𝕜 (Preorder.toHasLt.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommMonoid.toPartialOrder.{u1} 𝕜 (OrderedSemiring.toOrderedAddCommMonoid.{u1} 𝕜 _inst_1)))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)))))))) c) -> (forall {{x : E}}, (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s) -> (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (SMul.smul.{u1, u2} 𝕜 E _inst_3 c x) s))} {h₂ : forall {{x : E}}, (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s) -> (forall {{y : E}}, (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) y s) -> (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))) x y) s))} {x : E}, Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (ConvexCone.mk.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 s h₁ h₂)) (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s)
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {s : Set.{u2} E} {h₁ : forall {{c : 𝕜}}, (LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedSemiring.toPartialOrder.{u1} 𝕜 _inst_1))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) c) -> (forall {{x : E}}, (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s) -> (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E _inst_3) c x) s))} {h₂ : forall {{x : E}}, (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s) -> (forall {{y : E}}, (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) y s) -> (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))) x y) s))} {x : E}, Iff (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (ConvexCone.mk.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 s h₁ h₂)) (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s)
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_mk ConvexCone.mem_mkₓ'. -/
@[simp]
theorem mem_mk {s : Set E} {h₁ h₂ x} : x ∈ @mk 𝕜 _ _ _ _ s h₁ h₂ ↔ x ∈ s :=
  Iff.rfl
#align convex_cone.mem_mk ConvexCone.mem_mk

/- warning: convex_cone.ext -> ConvexCone.ext is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3} {T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3}, (forall (x : E), Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x T)) -> (Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S T)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3} {T : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3}, (forall (x : E), Iff (Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) (Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) x T)) -> (Eq.{succ u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) S T)
Case conversion may be inaccurate. Consider using '#align convex_cone.ext ConvexCone.extₓ'. -/
/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext]
theorem ext {S T : ConvexCone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align convex_cone.ext ConvexCone.ext

/- warning: convex_cone.smul_mem -> ConvexCone.smul_mem is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) {c : 𝕜} {x : E}, (LT.lt.{u1} 𝕜 (Preorder.toHasLt.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommMonoid.toPartialOrder.{u1} 𝕜 (OrderedSemiring.toOrderedAddCommMonoid.{u1} 𝕜 _inst_1)))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)))))))) c) -> (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) -> (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (SMul.smul.{u1, u2} 𝕜 E _inst_3 c x) S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] (S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) {c : 𝕜} {x : E}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedSemiring.toPartialOrder.{u2} 𝕜 _inst_1))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))))) c) -> (Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) -> (Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) (HSMul.hSMul.{u2, u1, u1} 𝕜 E E (instHSMul.{u2, u1} 𝕜 E _inst_3) c x) S)
Case conversion may be inaccurate. Consider using '#align convex_cone.smul_mem ConvexCone.smul_memₓ'. -/
theorem smul_mem {c : 𝕜} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S :=
  S.smul_mem' hc hx
#align convex_cone.smul_mem ConvexCone.smul_mem

/- warning: convex_cone.add_mem -> ConvexCone.add_mem is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) {{x : E}}, (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) -> (forall {{y : E}}, (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) y S) -> (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))) x y) S))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) {{x : E}}, (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) -> (forall {{y : E}}, (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) y S) -> (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))) x y) S))
Case conversion may be inaccurate. Consider using '#align convex_cone.add_mem ConvexCone.add_memₓ'. -/
theorem add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S :=
  S.add_mem' hx hy
#align convex_cone.add_mem ConvexCone.add_mem

instance : AddMemClass (ConvexCone 𝕜 E) E where add_mem c a b ha hb := add_mem c ha hb

instance : Inf (ConvexCone 𝕜 E) :=
  ⟨fun S T =>
    ⟨S ∩ T, fun c hc x hx => ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩, fun x hx y hy =>
      ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

/- warning: convex_cone.coe_inf -> ConvexCone.coe_inf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3), Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (Inf.inf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S T)) (Inter.inter.{u2} (Set.{u2} E) (Set.hasInter.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) S) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) T))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3), Eq.{succ u2} (Set.{u2} E) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Inf.inf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instInfConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S T)) (Inter.inter.{u2} (Set.{u2} E) (Set.instInterSet.{u2} E) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) T))
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_inf ConvexCone.coe_infₓ'. -/
@[simp]
theorem coe_inf : ((S ⊓ T : ConvexCone 𝕜 E) : Set E) = ↑S ∩ ↑T :=
  rfl
#align convex_cone.coe_inf ConvexCone.coe_inf

/- warning: convex_cone.mem_inf -> ConvexCone.mem_inf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) {x : E}, Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (Inf.inf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S T)) (And (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x T))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) {x : E}, Iff (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (Inf.inf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instInfConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S T)) (And (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x S) (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x T))
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_inf ConvexCone.mem_infₓ'. -/
theorem mem_inf {x} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl
#align convex_cone.mem_inf ConvexCone.mem_inf

instance : InfSet (ConvexCone 𝕜 E) :=
  ⟨fun S =>
    ⟨⋂ s ∈ S, ↑s, fun c hc x hx => mem_biInter fun s hs => s.smul_mem hc <| mem_iInter₂.1 hx s hs,
      fun x hx y hy =>
      mem_biInter fun s hs => s.add_mem (mem_iInter₂.1 hx s hs) (mem_iInter₂.1 hy s hs)⟩⟩

/- warning: convex_cone.coe_Inf -> ConvexCone.coe_sInf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)), Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (InfSet.sInf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S)) (Set.iInter.{u2, succ u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (fun (s : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) => Set.iInter.{u2, 0} E (Membership.Mem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (Set.hasMem.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) s S) (fun (H : Membership.Mem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (Set.hasMem.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) s S) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) s)))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)), Eq.{succ u2} (Set.{u2} E) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (InfSet.sInf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instInfSetConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S)) (Set.iInter.{u2, succ u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (fun (s : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) => Set.iInter.{u2, 0} E (Membership.mem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (Set.instMembershipSet.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) s S) (fun (H : Membership.mem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (Set.instMembershipSet.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) s S) => SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) s)))
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_Inf ConvexCone.coe_sInfₓ'. -/
@[simp]
theorem coe_sInf (S : Set (ConvexCone 𝕜 E)) : ↑(sInf S) = ⋂ s ∈ S, (s : Set E) :=
  rfl
#align convex_cone.coe_Inf ConvexCone.coe_sInf

/- warning: convex_cone.mem_Inf -> ConvexCone.mem_sInf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {x : E} {S : Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)}, Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (InfSet.sInf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S)) (forall (s : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3), (Membership.Mem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (Set.hasMem.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) s S) -> (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x s))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {x : E} {S : Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)}, Iff (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (InfSet.sInf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instInfSetConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) S)) (forall (s : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3), (Membership.mem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (Set.instMembershipSet.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) s S) -> (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x s))
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_Inf ConvexCone.mem_sInfₓ'. -/
theorem mem_sInf {x : E} {S : Set (ConvexCone 𝕜 E)} : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s :=
  mem_iInter₂
#align convex_cone.mem_Inf ConvexCone.mem_sInf

/- warning: convex_cone.coe_infi -> ConvexCone.coe_iInf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {ι : Sort.{u3}} (f : ι -> (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)), Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (iInf.{u2, u3} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) ι f)) (Set.iInter.{u2, u3} E ι (fun (i : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (f i)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {ι : Sort.{u3}} (f : ι -> (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)), Eq.{succ u1} (Set.{u1} E) (SetLike.coe.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (iInf.{u1, u3} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instInfSetConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) ι f)) (Set.iInter.{u1, u3} E ι (fun (i : ι) => SetLike.coe.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (f i)))
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_infi ConvexCone.coe_iInfₓ'. -/
@[simp]
theorem coe_iInf {ι : Sort _} (f : ι → ConvexCone 𝕜 E) : ↑(iInf f) = ⋂ i, (f i : Set E) := by
  simp [iInf]
#align convex_cone.coe_infi ConvexCone.coe_iInf

/- warning: convex_cone.mem_infi -> ConvexCone.mem_iInf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {ι : Sort.{u3}} {x : E} {f : ι -> (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)}, Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (iInf.{u2, u3} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) ι f)) (forall (i : ι), Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (f i))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {ι : Sort.{u3}} {x : E} {f : ι -> (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)}, Iff (Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) x (iInf.{u1, u3} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instInfSetConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) ι f)) (forall (i : ι), Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) x (f i))
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_infi ConvexCone.mem_iInfₓ'. -/
theorem mem_iInf {ι : Sort _} {x : E} {f : ι → ConvexCone 𝕜 E} : x ∈ iInf f ↔ ∀ i, x ∈ f i :=
  mem_iInter₂.trans <| by simp
#align convex_cone.mem_infi ConvexCone.mem_iInf

variable (𝕜)

instance : Bot (ConvexCone 𝕜 E) :=
  ⟨⟨∅, fun c hc x => False.elim, fun x => False.elim⟩⟩

/- warning: convex_cone.mem_bot -> ConvexCone.mem_bot is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (x : E), Eq.{1} Prop (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (Bot.bot.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasBot.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) False
but is expected to have type
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (x : E), Eq.{1} Prop (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (Bot.bot.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instBotConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) False
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_bot ConvexCone.mem_botₓ'. -/
theorem mem_bot (x : E) : (x ∈ (⊥ : ConvexCone 𝕜 E)) = False :=
  rfl
#align convex_cone.mem_bot ConvexCone.mem_bot

/- warning: convex_cone.coe_bot -> ConvexCone.coe_bot is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E], Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (Bot.bot.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasBot.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))
but is expected to have type
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E], Eq.{succ u2} (Set.{u2} E) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Bot.bot.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instBotConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.instEmptyCollectionSet.{u2} E))
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_bot ConvexCone.coe_botₓ'. -/
@[simp]
theorem coe_bot : ↑(⊥ : ConvexCone 𝕜 E) = (∅ : Set E) :=
  rfl
#align convex_cone.coe_bot ConvexCone.coe_bot

instance : Top (ConvexCone 𝕜 E) :=
  ⟨⟨univ, fun c hc x hx => mem_univ _, fun x hx y hy => mem_univ _⟩⟩

/- warning: convex_cone.mem_top -> ConvexCone.mem_top is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (x : E), Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (Top.top.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasTop.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))
but is expected to have type
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (x : E), Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) x (Top.top.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instTopConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_top ConvexCone.mem_topₓ'. -/
theorem mem_top (x : E) : x ∈ (⊤ : ConvexCone 𝕜 E) :=
  mem_univ x
#align convex_cone.mem_top ConvexCone.mem_top

/- warning: convex_cone.coe_top -> ConvexCone.coe_top is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E], Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (Top.top.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.hasTop.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) (Set.univ.{u2} E)
but is expected to have type
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E], Eq.{succ u2} (Set.{u2} E) (SetLike.coe.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Top.top.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instTopConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) (Set.univ.{u2} E)
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_top ConvexCone.coe_topₓ'. -/
@[simp]
theorem coe_top : ↑(⊤ : ConvexCone 𝕜 E) = (univ : Set E) :=
  rfl
#align convex_cone.coe_top ConvexCone.coe_top

instance : CompleteLattice (ConvexCone 𝕜 E) :=
  { SetLike.partialOrder with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S x => False.elim
    top := ⊤
    le_top := fun S x hx => mem_top 𝕜 x
    inf := (· ⊓ ·)
    sInf := InfSet.sInf
    sup := fun a b => sInf { x | a ≤ x ∧ b ≤ x }
    sSup := fun s => sInf { T | ∀ S ∈ s, S ≤ T }
    le_sup_left := fun a b => fun x hx => mem_sInf.2 fun s hs => hs.1 hx
    le_sup_right := fun a b => fun x hx => mem_sInf.2 fun s hs => hs.2 hx
    sup_le := fun a b c ha hb x hx => mem_sInf.1 hx c ⟨ha, hb⟩
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun a b x => And.left
    inf_le_right := fun a b x => And.right
    le_sup := fun s p hs x hx => mem_sInf.2 fun t ht => ht p hs hx
    sup_le := fun s p hs x hx => mem_sInf.1 hx p hs
    le_inf := fun s a ha x hx => mem_sInf.2 fun t ht => ha t ht hx
    inf_le := fun s a ha x hx => mem_sInf.1 hx _ ha }

instance : Inhabited (ConvexCone 𝕜 E) :=
  ⟨⊥⟩

end SMul

section Module

variable [Module 𝕜 E] (S : ConvexCone 𝕜 E)

/- warning: convex_cone.convex -> ConvexCone.convex is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))), Convex.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))))))) S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2] (S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))), Convex.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3)))) (SetLike.coe.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) S)
Case conversion may be inaccurate. Consider using '#align convex_cone.convex ConvexCone.convexₓ'. -/
protected theorem convex : Convex 𝕜 (S : Set E) :=
  convex_iff_forall_pos.2 fun x hx y hy a b ha hb _ =>
    S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)
#align convex_cone.convex ConvexCone.convex

end Module

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G]

section MulAction

variable [MulAction 𝕜 E] (S : ConvexCone 𝕜 E)

/- warning: convex_cone.smul_mem_iff -> ConvexCone.smul_mem_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.smul_mem_iff ConvexCone.smul_mem_iffₓ'. -/
theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : E} : c • x ∈ S ↔ x ∈ S :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hc⟩
#align convex_cone.smul_mem_iff ConvexCone.smul_mem_iff

end MulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

#print ConvexCone.map /-
/-- The image of a convex cone under a `𝕜`-linear map is a convex cone. -/
def map (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) : ConvexCone 𝕜 F
    where
  carrier := f '' S
  smul_mem' := fun c hc y ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx)
  add_mem' := fun y₁ ⟨x₁, hx₁, hy₁⟩ y₂ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (S.add_mem hx₁ hx₂)
#align convex_cone.map ConvexCone.map
-/

/- warning: convex_cone.mem_map -> ConvexCone.mem_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_map ConvexCone.mem_mapₓ'. -/
@[simp]
theorem mem_map {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 E} {y : F} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex
#align convex_cone.mem_map ConvexCone.mem_map

/- warning: convex_cone.map_map -> ConvexCone.map_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.map_map ConvexCone.map_mapₓ'. -/
theorem map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 E) :
    (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f S
#align convex_cone.map_map ConvexCone.map_map

/- warning: convex_cone.map_id -> ConvexCone.map_id is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2] (S : ConvexCone.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2 _inst_5))))), Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2 _inst_5))))) (ConvexCone.map.{u1, u2, u2} 𝕜 E E _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearMap.id.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2 _inst_5) S) S
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2] (S : ConvexCone.{u2, u1} 𝕜 E (OrderedCommSemiring.toOrderedSemiring.{u2} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1)))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_5))))), Eq.{succ u1} (ConvexCone.{u2, u1} 𝕜 E (OrderedCommSemiring.toOrderedSemiring.{u2} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1)))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_5))))) (ConvexCone.map.{u2, u1, u1} 𝕜 E E _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearMap.id.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_5) S) S
Case conversion may be inaccurate. Consider using '#align convex_cone.map_id ConvexCone.map_idₓ'. -/
@[simp]
theorem map_id (S : ConvexCone 𝕜 E) : S.map LinearMap.id = S :=
  SetLike.coe_injective <| image_id _
#align convex_cone.map_id ConvexCone.map_id

#print ConvexCone.comap /-
/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : ConvexCone 𝕜 E
    where
  carrier := f ⁻¹' S
  smul_mem' c hc x hx := by
    rw [mem_preimage, f.map_smul c]
    exact S.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage, f.map_add]
    exact S.add_mem hx hy
#align convex_cone.comap ConvexCone.comap
-/

/- warning: convex_cone.coe_comap -> ConvexCone.coe_comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_comap ConvexCone.coe_comapₓ'. -/
@[simp]
theorem coe_comap (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 F) : (S.comap f : Set E) = f ⁻¹' S :=
  rfl
#align convex_cone.coe_comap ConvexCone.coe_comap

/- warning: convex_cone.comap_id -> ConvexCone.comap_id is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_5 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2] (S : ConvexCone.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2 _inst_5))))), Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2 _inst_5))))) (ConvexCone.comap.{u1, u2, u2} 𝕜 E E _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearMap.id.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))) _inst_2 _inst_5) S) S
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_5 : Module.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2] (S : ConvexCone.{u2, u1} 𝕜 E (OrderedCommSemiring.toOrderedSemiring.{u2} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1)))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_5))))), Eq.{succ u1} (ConvexCone.{u2, u1} 𝕜 E (OrderedCommSemiring.toOrderedSemiring.{u2} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1)))))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_5))))) (ConvexCone.comap.{u2, u1, u1} 𝕜 E E _inst_1 _inst_2 _inst_2 _inst_5 _inst_5 (LinearMap.id.{u2, u1} 𝕜 E (StrictOrderedSemiring.toSemiring.{u2} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u2} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u2} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))) _inst_2 _inst_5) S) S
Case conversion may be inaccurate. Consider using '#align convex_cone.comap_id ConvexCone.comap_idₓ'. -/
@[simp]
theorem comap_id (S : ConvexCone 𝕜 E) : S.comap LinearMap.id = S :=
  SetLike.coe_injective preimage_id
#align convex_cone.comap_id ConvexCone.comap_id

/- warning: convex_cone.comap_comap -> ConvexCone.comap_comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.comap_comap ConvexCone.comap_comapₓ'. -/
theorem comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : ConvexCone 𝕜 G) :
    (S.comap g).comap f = S.comap (g.comp f) :=
  SetLike.coe_injective <| preimage_comp.symm
#align convex_cone.comap_comap ConvexCone.comap_comap

/- warning: convex_cone.mem_comap -> ConvexCone.mem_comap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_comap ConvexCone.mem_comapₓ'. -/
@[simp]
theorem mem_comap {f : E →ₗ[𝕜] F} {S : ConvexCone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl
#align convex_cone.mem_comap ConvexCone.mem_comap

end Module

end AddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup E] [Module 𝕜 E]

/- warning: convex_cone.to_ordered_smul -> ConvexCone.to_orderedSMul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.to_ordered_smul ConvexCone.to_orderedSMulₓ'. -/
/-- Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
theorem to_orderedSMul (S : ConvexCone 𝕜 E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ S) : OrderedSMul 𝕜 E :=
  OrderedSMul.mk'
    (by
      intro x y z xy hz
      rw [h (z • x) (z • y), ← smul_sub z y x]
      exact smul_mem S hz ((h x y).mp xy.le))
#align convex_cone.to_ordered_smul ConvexCone.to_orderedSMul

end OrderedAddCommGroup

end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [SMul 𝕜 E] (S : ConvexCone 𝕜 E)

#print ConvexCone.Pointed /-
/-- A convex cone is pointed if it includes `0`. -/
def Pointed (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∈ S
#align convex_cone.pointed ConvexCone.Pointed
-/

#print ConvexCone.Blunt /-
/-- A convex cone is blunt if it doesn't include `0`. -/
def Blunt (S : ConvexCone 𝕜 E) : Prop :=
  (0 : E) ∉ S
#align convex_cone.blunt ConvexCone.Blunt
-/

/- warning: convex_cone.pointed_iff_not_blunt -> ConvexCone.pointed_iff_not_blunt is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3), Iff (ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Not (ConvexCone.Blunt.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] (S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3), Iff (ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Not (ConvexCone.Blunt.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S))
Case conversion may be inaccurate. Consider using '#align convex_cone.pointed_iff_not_blunt ConvexCone.pointed_iff_not_bluntₓ'. -/
theorem pointed_iff_not_blunt (S : ConvexCone 𝕜 E) : S.Pointed ↔ ¬S.Blunt :=
  ⟨fun h₁ h₂ => h₂ h₁, Classical.not_not.mp⟩
#align convex_cone.pointed_iff_not_blunt ConvexCone.pointed_iff_not_blunt

/- warning: convex_cone.blunt_iff_not_pointed -> ConvexCone.blunt_iff_not_pointed is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3), Iff (ConvexCone.Blunt.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Not (ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] (S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3), Iff (ConvexCone.Blunt.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Not (ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S))
Case conversion may be inaccurate. Consider using '#align convex_cone.blunt_iff_not_pointed ConvexCone.blunt_iff_not_pointedₓ'. -/
theorem blunt_iff_not_pointed (S : ConvexCone 𝕜 E) : S.Blunt ↔ ¬S.Pointed := by
  rw [pointed_iff_not_blunt, Classical.not_not]
#align convex_cone.blunt_iff_not_pointed ConvexCone.blunt_iff_not_pointed

/- warning: convex_cone.pointed.mono -> ConvexCone.Pointed.mono is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3} {T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3}, (LE.le.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Preorder.toHasLe.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.partialOrder.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) S T) -> (ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3} {T : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3}, (LE.le.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (Preorder.toLE.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instCompleteLatticeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))))) S T) -> (ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T)
Case conversion may be inaccurate. Consider using '#align convex_cone.pointed.mono ConvexCone.Pointed.monoₓ'. -/
theorem Pointed.mono {S T : ConvexCone 𝕜 E} (h : S ≤ T) : S.Pointed → T.Pointed :=
  @h _
#align convex_cone.pointed.mono ConvexCone.Pointed.mono

/- warning: convex_cone.blunt.anti -> ConvexCone.Blunt.anti is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3} {T : ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3}, (LE.le.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Preorder.toHasLe.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SetLike.partialOrder.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) T S) -> (ConvexCone.Blunt.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Blunt.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3} {T : ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3}, (LE.le.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (Preorder.toLE.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (PartialOrder.toPreorder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (ConvexCone.instCompleteLatticeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))))) T S) -> (ConvexCone.Blunt.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Blunt.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T)
Case conversion may be inaccurate. Consider using '#align convex_cone.blunt.anti ConvexCone.Blunt.antiₓ'. -/
theorem Blunt.anti {S T : ConvexCone 𝕜 E} (h : T ≤ S) : S.Blunt → T.Blunt :=
  (· ∘ @h)
#align convex_cone.blunt.anti ConvexCone.Blunt.anti

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup E] [SMul 𝕜 E] (S : ConvexCone 𝕜 E)

#print ConvexCone.Flat /-
/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def Flat : Prop :=
  ∃ x ∈ S, x ≠ (0 : E) ∧ -x ∈ S
#align convex_cone.flat ConvexCone.Flat
-/

#print ConvexCone.Salient /-
/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def Salient : Prop :=
  ∀ x ∈ S, x ≠ (0 : E) → -x ∉ S
#align convex_cone.salient ConvexCone.Salient
-/

/- warning: convex_cone.salient_iff_not_flat -> ConvexCone.salient_iff_not_flat is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] (S : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3), Iff (ConvexCone.Salient.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Not (ConvexCone.Flat.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] (S : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3), Iff (ConvexCone.Salient.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Not (ConvexCone.Flat.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S))
Case conversion may be inaccurate. Consider using '#align convex_cone.salient_iff_not_flat ConvexCone.salient_iff_not_flatₓ'. -/
theorem salient_iff_not_flat (S : ConvexCone 𝕜 E) : S.Salient ↔ ¬S.Flat :=
  by
  constructor
  · rintro h₁ ⟨x, xs, H₁, H₂⟩
    exact h₁ x xs H₁ H₂
  · intro h
    unfold flat at h
    push_neg  at h
    exact h
#align convex_cone.salient_iff_not_flat ConvexCone.salient_iff_not_flat

/- warning: convex_cone.flat.mono -> ConvexCone.Flat.mono is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3} {T : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3}, (LE.le.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (Preorder.toHasLe.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)))) S T) -> (ConvexCone.Flat.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Flat.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3} {T : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3}, (LE.le.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (Preorder.toLE.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (PartialOrder.toPreorder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (ConvexCone.instCompleteLatticeConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3))))) S T) -> (ConvexCone.Flat.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Flat.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T)
Case conversion may be inaccurate. Consider using '#align convex_cone.flat.mono ConvexCone.Flat.monoₓ'. -/
theorem Flat.mono {S T : ConvexCone 𝕜 E} (h : S ≤ T) : S.Flat → T.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩
#align convex_cone.flat.mono ConvexCone.Flat.mono

/- warning: convex_cone.salient.anti -> ConvexCone.Salient.anti is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3} {T : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3}, (LE.le.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (Preorder.toHasLe.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (PartialOrder.toPreorder.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (SetLike.partialOrder.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)))) T S) -> (ConvexCone.Salient.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Salient.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3} {T : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3}, (LE.le.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (Preorder.toLE.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (PartialOrder.toPreorder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (OmegaCompletePartialOrder.toPartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3) (ConvexCone.instCompleteLatticeConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3))))) T S) -> (ConvexCone.Salient.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Salient.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T)
Case conversion may be inaccurate. Consider using '#align convex_cone.salient.anti ConvexCone.Salient.antiₓ'. -/
theorem Salient.anti {S T : ConvexCone 𝕜 E} (h : T ≤ S) : S.Salient → T.Salient :=
  fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)
#align convex_cone.salient.anti ConvexCone.Salient.anti

/- warning: convex_cone.flat.pointed -> ConvexCone.Flat.pointed is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3}, (ConvexCone.Flat.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3 S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3}, (ConvexCone.Flat.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) -> (ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3 S)
Case conversion may be inaccurate. Consider using '#align convex_cone.flat.pointed ConvexCone.Flat.pointedₓ'. -/
/-- A flat cone is always pointed (contains `0`). -/
theorem Flat.pointed {S : ConvexCone 𝕜 E} (hS : S.Flat) : S.Pointed :=
  by
  obtain ⟨x, hx, _, hxneg⟩ := hS
  rw [pointed, ← add_neg_self x]
  exact add_mem S hx hxneg
#align convex_cone.flat.pointed ConvexCone.Flat.pointed

/- warning: convex_cone.blunt.salient -> ConvexCone.Blunt.salient is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : SMul.{u1, u2} 𝕜 E] {S : ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3}, (ConvexCone.Blunt.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3 S) -> (ConvexCone.Salient.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : SMul.{u2, u1} 𝕜 E] {S : ConvexCone.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3}, (ConvexCone.Blunt.{u2, u1} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u1} E _inst_2) _inst_3 S) -> (ConvexCone.Salient.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S)
Case conversion may be inaccurate. Consider using '#align convex_cone.blunt.salient ConvexCone.Blunt.salientₓ'. -/
/-- A blunt cone (one not containing `0`) is always salient. -/
theorem Blunt.salient {S : ConvexCone 𝕜 E} : S.Blunt → S.Salient :=
  by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt flat.pointed
#align convex_cone.blunt.salient ConvexCone.Blunt.salient

#print ConvexCone.toPreorder /-
/-- A pointed convex cone defines a preorder. -/
def toPreorder (h₁ : S.Pointed) : Preorder E
    where
  le x y := y - x ∈ S
  le_refl x := by change x - x ∈ S <;> rw [sub_self x] <;> exact h₁
  le_trans x y z xy zy := by simpa using add_mem S zy xy
#align convex_cone.to_preorder ConvexCone.toPreorder
-/

#print ConvexCone.toPartialOrder /-
/-- A pointed and salient cone defines a partial order. -/
def toPartialOrder (h₁ : S.Pointed) (h₂ : S.Salient) : PartialOrder E :=
  { toPreorder S h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a ≠ 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }
#align convex_cone.to_partial_order ConvexCone.toPartialOrder
-/

#print ConvexCone.toOrderedAddCommGroup /-
/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def toOrderedAddCommGroup (h₁ : S.Pointed) (h₂ : S.Salient) : OrderedAddCommGroup E :=
  { toPartialOrder S h₁ h₂, show AddCommGroup E by infer_instance with
    add_le_add_left := by
      intro a b hab c
      change c + b - (c + a) ∈ S
      rw [add_sub_add_left_eq_sub]
      exact hab }
#align convex_cone.to_ordered_add_comm_group ConvexCone.toOrderedAddCommGroup
-/

end AddCommGroup

section Module

variable [AddCommMonoid E] [Module 𝕜 E]

instance : Zero (ConvexCone 𝕜 E) :=
  ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩

/- warning: convex_cone.mem_zero -> ConvexCone.mem_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] (x : E), Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))))) x (OfNat.ofNat.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (OfNat.mk.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (Zero.zero.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.hasZero.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))) (Eq.{succ u2} E x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] (x : E), Iff (Membership.mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (SetLike.instMembership.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.instSetLikeConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))))) x (OfNat.ofNat.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (Zero.toOfNat0.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.instZeroConvexConeToSMulToZeroToAddMonoidToSMulZeroClassToZeroToMonoidWithZeroToSemiringToSMulWithZeroToMulActionWithZero.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (Eq.{succ u2} E x (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)))))
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_zero ConvexCone.mem_zeroₓ'. -/
@[simp]
theorem mem_zero (x : E) : x ∈ (0 : ConvexCone 𝕜 E) ↔ x = 0 :=
  Iff.rfl
#align convex_cone.mem_zero ConvexCone.mem_zero

#print ConvexCone.coe_zero /-
@[simp]
theorem coe_zero : ((0 : ConvexCone 𝕜 E) : Set E) = 0 :=
  rfl
#align convex_cone.coe_zero ConvexCone.coe_zero
-/

/- warning: convex_cone.pointed_zero -> ConvexCone.pointed_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2], ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))) (OfNat.ofNat.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (OfNat.mk.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (Zero.zero.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.hasZero.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2], ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3)))) (OfNat.ofNat.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (Zero.toOfNat0.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.instZeroConvexConeToSMulToZeroToAddMonoidToSMulZeroClassToZeroToMonoidWithZeroToSemiringToSMulWithZeroToMulActionWithZero.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align convex_cone.pointed_zero ConvexCone.pointed_zeroₓ'. -/
theorem pointed_zero : (0 : ConvexCone 𝕜 E).Pointed := by rw [pointed, mem_zero]
#align convex_cone.pointed_zero ConvexCone.pointed_zero

instance : Add (ConvexCone 𝕜 E) :=
  ⟨fun K₁ K₂ =>
    { carrier := { z | ∃ x y : E, x ∈ K₁ ∧ y ∈ K₂ ∧ x + y = z }
      smul_mem' := by
        rintro c hc _ ⟨x, y, hx, hy, rfl⟩
        rw [smul_add]
        use c • x, c • y, K₁.smul_mem hc hx, K₂.smul_mem hc hy
      add_mem' := by
        rintro _ ⟨x₁, x₂, hx₁, hx₂, rfl⟩ y ⟨y₁, y₂, hy₁, hy₂, rfl⟩
        use x₁ + y₁, x₂ + y₂, K₁.add_mem hx₁ hy₁, K₂.add_mem hx₂ hy₂
        abel }⟩

/- warning: convex_cone.mem_add -> ConvexCone.mem_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_add ConvexCone.mem_addₓ'. -/
@[simp]
theorem mem_add {K₁ K₂ : ConvexCone 𝕜 E} {a : E} :
    a ∈ K₁ + K₂ ↔ ∃ x y : E, x ∈ K₁ ∧ y ∈ K₂ ∧ x + y = a :=
  Iff.rfl
#align convex_cone.mem_add ConvexCone.mem_add

instance : AddZeroClass (ConvexCone 𝕜 E) :=
  ⟨0, Add.add, fun _ => by
    ext
    simp, fun _ => by
    ext
    simp⟩

instance : AddCommSemigroup (ConvexCone 𝕜 E)
    where
  add := Add.add
  add_assoc _ _ _ := SetLike.coe_injective <| Set.addCommSemigroup.add_assoc _ _ _
  add_comm _ _ := SetLike.coe_injective <| Set.addCommSemigroup.add_comm _ _

end Module

end OrderedSemiring

end ConvexCone

namespace Submodule

/-! ### Submodules are cones -/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [Module 𝕜 E]

#print Submodule.toConvexCone /-
/-- Every submodule is trivially a convex cone. -/
def toConvexCone (S : Submodule 𝕜 E) : ConvexCone 𝕜 E
    where
  carrier := S
  smul_mem' c hc x hx := S.smul_mem c hx
  add_mem' x hx y hy := S.add_mem hx hy
#align submodule.to_convex_cone Submodule.toConvexCone
-/

/- warning: submodule.coe_to_convex_cone -> Submodule.coe_toConvexCone is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] (S : Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3), Eq.{succ u2} (Set.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Set.{u2} E) (SetLike.Set.hasCoeT.{u2, u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) E (Submodule.setLike.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))) S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2] (S : Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3), Eq.{succ u1} (Set.{u1} E) (SetLike.coe.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S)) (SetLike.coe.{u1, u1} (Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) E (Submodule.setLike.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) S)
Case conversion may be inaccurate. Consider using '#align submodule.coe_to_convex_cone Submodule.coe_toConvexConeₓ'. -/
@[simp]
theorem coe_toConvexCone (S : Submodule 𝕜 E) : ↑S.toConvexCone = (S : Set E) :=
  rfl
#align submodule.coe_to_convex_cone Submodule.coe_toConvexCone

/- warning: submodule.mem_to_convex_cone -> Submodule.mem_toConvexCone is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] {x : E} {S : Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3}, Iff (Membership.Mem.{u2, u2} E (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (SetLike.hasMem.{u2, u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.setLike.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))))) x (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S)) (Membership.Mem.{u2, u2} E (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (SetLike.hasMem.{u2, u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) E (Submodule.setLike.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)) x S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2] {x : E} {S : Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3}, Iff (Membership.mem.{u1, u1} E (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) (SetLike.instMembership.{u1, u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) E (ConvexCone.instSetLikeConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3)))))) x (Submodule.toConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S)) (Membership.mem.{u1, u1} E (Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) E (Submodule.setLike.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3)) x S)
Case conversion may be inaccurate. Consider using '#align submodule.mem_to_convex_cone Submodule.mem_toConvexConeₓ'. -/
@[simp]
theorem mem_toConvexCone {x : E} {S : Submodule 𝕜 E} : x ∈ S.toConvexCone ↔ x ∈ S :=
  Iff.rfl
#align submodule.mem_to_convex_cone Submodule.mem_toConvexCone

/- warning: submodule.to_convex_cone_le_iff -> Submodule.toConvexCone_le_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.to_convex_cone_le_iff Submodule.toConvexCone_le_iffₓ'. -/
@[simp]
theorem toConvexCone_le_iff {S T : Submodule 𝕜 E} : S.toConvexCone ≤ T.toConvexCone ↔ S ≤ T :=
  Iff.rfl
#align submodule.to_convex_cone_le_iff Submodule.toConvexCone_le_iff

/- warning: submodule.to_convex_cone_bot -> Submodule.toConvexCone_bot is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2], Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Bot.bot.{u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Submodule.hasBot.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))) (OfNat.ofNat.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (OfNat.mk.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (Zero.zero.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.hasZero.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2], Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Bot.bot.{u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Submodule.instBotSubmodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))) (OfNat.ofNat.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) 0 (Zero.toOfNat0.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.instZeroConvexConeToSMulToZeroToAddMonoidToSMulZeroClassToZeroToMonoidWithZeroToSemiringToSMulWithZeroToMulActionWithZero.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align submodule.to_convex_cone_bot Submodule.toConvexCone_botₓ'. -/
@[simp]
theorem toConvexCone_bot : (⊥ : Submodule 𝕜 E).toConvexCone = 0 :=
  rfl
#align submodule.to_convex_cone_bot Submodule.toConvexCone_bot

/- warning: submodule.to_convex_cone_top -> Submodule.toConvexCone_top is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2], Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Top.top.{u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Submodule.hasTop.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))) (Top.top.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.hasTop.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2], Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Top.top.{u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Submodule.instTopSubmodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))) (Top.top.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.instTopConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2)) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))))
Case conversion may be inaccurate. Consider using '#align submodule.to_convex_cone_top Submodule.toConvexCone_topₓ'. -/
@[simp]
theorem toConvexCone_top : (⊤ : Submodule 𝕜 E).toConvexCone = ⊤ :=
  rfl
#align submodule.to_convex_cone_top Submodule.toConvexCone_top

/- warning: submodule.to_convex_cone_inf -> Submodule.toConvexCone_inf is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] (S : Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (T : Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3), Eq.{succ u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Inf.inf.{u2} (Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (Submodule.hasInf.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3) S T)) (Inf.inf.{u2} (ConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.hasInf.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2] (S : Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) (T : Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3), Eq.{succ u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 (Inf.inf.{u1} (Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) (Submodule.instInfSubmodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3) S T)) (Inf.inf.{u1} (ConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) (ConvexCone.instInfConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3))))) (Submodule.toConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S) (Submodule.toConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T))
Case conversion may be inaccurate. Consider using '#align submodule.to_convex_cone_inf Submodule.toConvexCone_infₓ'. -/
@[simp]
theorem toConvexCone_inf (S T : Submodule 𝕜 E) :
    (S ⊓ T).toConvexCone = S.toConvexCone ⊓ T.toConvexCone :=
  rfl
#align submodule.to_convex_cone_inf Submodule.toConvexCone_inf

/- warning: submodule.pointed_to_convex_cone -> Submodule.pointed_toConvexCone is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2] (S : Submodule.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3), ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E _inst_2))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) _inst_2 _inst_3)))) (Submodule.toConvexCone.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 S)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2] (S : Submodule.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3), ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E _inst_2)) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) _inst_2 _inst_3)))) (Submodule.toConvexCone.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 S)
Case conversion may be inaccurate. Consider using '#align submodule.pointed_to_convex_cone Submodule.pointed_toConvexConeₓ'. -/
@[simp]
theorem pointed_toConvexCone (S : Submodule 𝕜 E) : S.toConvexCone.Pointed :=
  S.zero_mem
#align submodule.pointed_to_convex_cone Submodule.pointed_toConvexCone

end AddCommMonoid

end OrderedSemiring

end Submodule

namespace ConvexCone

/-! ### Positive cone of an ordered module -/


section PositiveCone

variable (𝕜 E) [OrderedSemiring 𝕜] [OrderedAddCommGroup E] [Module 𝕜 E] [OrderedSMul 𝕜 E]

/- warning: convex_cone.positive -> ConvexCone.positive is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))], ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))))
but is expected to have type
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) _inst_3))], ConvexCone.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) _inst_3))))
Case conversion may be inaccurate. Consider using '#align convex_cone.positive ConvexCone.positiveₓ'. -/
/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive : ConvexCone 𝕜 E where
  carrier := Set.Ici 0
  smul_mem' c hc x (hx : _ ≤ _) := smul_nonneg hc.le hx
  add_mem' x (hx : _ ≤ _) y (hy : _ ≤ _) := add_nonneg hx hy
#align convex_cone.positive ConvexCone.positive

/- warning: convex_cone.mem_positive -> ConvexCone.mem_positive is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_positive ConvexCone.mem_positiveₓ'. -/
@[simp]
theorem mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x :=
  Iff.rfl
#align convex_cone.mem_positive ConvexCone.mem_positive

/- warning: convex_cone.coe_positive -> ConvexCone.coe_positive is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_positive ConvexCone.coe_positiveₓ'. -/
@[simp]
theorem coe_positive : ↑(positive 𝕜 E) = Set.Ici (0 : E) :=
  rfl
#align convex_cone.coe_positive ConvexCone.coe_positive

/- warning: convex_cone.salient_positive -> ConvexCone.salient_positive is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))], ConvexCone.Salient.{u1, u2} 𝕜 E _inst_1 (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3)))) (ConvexCone.positive.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
but is expected to have type
  forall (𝕜 : Type.{u2}) (E : Type.{u1}) [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : OrderedAddCommGroup.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))] [_inst_4 : OrderedSMul.{u2, u1} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (OrderedAddCommMonoid.toAddCommMonoid.{u1} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3))], ConvexCone.Salient.{u2, u1} 𝕜 E _inst_1 (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2) (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3)))) (ConvexCone.positive.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align convex_cone.salient_positive ConvexCone.salient_positiveₓ'. -/
/-- The positive cone of an ordered module is always salient. -/
theorem salient_positive : Salient (positive 𝕜 E) := fun x xs hx hx' =>
  lt_irrefl (0 : E)
    (calc
      0 < x := lt_of_le_of_ne xs hx.symm
      _ ≤ x + -x := (le_add_of_nonneg_right hx')
      _ = 0 := add_neg_self x
      )
#align convex_cone.salient_positive ConvexCone.salient_positive

/- warning: convex_cone.pointed_positive -> ConvexCone.pointed_positive is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))], ConvexCone.Pointed.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3)))) (ConvexCone.positive.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
but is expected to have type
  forall (𝕜 : Type.{u2}) (E : Type.{u1}) [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : OrderedAddCommGroup.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))] [_inst_4 : OrderedSMul.{u2, u1} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (OrderedAddCommMonoid.toAddCommMonoid.{u1} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3))], ConvexCone.Pointed.{u2, u1} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3)))) (ConvexCone.positive.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align convex_cone.pointed_positive ConvexCone.pointed_positiveₓ'. -/
/-- The positive cone of an ordered module is always pointed. -/
theorem pointed_positive : Pointed (positive 𝕜 E) :=
  le_refl 0
#align convex_cone.pointed_positive ConvexCone.pointed_positive

/- warning: convex_cone.strictly_positive -> ConvexCone.strictlyPositive is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))], ConvexCone.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))))
but is expected to have type
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddMonoid.toZero.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) _inst_3))], ConvexCone.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (MonoidWithZero.toZero.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) _inst_3))))
Case conversion may be inaccurate. Consider using '#align convex_cone.strictly_positive ConvexCone.strictlyPositiveₓ'. -/
/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`convex_cone.positive`) being established terminology for the non-negative elements. -/
def strictlyPositive : ConvexCone 𝕜 E
    where
  carrier := Set.Ioi 0
  smul_mem' c hc x (hx : _ < _) := smul_pos hc hx
  add_mem' x hx y hy := add_pos hx hy
#align convex_cone.strictly_positive ConvexCone.strictlyPositive

/- warning: convex_cone.mem_strictly_positive -> ConvexCone.mem_strictlyPositive is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.mem_strictly_positive ConvexCone.mem_strictlyPositiveₓ'. -/
@[simp]
theorem mem_strictlyPositive {x : E} : x ∈ strictlyPositive 𝕜 E ↔ 0 < x :=
  Iff.rfl
#align convex_cone.mem_strictly_positive ConvexCone.mem_strictlyPositive

/- warning: convex_cone.coe_strictly_positive -> ConvexCone.coe_strictlyPositive is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.coe_strictly_positive ConvexCone.coe_strictlyPositiveₓ'. -/
@[simp]
theorem coe_strictlyPositive : ↑(strictlyPositive 𝕜 E) = Set.Ioi (0 : E) :=
  rfl
#align convex_cone.coe_strictly_positive ConvexCone.coe_strictlyPositive

/- warning: convex_cone.positive_le_strictly_positive -> ConvexCone.positive_le_strictlyPositive is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_cone.positive_le_strictly_positive ConvexCone.positive_le_strictlyPositiveₓ'. -/
theorem positive_le_strictlyPositive : strictlyPositive 𝕜 E ≤ positive 𝕜 E := fun x => le_of_lt
#align convex_cone.positive_le_strictly_positive ConvexCone.positive_le_strictlyPositive

/- warning: convex_cone.salient_strictly_positive -> ConvexCone.salient_strictlyPositive is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))], ConvexCone.Salient.{u1, u2} 𝕜 E _inst_1 (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3)))) (ConvexCone.strictlyPositive.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
but is expected to have type
  forall (𝕜 : Type.{u2}) (E : Type.{u1}) [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : OrderedAddCommGroup.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))] [_inst_4 : OrderedSMul.{u2, u1} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (OrderedAddCommMonoid.toAddCommMonoid.{u1} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3))], ConvexCone.Salient.{u2, u1} 𝕜 E _inst_1 (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2) (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3)))) (ConvexCone.strictlyPositive.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align convex_cone.salient_strictly_positive ConvexCone.salient_strictlyPositiveₓ'. -/
/-- The strictly positive cone of an ordered module is always salient. -/
theorem salient_strictlyPositive : Salient (strictlyPositive 𝕜 E) :=
  (salient_positive 𝕜 E).anti <| positive_le_strictlyPositive 𝕜 E
#align convex_cone.salient_strictly_positive ConvexCone.salient_strictlyPositive

/- warning: convex_cone.blunt_strictly_positive -> ConvexCone.blunt_strictlyPositive is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : OrderedAddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))] [_inst_4 : OrderedSMul.{u1, u2} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (OrderedAddCommMonoid.toAddCommMonoid.{u2} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u2} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3))], ConvexCone.Blunt.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1)) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E (OrderedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) _inst_3)))) (ConvexCone.strictlyPositive.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
but is expected to have type
  forall (𝕜 : Type.{u2}) (E : Type.{u1}) [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : OrderedAddCommGroup.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))] [_inst_4 : OrderedSMul.{u2, u1} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (AddMonoid.toZero.{u1} E (AddCommMonoid.toAddMonoid.{u1} E (OrderedAddCommMonoid.toAddCommMonoid.{u1} E (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3))], ConvexCone.Blunt.{u2, u1} 𝕜 E _inst_1 (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (MonoidWithZero.toZero.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1)) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (OrderedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (OrderedCancelAddCommMonoid.toAddCommMonoid.{u1} E (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u1} E _inst_2)) _inst_3)))) (ConvexCone.strictlyPositive.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4)
Case conversion may be inaccurate. Consider using '#align convex_cone.blunt_strictly_positive ConvexCone.blunt_strictlyPositiveₓ'. -/
/-- The strictly positive cone of an ordered module is always blunt. -/
theorem blunt_strictlyPositive : Blunt (strictlyPositive 𝕜 E) :=
  lt_irrefl 0
#align convex_cone.blunt_strictly_positive ConvexCone.blunt_strictlyPositive

end PositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Convex

#print Convex.toCone /-
/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def toCone (s : Set E) (hs : Convex 𝕜 s) : ConvexCone 𝕜 E :=
  by
  apply ConvexCone.mk (⋃ (c : 𝕜) (H : 0 < c), c • s) <;> simp only [mem_Union, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine' ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left _ this.ne']
#align convex.to_cone Convex.toCone
-/

variable {s : Set E} (hs : Convex 𝕜 s) {x : E}

/- warning: convex.mem_to_cone -> Convex.mem_toCone is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex.mem_to_cone Convex.mem_toConeₓ'. -/
theorem mem_toCone : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ ∃ y ∈ s, c • y = x := by
  simp only [to_cone, ConvexCone.mem_mk, mem_Union, mem_smul_set, eq_comm, exists_prop]
#align convex.mem_to_cone Convex.mem_toCone

/- warning: convex.mem_to_cone' -> Convex.mem_to_cone' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex.mem_to_cone' Convex.mem_to_cone'ₓ'. -/
theorem mem_to_cone' : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ c • x ∈ s :=
  by
  refine' hs.mem_to_cone.trans ⟨_, _⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩
#align convex.mem_to_cone' Convex.mem_to_cone'

#print Convex.subset_toCone /-
theorem subset_toCone : s ⊆ hs.toCone s := fun x hx =>
  hs.mem_to_cone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩
#align convex.subset_to_cone Convex.subset_toCone
-/

/- warning: convex.to_cone_is_least -> Convex.toCone_isLeast is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex.to_cone_is_least Convex.toCone_isLeastₓ'. -/
/-- `hs.to_cone s` is the least cone that includes `s`. -/
theorem toCone_isLeast : IsLeast { t : ConvexCone 𝕜 E | s ⊆ t } (hs.toCone s) :=
  by
  refine' ⟨hs.subset_to_cone, fun t ht x hx => _⟩
  rcases hs.mem_to_cone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)
#align convex.to_cone_is_least Convex.toCone_isLeast

#print Convex.toCone_eq_sInf /-
theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone 𝕜 E | s ⊆ t } :=
  hs.toCone_isLeast.IsGLB.sInf_eq.symm
#align convex.to_cone_eq_Inf Convex.toCone_eq_sInf
-/

end Convex

/- warning: convex_hull_to_cone_is_least -> convexHull_toCone_isLeast is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex_hull_to_cone_is_least convexHull_toCone_isLeastₓ'. -/
theorem convexHull_toCone_isLeast (s : Set E) :
    IsLeast { t : ConvexCone 𝕜 E | s ⊆ t } ((convex_convexHull 𝕜 s).toCone _) :=
  by
  convert(convex_convexHull 𝕜 s).toCone_isLeast
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩
#align convex_hull_to_cone_is_least convexHull_toCone_isLeast

#print convexHull_toCone_eq_sInf /-
theorem convexHull_toCone_eq_sInf (s : Set E) :
    (convex_convexHull 𝕜 s).toCone _ = sInf { t : ConvexCone 𝕜 E | s ⊆ t } :=
  Eq.symm <| IsGLB.sInf_eq <| IsLeast.isGLB <| convexHull_toCone_isLeast s
#align convex_hull_to_cone_eq_Inf convexHull_toCone_eq_sInf
-/

end ConeFromConvex

/-!
### M. Riesz extension theorem

Given a convex cone `s` in a vector space `E`, a submodule `p`, and a linear `f : p → ℝ`, assume
that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then there exists a globally defined linear
function `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.

We prove this theorem using Zorn's lemma. `riesz_extension.step` is the main part of the proof.
It says that if the domain `p` of `f` is not the whole space, then `f` can be extended to a larger
subspace `p ⊔ span ℝ {y}` without breaking the non-negativity condition.

In `riesz_extension.exists_top` we use Zorn's lemma to prove that we can extend `f`
to a linear map `g` on `⊤ : submodule E`. Mathematically this is the same as a linear map on `E`
but in Lean `⊤ : submodule E` is isomorphic but is not equal to `E`. In `riesz_extension`
we use this isomorphism to prove the theorem.
-/


variable [AddCommGroup E] [Module ℝ E]

namespace riesz_extension

open Submodule

variable (s : ConvexCone ℝ E) (f : E →ₗ.[ℝ] ℝ)

/- warning: riesz_extension.step -> RieszExtension.step is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align riesz_extension.step RieszExtension.stepₓ'. -/
/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
theorem step (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x :=
  by
  obtain ⟨y, -, hy⟩ : ∃ (y : E)(h : y ∈ ⊤), y ∉ f.domain :=
    @SetLike.exists_of_lt (Submodule ℝ E) _ _ _ _ (lt_top_iff_ne_top.2 hdom)
  obtain ⟨c, le_c, c_le⟩ :
    ∃ c, (∀ x : f.domain, -(x : E) - y ∈ s → f x ≤ c) ∧ ∀ x : f.domain, (x : E) + y ∈ s → c ≤ f x :=
    by
    set Sp := f '' { x : f.domain | (x : E) + y ∈ s }
    set Sn := f '' { x : f.domain | -(x : E) - y ∈ s }
    suffices (upperBounds Sn ∩ lowerBounds Sp).Nonempty by
      simpa only [Set.Nonempty, upperBounds, lowerBounds, ball_image_iff] using this
    refine' exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (Dense y)) _
    · rcases Dense (-y) with ⟨x, hx⟩
      rw [← neg_neg x, AddSubgroupClass.coe_neg, ← sub_eq_add_neg] at hx
      exact ⟨_, hx⟩
    rintro a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩
    have := s.add_mem hxp hxn
    rw [add_assoc, add_sub_cancel'_right, ← sub_eq_add_neg, ← AddSubgroupClass.coe_sub] at this
    replace := nonneg _ this
    rwa [f.map_sub, sub_nonneg] at this
  have hy' : y ≠ 0 := fun hy₀ => hy (hy₀.symm ▸ zero_mem _)
  refine' ⟨f.sup_span_singleton y (-c) hy, _, _⟩
  · refine' lt_iff_le_not_le.2 ⟨f.left_le_sup _ _, fun H => _⟩
    replace H := linear_pmap.domain_mono.monotone H
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, span_le, singleton_subset_iff] at H
    exact hy H.2
  · rintro ⟨z, hz⟩ hzs
    rcases mem_sup.1 hz with ⟨x, hx, y', hy', rfl⟩
    rcases mem_span_singleton.1 hy' with ⟨r, rfl⟩
    simp only [Subtype.coe_mk] at hzs
    erw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hx, smul_neg, ← sub_eq_add_neg, sub_nonneg]
    rcases lt_trichotomy r 0 with (hr | hr | hr)
    · have : -(r⁻¹ • x) - y ∈ s := by
        rwa [← s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_neg, smul_smul,
          mul_inv_cancel hr.ne, one_smul, sub_eq_add_neg, neg_smul, neg_neg]
      replace := le_c (r⁻¹ • ⟨x, hx⟩) this
      rwa [← mul_le_mul_left (neg_pos.2 hr), neg_mul, neg_mul, neg_le_neg_iff, f.map_smul,
        smul_eq_mul, ← mul_assoc, mul_inv_cancel hr.ne, one_mul] at this
    · subst r
      simp only [zero_smul, add_zero] at hzs⊢
      apply nonneg
      exact hzs
    · have : r⁻¹ • x + y ∈ s := by
        rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel hr.ne', one_smul]
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this
      rwa [← mul_le_mul_left hr, f.map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel hr.ne',
        one_mul] at this
#align riesz_extension.step RieszExtension.step

/- warning: riesz_extension.exists_top -> RieszExtension.exists_top is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align riesz_extension.exists_top RieszExtension.exists_topₓ'. -/
theorem exists_top (p : E →ₗ.[ℝ] ℝ) (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
    (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
    ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x :=
  by
  replace hp_nonneg : p ∈ { p | _ };
  · rw [mem_set_of_eq]
    exact hp_nonneg
  obtain ⟨q, hqs, hpq, hq⟩ := zorn_nonempty_partialOrder₀ _ _ _ hp_nonneg
  · refine' ⟨q, hpq, _, hqs⟩
    contrapose! hq
    rcases step s q hqs _ hq with ⟨r, hqr, hr⟩
    · exact ⟨r, hr, hqr.le, hqr.ne'⟩
    ·
      exact fun y =>
        let ⟨x, hx⟩ := hp_dense y
        ⟨of_le hpq.left x, hx⟩
  · intro c hcs c_chain y hy
    clear hp_nonneg hp_dense p
    have cne : c.nonempty := ⟨y, hy⟩
    refine'
      ⟨LinearPMap.sSup c c_chain.directed_on, _, fun _ => LinearPMap.le_sSup c_chain.directed_on⟩
    rintro ⟨x, hx⟩ hxs
    have hdir : DirectedOn (· ≤ ·) (LinearPMap.domain '' c) :=
      directedOn_image.2 (c_chain.directed_on.mono linear_pmap.domain_mono.monotone)
    rcases(mem_Sup_of_directed (cne.image _) hdir).1 hx with ⟨_, ⟨f, hfc, rfl⟩, hfx⟩
    have : f ≤ LinearPMap.sSup c c_chain.directed_on := LinearPMap.le_sSup _ hfc
    convert← hcs hfc ⟨x, hfx⟩ hxs
    apply this.2
    rfl
#align riesz_extension.exists_top RieszExtension.exists_top

end riesz_extension

/- warning: riesz_extension -> riesz_extension is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align riesz_extension riesz_extensionₓ'. -/
/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem riesz_extension (s : ConvexCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
    (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x :=
  by
  rcases RieszExtension.exists_top s f nonneg Dense with ⟨⟨g_dom, g⟩, ⟨hpg, hfg⟩, htop, hgs⟩
  clear hpg
  refine' ⟨g ∘ₗ ↑(LinearEquiv.ofTop _ htop).symm, _, _⟩ <;>
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.ofTop_symm_apply]
  · exact fun x => (hfg (Submodule.coe_mk _ _).symm).symm
  · exact fun x hx => hgs ⟨x, _⟩ hx
#align riesz_extension riesz_extension

/- warning: exists_extension_of_le_sublinear -> exists_extension_of_le_sublinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exists_extension_of_le_sublinear exists_extension_of_le_sublinearₓ'. -/
/-- **Hahn-Banach theorem**: if `N : E → ℝ` is a sublinear map, `f` is a linear map
defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
for all `x`. -/
theorem exists_extension_of_le_sublinear (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x) (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  by
  let s : ConvexCone ℝ (E × ℝ) :=
    { carrier := { p : E × ℝ | N p.1 ≤ p.2 }
      smul_mem' := fun c hc p hp =>
        calc
          N (c • p.1) = c * N p.1 := N_hom c hc p.1
          _ ≤ c * p.2 := mul_le_mul_of_nonneg_left hp hc.le
          
      add_mem' := fun x hx y hy => (N_add _ _).trans (add_le_add hx hy) }
  obtain ⟨g, g_eq, g_nonneg⟩ := riesz_extension s ((-f).coprod (linear_map.id.to_pmap ⊤)) _ _ <;>
    try
      simp only [LinearPMap.coprod_apply, to_pmap_apply, id_apply, LinearPMap.neg_apply, ←
        sub_eq_neg_add, sub_nonneg, Subtype.coe_mk] at *
  replace g_eq : ∀ (x : f.domain) (y : ℝ), g (x, y) = y - f x
  · intro x y
    simpa only [Subtype.coe_mk, Subtype.coe_eta] using g_eq ⟨(x, y), ⟨x.2, trivial⟩⟩
  · refine' ⟨-g.comp (inl ℝ E ℝ), _, _⟩ <;> simp only [neg_apply, inl_apply, comp_apply]
    · intro x
      simp [g_eq x 0]
    · intro x
      have A : (x, N x) = (x, 0) + (0, N x) := by simp
      have B := g_nonneg ⟨x, N x⟩ (le_refl (N x))
      rw [A, map_add, ← neg_le_iff_add_nonneg'] at B
      have C := g_eq 0 (N x)
      simp only [Submodule.coe_zero, f.map_zero, sub_zero] at C
      rwa [← C]
  · exact fun x hx => le_trans (hf _) hx
  · rintro ⟨x, y⟩
    refine' ⟨⟨(0, N x - y), ⟨f.domain.zero_mem, trivial⟩⟩, _⟩
    simp only [ConvexCone.mem_mk, mem_set_of_eq, Subtype.coe_mk, Prod.fst_add, Prod.snd_add,
      zero_add, sub_add_cancel]
#align exists_extension_of_le_sublinear exists_extension_of_le_sublinear

