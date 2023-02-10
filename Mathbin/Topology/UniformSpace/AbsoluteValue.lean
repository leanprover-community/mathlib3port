/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.uniform_space.absolute_value
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.AbsoluteValue
import Mathbin.Topology.UniformSpace.Basic

/-!
# Uniform structure induced by an absolute value

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build a uniform space structure on a commutative ring `R` equipped with an absolute value into
a linear ordered field `𝕜`. Of course in the case `R` is `ℚ`, `ℝ` or `ℂ` and
`𝕜 = ℝ`, we get the same thing as the metric space construction, and the general construction
follows exactly the same path.

## Implementation details

Note that we import `data.real.cau_seq` because this is where absolute values are defined, but
the current file does not depend on real numbers. TODO: extract absolute values from that
`data.real` folder.

## References

* [N. Bourbaki, *Topologie générale*][bourbaki1966]

## Tags

absolute value, uniform spaces
-/


open Set Function Filter UniformSpace

open Filter

namespace IsAbsoluteValue

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

variable {R : Type _} [CommRing R] (abv : R → 𝕜) [IsAbsoluteValue abv]

#print IsAbsoluteValue.uniformSpaceCore /-
/-- The uniformity coming from an absolute value. -/
def uniformSpaceCore : UniformSpace.Core R
    where
  uniformity := ⨅ ε > 0, 𝓟 { p : R × R | abv (p.2 - p.1) < ε }
  refl :=
    le_infᵢ fun ε =>
      le_infᵢ fun ε_pos =>
        principal_mono.2 fun ⟨x, y⟩ h => by simpa [show x = y from h, abv_zero abv]
  symm :=
    tendsto_infᵢ.2 fun ε =>
      tendsto_infᵢ.2 fun h =>
        tendsto_infᵢ' ε <|
          tendsto_infᵢ' h <|
            tendsto_principal_principal.2 fun ⟨x, y⟩ h =>
              by
              have h : abv (y - x) < ε := by simpa [-sub_eq_add_neg] using h
              rwa [abv_sub abv] at h
  comp :=
    le_infᵢ fun ε =>
      le_infᵢ fun h =>
        lift'_le
            (mem_infᵢ_of_mem (ε / 2) <| mem_infᵢ_of_mem (div_pos h zero_lt_two) (Subset.refl _)) <|
          by
          have : ∀ a b c : R, abv (c - a) < ε / 2 → abv (b - c) < ε / 2 → abv (b - a) < ε :=
            fun a b c hac hcb =>
            calc
              abv (b - a) ≤ _ := abv_sub_le abv b c a
              _ = abv (c - a) + abv (b - c) := add_comm _ _
              _ < ε / 2 + ε / 2 := add_lt_add hac hcb
              _ = ε := by rw [div_add_div_same, add_self_div_two]
              
          simpa [compRel]
#align is_absolute_value.uniform_space_core IsAbsoluteValue.uniformSpaceCore
-/

#print IsAbsoluteValue.uniformSpace /-
/-- The uniform structure coming from an absolute value. -/
def uniformSpace : UniformSpace R :=
  UniformSpace.ofCore (uniformSpaceCore abv)
#align is_absolute_value.uniform_space IsAbsoluteValue.uniformSpace
-/

/- warning: is_absolute_value.mem_uniformity -> IsAbsoluteValue.mem_uniformity is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] (abv : R -> 𝕜) [_inst_3 : IsAbsoluteValue.{u1, u2} 𝕜 (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) abv] {s : Set.{u2} (Prod.{u2, u2} R R)}, Iff (Membership.Mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} R R)) (Filter.{u2} (Prod.{u2, u2} R R)) (Filter.hasMem.{u2} (Prod.{u2, u2} R R)) s (UniformSpace.Core.uniformity.{u2} R (IsAbsoluteValue.uniformSpaceCore.{u1, u2} 𝕜 _inst_1 R _inst_2 abv _inst_3))) (Exists.{succ u1} 𝕜 (fun (ε : 𝕜) => Exists.{0} (GT.gt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) ε (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))))))))) (fun (H : GT.gt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) ε (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))))))))) => forall {a : R} {b : R}, (LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u1} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))))) (abv (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (SubNegMonoid.toHasSub.{u2} R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R (NonAssocRing.toAddGroupWithOne.{u2} R (Ring.toNonAssocRing.{u2} R (CommRing.toRing.{u2} R _inst_2))))))) b a)) ε) -> (Membership.Mem.{u2, u2} (Prod.{u2, u2} R R) (Set.{u2} (Prod.{u2, u2} R R)) (Set.hasMem.{u2} (Prod.{u2, u2} R R)) (Prod.mk.{u2, u2} R R a b) s))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {R : Type.{u2}} [_inst_2 : CommRing.{u2} R] (abv : R -> 𝕜) [_inst_3 : IsAbsoluteValue.{u1, u2} 𝕜 (OrderedCommSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u1} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u1} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))) R (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_2)) abv] {s : Set.{u2} (Prod.{u2, u2} R R)}, Iff (Membership.mem.{u2, u2} (Set.{u2} (Prod.{u2, u2} R R)) (Filter.{u2} (Prod.{u2, u2} R R)) (instMembershipSetFilter.{u2} (Prod.{u2, u2} R R)) s (UniformSpace.Core.uniformity.{u2} R (IsAbsoluteValue.uniformSpaceCore.{u1, u2} 𝕜 _inst_1 R _inst_2 abv _inst_3))) (Exists.{succ u1} 𝕜 (fun (ε : 𝕜) => And (GT.gt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) ε (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1)))))))) (forall {a : R} {b : R}, (LT.lt.{u1} 𝕜 (Preorder.toLT.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (abv (HSub.hSub.{u2, u2, u2} R R R (instHSub.{u2} R (Ring.toSub.{u2} R (CommRing.toRing.{u2} R _inst_2))) b a)) ε) -> (Membership.mem.{u2, u2} (Prod.{u2, u2} R R) (Set.{u2} (Prod.{u2, u2} R R)) (Set.instMembershipSet.{u2} (Prod.{u2, u2} R R)) (Prod.mk.{u2, u2} R R a b) s))))
Case conversion may be inaccurate. Consider using '#align is_absolute_value.mem_uniformity IsAbsoluteValue.mem_uniformityₓ'. -/
theorem mem_uniformity {s : Set (R × R)} :
    s ∈ (uniformSpaceCore abv).uniformity ↔ ∃ ε > 0, ∀ {a b : R}, abv (b - a) < ε → (a, b) ∈ s :=
  by
  suffices (s ∈ ⨅ ε : { ε : 𝕜 // ε > 0 }, 𝓟 { p : R × R | abv (p.2 - p.1) < ε.val }) ↔ _
    by
    rw [infᵢ_subtype] at this
    exact this
  rw [mem_infi_of_directed]
  · simp [subset_def]
  · rintro ⟨r, hr⟩ ⟨p, hp⟩
    exact
      ⟨⟨min r p, lt_min hr hp⟩, by simp (config := { contextual := true }) [lt_min_iff, (· ≥ ·)]⟩
#align is_absolute_value.mem_uniformity IsAbsoluteValue.mem_uniformity

end IsAbsoluteValue

