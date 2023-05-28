/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.mazur_ulam
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.RealVectorSpace
import Mathbin.Analysis.NormedSpace.AffineIsometry

/-!
# Mazur-Ulam Theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Mazur-Ulam theorem states that an isometric bijection between two normed affine spaces over `ℝ` is
affine. We formalize it in three definitions:

* `isometry_equiv.to_real_linear_isometry_equiv_of_map_zero` : given `E ≃ᵢ F` sending `0` to `0`,
  returns `E ≃ₗᵢ[ℝ] F` with the same `to_fun` and `inv_fun`;
* `isometry_equiv.to_real_linear_isometry_equiv` : given `f : E ≃ᵢ F`, returns a linear isometry
  equivalence `g : E ≃ₗᵢ[ℝ] F` with `g x = f x - f 0`.
* `isometry_equiv.to_real_affine_isometry_equiv` : given `f : PE ≃ᵢ PF`, returns an affine isometry
  equivalence `g : PE ≃ᵃⁱ[ℝ] PF` whose underlying `isometry_equiv` is `f`

The formalization is based on [Jussi Väisälä, *A Proof of the Mazur-Ulam Theorem*][Vaisala_2003].

## Tags

isometry, affine map, linear map
-/


variable {E PE F PF : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace PE]
  [NormedAddTorsor E PE] [NormedAddCommGroup F] [NormedSpace ℝ F] [MetricSpace PF]
  [NormedAddTorsor F PF]

open Set AffineMap AffineIsometryEquiv

noncomputable section

namespace IsometryEquiv

include E

/- warning: isometry_equiv.midpoint_fixed -> IsometryEquiv.midpoint_fixed is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {PE : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : MetricSpace.{u2} PE] [_inst_4 : NormedAddTorsor.{u1, u2} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)] {x : PE} {y : PE} (e : IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))), (Eq.{succ u2} PE (coeFn.{succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) (fun (_x : IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) => PE -> PE) (IsometryEquiv.hasCoeToFun.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) e x) x) -> (Eq.{succ u2} PE (coeFn.{succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) (fun (_x : IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) => PE -> PE) (IsometryEquiv.hasCoeToFun.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) e y) y) -> (Eq.{succ u2} PE (coeFn.{succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) (fun (_x : IsometryEquiv.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) => PE -> PE) (IsometryEquiv.hasCoeToFun.{u2, u2} PE PE (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3))) e (midpoint.{0, u1, u2} Real E PE Real.ring (invertibleTwo.{0} Real Real.divisionRing (StrictOrderedSemiring.to_charZero.{0} Real Real.strictOrderedSemiring)) (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedAddTorsor.toAddTorsor'.{u1, u2} E PE _inst_1 _inst_3 _inst_4) x y)) (midpoint.{0, u1, u2} Real E PE Real.ring (invertibleTwo.{0} Real Real.divisionRing (StrictOrderedSemiring.to_charZero.{0} Real Real.strictOrderedSemiring)) (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedAddTorsor.toAddTorsor'.{u1, u2} E PE _inst_1 _inst_3 _inst_4) x y))
but is expected to have type
  forall {E : Type.{u1}} {PE : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : MetricSpace.{u2} PE] [_inst_4 : NormedAddTorsor.{u1, u2} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)] {x : PE} {y : PE} (e : IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))), (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : PE) => PE) x) (FunLike.coe.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE (fun (_x : PE) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : PE) => PE) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE PE (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE PE (IsometryEquiv.instEquivLikeIsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))))) e x) x) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : PE) => PE) y) (FunLike.coe.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE (fun (_x : PE) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : PE) => PE) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE PE (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE PE (IsometryEquiv.instEquivLikeIsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))))) e y) y) -> (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : PE) => PE) (midpoint.{0, u1, u2} Real E PE Real.instRingReal (invertibleTwo.{0} Real Real.instDivisionRingReal (StrictOrderedSemiring.to_charZero.{0} Real Real.strictOrderedSemiring)) (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3) _inst_4) x y)) (FunLike.coe.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE (fun (_x : PE) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : PE) => PE) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE PE (EquivLike.toEmbeddingLike.{succ u2, succ u2, succ u2} (IsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))) PE PE (IsometryEquiv.instEquivLikeIsometryEquiv.{u2, u2} PE PE (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toEMetricSpace.{u2} PE _inst_3))))) e (midpoint.{0, u1, u2} Real E PE Real.instRingReal (invertibleTwo.{0} Real Real.instDivisionRingReal (StrictOrderedSemiring.to_charZero.{0} Real Real.strictOrderedSemiring)) (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3) _inst_4) x y)) (midpoint.{0, u1, u2} Real E PE Real.instRingReal (invertibleTwo.{0} Real Real.instDivisionRingReal (StrictOrderedSemiring.to_charZero.{0} Real Real.strictOrderedSemiring)) (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedAddTorsor.toAddTorsor.{u1, u2} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3) _inst_4) x y))
Case conversion may be inaccurate. Consider using '#align isometry_equiv.midpoint_fixed IsometryEquiv.midpoint_fixedₓ'. -/
/-- If an isometric self-homeomorphism of a normed vector space over `ℝ` fixes `x` and `y`,
then it fixes the midpoint of `[x, y]`. This is a lemma for a more general Mazur-Ulam theorem,
see below. -/
theorem midpoint_fixed {x y : PE} :
    ∀ e : PE ≃ᵢ PE, e x = x → e y = y → e (midpoint ℝ x y) = midpoint ℝ x y :=
  by
  set z := midpoint ℝ x y
  -- Consider the set of `e : E ≃ᵢ E` such that `e x = x` and `e y = y`
  set s := { e : PE ≃ᵢ PE | e x = x ∧ e y = y }
  haveI : Nonempty s := ⟨⟨IsometryEquiv.refl PE, rfl, rfl⟩⟩
  -- On the one hand, `e` cannot send the midpoint `z` of `[x, y]` too far
  have h_bdd : BddAbove (range fun e : s => dist (e z) z) :=
    by
    refine' ⟨dist x z + dist x z, forall_range_iff.2 <| Subtype.forall.2 _⟩
    rintro e ⟨hx, hy⟩
    calc
      dist (e z) z ≤ dist (e z) x + dist x z := dist_triangle (e z) x z
      _ = dist (e x) (e z) + dist x z := by rw [hx, dist_comm]
      _ = dist x z + dist x z := by erw [e.dist_eq x z]
      
  -- On the other hand, consider the map `f : (E ≃ᵢ E) → (E ≃ᵢ E)`
  -- sending each `e` to `R ∘ e⁻¹ ∘ R ∘ e`, where `R` is the point reflection in the
  -- midpoint `z` of `[x, y]`.
  set R : PE ≃ᵢ PE := (point_reflection ℝ z).toIsometryEquiv
  set f : PE ≃ᵢ PE → PE ≃ᵢ PE := fun e => ((e.trans R).trans e.symm).trans R
  -- Note that `f` doubles the value of ``dist (e z) z`
  have hf_dist : ∀ e, dist (f e z) z = 2 * dist (e z) z :=
    by
    intro e
    dsimp [f]
    rw [dist_point_reflection_fixed, ← e.dist_eq, e.apply_symm_apply,
      dist_point_reflection_self_real, dist_comm]
  -- Also note that `f` maps `s` to itself
  have hf_maps_to : maps_to f s s := by
    rintro e ⟨hx, hy⟩
    constructor <;> simp [hx, hy, e.symm_apply_eq.2 hx.symm, e.symm_apply_eq.2 hy.symm]
  -- Therefore, `dist (e z) z = 0` for all `e ∈ s`.
  set c := ⨆ e : s, dist ((e : PE ≃ᵢ PE) z) z
  have : c ≤ c / 2 := by
    apply ciSup_le
    rintro ⟨e, he⟩
    simp only [Subtype.coe_mk, le_div_iff' (zero_lt_two' ℝ), ← hf_dist]
    exact le_ciSup h_bdd ⟨f e, hf_maps_to he⟩
  replace : c ≤ 0
  · linarith
  refine' fun e hx hy => dist_le_zero.1 (le_trans _ this)
  exact le_ciSup h_bdd ⟨e, hx, hy⟩
#align isometry_equiv.midpoint_fixed IsometryEquiv.midpoint_fixed

include F

/- warning: isometry_equiv.map_midpoint -> IsometryEquiv.map_midpoint is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align isometry_equiv.map_midpoint IsometryEquiv.map_midpointₓ'. -/
/-- A bijective isometry sends midpoints to midpoints. -/
theorem map_midpoint (f : PE ≃ᵢ PF) (x y : PE) : f (midpoint ℝ x y) = midpoint ℝ (f x) (f y) :=
  by
  set e : PE ≃ᵢ PE :=
    ((f.trans <| (point_reflection ℝ <| midpoint ℝ (f x) (f y)).toIsometryEquiv).trans f.symm).trans
      (point_reflection ℝ <| midpoint ℝ x y).toIsometryEquiv
  have hx : e x = x := by simp
  have hy : e y = y := by simp
  have hm := e.midpoint_fixed hx hy
  simp only [e, trans_apply] at hm
  rwa [← eq_symm_apply, to_isometry_equiv_symm, point_reflection_symm, coe_to_isometry_equiv,
    coe_to_isometry_equiv, point_reflection_self, symm_apply_eq, point_reflection_fixed_iff] at hm
#align isometry_equiv.map_midpoint IsometryEquiv.map_midpoint

/-!
Since `f : PE ≃ᵢ PF` sends midpoints to midpoints, it is an affine map.
We define a conversion to a `continuous_linear_equiv` first, then a conversion to an `affine_map`.
-/


/- warning: isometry_equiv.to_real_linear_isometry_equiv_of_map_zero -> IsometryEquiv.toRealLinearIsometryEquivOfMapZero is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_5 : NormedAddCommGroup.{u2} F] [_inst_6 : NormedSpace.{0, u2} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5)] (f : IsometryEquiv.{u1, u2} E F (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5)))), (Eq.{succ u2} F (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (IsometryEquiv.{u1, u2} E F (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5)))) (fun (_x : IsometryEquiv.{u1, u2} E F (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5)))) => E -> F) (IsometryEquiv.hasCoeToFun.{u1, u2} E F (PseudoMetricSpace.toPseudoEMetricSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5)))) f (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_1)))))))))) (OfNat.ofNat.{u2} F 0 (OfNat.mk.{u2} F 0 (Zero.zero.{u2} F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (NormedAddGroup.toAddGroup.{u2} F (NormedAddCommGroup.toNormedAddGroup.{u2} F _inst_5)))))))))) -> (LinearIsometryEquiv.{0, 0, u1, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHomInvPair.ids.{0} Real Real.semiring) (RingHomInvPair.ids.{0} Real Real.semiring) E F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedSpace.toModule.{0, u2} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5) _inst_6))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_5 : NormedAddCommGroup.{u2} F] [_inst_6 : NormedSpace.{0, u2} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5)] (f : IsometryEquiv.{u1, u2} E F (EMetricSpace.toPseudoEMetricSpace.{u1} E (MetricSpace.toEMetricSpace.{u1} E (NormedAddCommGroup.toMetricSpace.{u1} E _inst_1))) (EMetricSpace.toPseudoEMetricSpace.{u2} F (MetricSpace.toEMetricSpace.{u2} F (NormedAddCommGroup.toMetricSpace.{u2} F _inst_5)))), (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (IsometryEquiv.{u1, u2} E F (EMetricSpace.toPseudoEMetricSpace.{u1} E (MetricSpace.toEMetricSpace.{u1} E (NormedAddCommGroup.toMetricSpace.{u1} E _inst_1))) (EMetricSpace.toPseudoEMetricSpace.{u2} F (MetricSpace.toEMetricSpace.{u2} F (NormedAddCommGroup.toMetricSpace.{u2} F _inst_5)))) E (fun (_x : E) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (IsometryEquiv.{u1, u2} E F (EMetricSpace.toPseudoEMetricSpace.{u1} E (MetricSpace.toEMetricSpace.{u1} E (NormedAddCommGroup.toMetricSpace.{u1} E _inst_1))) (EMetricSpace.toPseudoEMetricSpace.{u2} F (MetricSpace.toEMetricSpace.{u2} F (NormedAddCommGroup.toMetricSpace.{u2} F _inst_5)))) E F (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (IsometryEquiv.{u1, u2} E F (EMetricSpace.toPseudoEMetricSpace.{u1} E (MetricSpace.toEMetricSpace.{u1} E (NormedAddCommGroup.toMetricSpace.{u1} E _inst_1))) (EMetricSpace.toPseudoEMetricSpace.{u2} F (MetricSpace.toEMetricSpace.{u2} F (NormedAddCommGroup.toMetricSpace.{u2} F _inst_5)))) E F (IsometryEquiv.instEquivLikeIsometryEquiv.{u1, u2} E F (EMetricSpace.toPseudoEMetricSpace.{u1} E (MetricSpace.toEMetricSpace.{u1} E (NormedAddCommGroup.toMetricSpace.{u1} E _inst_1))) (EMetricSpace.toPseudoEMetricSpace.{u2} F (MetricSpace.toEMetricSpace.{u2} F (NormedAddCommGroup.toMetricSpace.{u2} F _inst_5)))))) f (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) 0 (Zero.toOfNat0.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (NegZeroClass.toZero.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (SubNegZeroMonoid.toNegZeroClass.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (SubtractionMonoid.toSubNegZeroMonoid.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (SubtractionCommMonoid.toSubtractionMonoid.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (AddCommGroup.toDivisionAddCommMonoid.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) (NormedAddCommGroup.toAddCommGroup.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : E) => F) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1))))))))) _inst_5))))))))) -> (LinearIsometryEquiv.{0, 0, u1, u2} Real Real Real.semiring Real.semiring (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHom.id.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)) (RingHomInvPair.ids.{0} Real Real.semiring) (RingHomInvPair.ids.{0} Real Real.semiring) E F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2) (NormedSpace.toModule.{0, u2} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_5) _inst_6))
Case conversion may be inaccurate. Consider using '#align isometry_equiv.to_real_linear_isometry_equiv_of_map_zero IsometryEquiv.toRealLinearIsometryEquivOfMapZeroₓ'. -/
/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ` and `f 0 = 0`, then `f` is a linear isometry equivalence. -/
def toRealLinearIsometryEquivOfMapZero (f : E ≃ᵢ F) (h0 : f 0 = 0) : E ≃ₗᵢ[ℝ] F :=
  { (AddMonoidHom.ofMapMidpoint ℝ ℝ f h0 f.map_midpoint).toRealLinearMap f.Continuous, f with
    norm_map' := fun x => show ‖f x‖ = ‖x‖ by simp only [← dist_zero_right, ← h0, f.dist_eq] }
#align isometry_equiv.to_real_linear_isometry_equiv_of_map_zero IsometryEquiv.toRealLinearIsometryEquivOfMapZero

/- warning: isometry_equiv.coe_to_real_linear_equiv_of_map_zero -> IsometryEquiv.coe_to_real_linear_equiv_of_map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align isometry_equiv.coe_to_real_linear_equiv_of_map_zero IsometryEquiv.coe_to_real_linear_equiv_of_map_zeroₓ'. -/
@[simp]
theorem coe_to_real_linear_equiv_of_map_zero (f : E ≃ᵢ F) (h0 : f 0 = 0) :
    ⇑(f.toRealLinearIsometryEquivOfMapZero h0) = f :=
  rfl
#align isometry_equiv.coe_to_real_linear_equiv_of_map_zero IsometryEquiv.coe_to_real_linear_equiv_of_map_zero

/- warning: isometry_equiv.coe_to_real_linear_equiv_of_map_zero_symm -> IsometryEquiv.coe_to_real_linear_equiv_of_map_zero_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align isometry_equiv.coe_to_real_linear_equiv_of_map_zero_symm IsometryEquiv.coe_to_real_linear_equiv_of_map_zero_symmₓ'. -/
@[simp]
theorem coe_to_real_linear_equiv_of_map_zero_symm (f : E ≃ᵢ F) (h0 : f 0 = 0) :
    ⇑(f.toRealLinearIsometryEquivOfMapZero h0).symm = f.symm :=
  rfl
#align isometry_equiv.coe_to_real_linear_equiv_of_map_zero_symm IsometryEquiv.coe_to_real_linear_equiv_of_map_zero_symm

#print IsometryEquiv.toRealLinearIsometryEquiv /-
/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed vector spaces
over `ℝ`, then `x ↦ f x - f 0` is a linear isometry equivalence. -/
def toRealLinearIsometryEquiv (f : E ≃ᵢ F) : E ≃ₗᵢ[ℝ] F :=
  (f.trans (IsometryEquiv.addRight (f 0)).symm).toRealLinearIsometryEquivOfMapZero
    (by simpa only [sub_eq_add_neg] using sub_self (f 0))
#align isometry_equiv.to_real_linear_isometry_equiv IsometryEquiv.toRealLinearIsometryEquiv
-/

/- warning: isometry_equiv.to_real_linear_equiv_apply -> IsometryEquiv.to_real_linear_equiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align isometry_equiv.to_real_linear_equiv_apply IsometryEquiv.to_real_linear_equiv_applyₓ'. -/
@[simp]
theorem to_real_linear_equiv_apply (f : E ≃ᵢ F) (x : E) :
    (f.toRealLinearIsometryEquiv : E → F) x = f x - f 0 :=
  (sub_eq_add_neg (f x) (f 0)).symm
#align isometry_equiv.to_real_linear_equiv_apply IsometryEquiv.to_real_linear_equiv_apply

/- warning: isometry_equiv.to_real_linear_isometry_equiv_symm_apply -> IsometryEquiv.toRealLinearIsometryEquiv_symm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align isometry_equiv.to_real_linear_isometry_equiv_symm_apply IsometryEquiv.toRealLinearIsometryEquiv_symm_applyₓ'. -/
@[simp]
theorem toRealLinearIsometryEquiv_symm_apply (f : E ≃ᵢ F) (y : F) :
    (f.toRealLinearIsometryEquiv.symm : F → E) y = f.symm (y + f 0) :=
  rfl
#align isometry_equiv.to_real_linear_isometry_equiv_symm_apply IsometryEquiv.toRealLinearIsometryEquiv_symm_apply

#print IsometryEquiv.toRealAffineIsometryEquiv /-
/-- **Mazur-Ulam Theorem**: if `f` is an isometric bijection between two normed add-torsors over
normed vector spaces over `ℝ`, then `f` is an affine isometry equivalence. -/
def toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : PE ≃ᵃⁱ[ℝ] PF :=
  AffineIsometryEquiv.mk' f
    ((vaddConst (Classical.arbitrary PE)).trans <|
        f.trans (vaddConst (f <| Classical.arbitrary PE)).symm).toRealLinearIsometryEquiv
    (Classical.arbitrary PE) fun p => by simp
#align isometry_equiv.to_real_affine_isometry_equiv IsometryEquiv.toRealAffineIsometryEquiv
-/

/- warning: isometry_equiv.coe_fn_to_real_affine_isometry_equiv -> IsometryEquiv.coeFn_toRealAffineIsometryEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align isometry_equiv.coe_fn_to_real_affine_isometry_equiv IsometryEquiv.coeFn_toRealAffineIsometryEquivₓ'. -/
@[simp]
theorem coeFn_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) : ⇑f.toRealAffineIsometryEquiv = f :=
  rfl
#align isometry_equiv.coe_fn_to_real_affine_isometry_equiv IsometryEquiv.coeFn_toRealAffineIsometryEquiv

/- warning: isometry_equiv.coe_to_real_affine_isometry_equiv -> IsometryEquiv.coe_toRealAffineIsometryEquiv is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {PE : Type.{u2}} {F : Type.{u3}} {PF : Type.{u4}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : MetricSpace.{u2} PE] [_inst_4 : NormedAddTorsor.{u1, u2} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)] [_inst_5 : NormedAddCommGroup.{u3} F] [_inst_6 : NormedSpace.{0, u3} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_5)] [_inst_7 : MetricSpace.{u4} PF] [_inst_8 : NormedAddTorsor.{u3, u4} F PF (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_5) (MetricSpace.toPseudoMetricSpace.{u4} PF _inst_7)] (f : IsometryEquiv.{u2, u4} PE PF (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u4} PF (MetricSpace.toPseudoMetricSpace.{u4} PF _inst_7))), Eq.{max (succ u2) (succ u4)} (IsometryEquiv.{u2, u4} PE PF (PseudoMetricSpace.toPseudoEMetricSpace.{u2} PE (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u4} PF (MetricSpace.toPseudoMetricSpace.{u4} PF _inst_7))) (AffineIsometryEquiv.toIsometryEquiv.{0, u1, u3, u2, u4} Real E F PE PF Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_5) _inst_2 _inst_6 (MetricSpace.toPseudoMetricSpace.{u2} PE _inst_3) (MetricSpace.toPseudoMetricSpace.{u4} PF _inst_7) _inst_4 _inst_8 (IsometryEquiv.toRealAffineIsometryEquiv.{u1, u2, u3, u4} E PE F PF _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 f)) f
but is expected to have type
  forall {E : Type.{u2}} {PE : Type.{u4}} {F : Type.{u1}} {PF : Type.{u3}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)] [_inst_3 : MetricSpace.{u4} PE] [_inst_4 : NormedAddTorsor.{u2, u4} E PE (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1) (MetricSpace.toPseudoMetricSpace.{u4} PE _inst_3)] [_inst_5 : NormedAddCommGroup.{u1} F] [_inst_6 : NormedSpace.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_5)] [_inst_7 : MetricSpace.{u3} PF] [_inst_8 : NormedAddTorsor.{u1, u3} F PF (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_5) (MetricSpace.toPseudoMetricSpace.{u3} PF _inst_7)] (f : IsometryEquiv.{u4, u3} PE PF (EMetricSpace.toPseudoEMetricSpace.{u4} PE (MetricSpace.toEMetricSpace.{u4} PE _inst_3)) (EMetricSpace.toPseudoEMetricSpace.{u3} PF (MetricSpace.toEMetricSpace.{u3} PF _inst_7))), Eq.{max (succ u4) (succ u3)} (IsometryEquiv.{u4, u3} PE PF (PseudoMetricSpace.toPseudoEMetricSpace.{u4} PE (MetricSpace.toPseudoMetricSpace.{u4} PE _inst_3)) (PseudoMetricSpace.toPseudoEMetricSpace.{u3} PF (MetricSpace.toPseudoMetricSpace.{u3} PF _inst_7))) (AffineIsometryEquiv.toIsometryEquiv.{0, u2, u1, u4, u3} Real E F PE PF Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_5) _inst_2 _inst_6 (MetricSpace.toPseudoMetricSpace.{u4} PE _inst_3) (MetricSpace.toPseudoMetricSpace.{u3} PF _inst_7) _inst_4 _inst_8 (IsometryEquiv.toRealAffineIsometryEquiv.{u2, u4, u1, u3} E PE F PF _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 f)) f
Case conversion may be inaccurate. Consider using '#align isometry_equiv.coe_to_real_affine_isometry_equiv IsometryEquiv.coe_toRealAffineIsometryEquivₓ'. -/
@[simp]
theorem coe_toRealAffineIsometryEquiv (f : PE ≃ᵢ PF) :
    f.toRealAffineIsometryEquiv.toIsometryEquiv = f :=
  by
  ext
  rfl
#align isometry_equiv.coe_to_real_affine_isometry_equiv IsometryEquiv.coe_toRealAffineIsometryEquiv

end IsometryEquiv

