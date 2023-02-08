/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module data.set.pointwise.iterate
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Dynamics.FixedPoints.Basic

/-!
# Results about pointwise operations on sets with iteration.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Pointwise

open Set Function

/- warning: smul_eq_self_of_preimage_zpow_eq_self -> smul_eq_self_of_preimage_zpow_eq_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {n : Int} {s : Set.{u1} G}, (Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) x n) s) s) -> (forall {g : G} {j : Nat}, (Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) g (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) n j)) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))))) -> (Eq.{succ u1} (Set.{u1} G) (SMul.smul.{u1, u1} G (Set.{u1} G) (Set.smulSet.{u1, u1} G G (Mul.toSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))) g s) s))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {n : Int} {s : Set.{u1} G}, (Eq.{succ u1} (Set.{u1} G) (Set.preimage.{u1, u1} G G (fun (x : G) => HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) x n) s) s) -> (forall {g : G} {j : Nat}, (Eq.{succ u1} G (HPow.hPow.{u1, 0, u1} G Int G (instHPow.{u1, 0} G Int (DivInvMonoid.Pow.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1)))) g (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat n j)) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G (CommGroup.toDivisionCommMonoid.{u1} G _inst_1)))))))) -> (Eq.{succ u1} (Set.{u1} G) (HSMul.hSMul.{u1, u1, u1} G (Set.{u1} G) (Set.{u1} G) (instHSMul.{u1, u1} G (Set.{u1} G) (Set.smulSet.{u1, u1} G G (MulAction.toSMul.{u1, u1} G G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) (Monoid.toMulAction.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_1))))))) g s) s))
Case conversion may be inaccurate. Consider using '#align smul_eq_self_of_preimage_zpow_eq_self smul_eq_self_of_preimage_zpow_eq_selfₓ'. -/
/-- Let `n : ℤ` and `s` a subset of a commutative group `G` that is invariant under preimage for
the map `x ↦ x^n`. Then `s` is invariant under the pointwise action of the subgroup of elements
`g : G` such that `g^(n^j) = 1` for some `j : ℕ`. (This subgroup is called the Prüfer subgroup when
 `G` is the `circle` and `n` is prime.) -/
@[to_additive
      "Let `n : ℤ` and `s` a subset of an additive commutative group `G` that is invariant\nunder preimage for the map `x ↦ n • x`. Then `s` is invariant under the pointwise action of the\nadditive subgroup of elements `g : G` such that `(n^j) • g = 0` for some `j : ℕ`. (This additive\nsubgroup is called the Prüfer subgroup when `G` is the `add_circle` and `n` is prime.)"]
theorem smul_eq_self_of_preimage_zpow_eq_self {G : Type _} [CommGroup G] {n : ℤ} {s : Set G}
    (hs : (fun x => x ^ n) ⁻¹' s = s) {g : G} {j : ℕ} (hg : g ^ n ^ j = 1) : g • s = s :=
  by
  suffices ∀ {g' : G} (hg' : g' ^ n ^ j = 1), g' • s ⊆ s
    by
    refine' le_antisymm (this hg) _
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1
    · rw [inv_zpow, hg, inv_one]
    simpa only [le_eq_subset, set_smul_subset_set_smul_iff] using this hg
  rw [(is_fixed_pt.preimage_iterate hs j : zpowGroupHom n^[j] ⁻¹' s = s).symm]
  rintro g' hg' - ⟨y, hy, rfl⟩
  change (zpowGroupHom n^[j]) (g' * y) ∈ s
  replace hg' : (zpowGroupHom n^[j]) g' = 1
  · simpa [zpowGroupHom]
  rwa [MonoidHom.iterate_map_mul, hg', one_mul]
#align smul_eq_self_of_preimage_zpow_eq_self smul_eq_self_of_preimage_zpow_eq_self
#align vadd_eq_self_of_preimage_zsmul_eq_self vadd_eq_self_of_preimage_zsmul_eq_self

