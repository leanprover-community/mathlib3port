/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz

! This file was ported from Lean 3 source module group_theory.solvable
! leanprover-community/mathlib commit 0f6670b8af2dff699de1c0b4b49039b31bc13c46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.VecNotation
import Mathbin.GroupTheory.Abelianization
import Mathbin.GroupTheory.Perm.ViaEmbedding
import Mathbin.GroupTheory.Subgroup.Simple
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/


open Subgroup

variable {G G' : Type _} [Group G] [Group G'] {f : G →* G'}

section derivedSeries

variable (G)

#print derivedSeries /-
/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n, derivedSeries n⁆
#align derived_series derivedSeries
-/

/- warning: derived_series_zero -> derivedSeries_zero is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G], Eq.{succ u1} (Subgroup.{u1} G _inst_1) (derivedSeries.{u1} G _inst_1 (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G], Eq.{succ u1} (Subgroup.{u1} G _inst_1) (derivedSeries.{u1} G _inst_1 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align derived_series_zero derivedSeries_zeroₓ'. -/
@[simp]
theorem derivedSeries_zero : derivedSeries G 0 = ⊤ :=
  rfl
#align derived_series_zero derivedSeries_zero

#print derivedSeries_succ /-
@[simp]
theorem derivedSeries_succ (n : ℕ) :
    derivedSeries G (n + 1) = ⁅derivedSeries G n, derivedSeries G n⁆ :=
  rfl
#align derived_series_succ derivedSeries_succ
-/

#print derivedSeries_normal /-
theorem derivedSeries_normal (n : ℕ) : (derivedSeries G n).Normal :=
  by
  induction' n with n ih
  · exact (⊤ : Subgroup G).normal_of_characteristic
  · exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)
#align derived_series_normal derivedSeries_normal
-/

#print derivedSeries_one /-
@[simp]
theorem derivedSeries_one : derivedSeries G 1 = commutator G :=
  rfl
#align derived_series_one derivedSeries_one
-/

end derivedSeries

section CommutatorMap

section DerivedSeriesMap

variable (f)

/- warning: map_derived_series_le_derived_series -> map_derivedSeries_le_derivedSeries is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {G' : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} G'] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (n : Nat), LE.le.{u2} (Subgroup.{u2} G' _inst_2) (Preorder.toLE.{u2} (Subgroup.{u2} G' _inst_2) (PartialOrder.toPreorder.{u2} (Subgroup.{u2} G' _inst_2) (SetLike.partialOrder.{u2, u2} (Subgroup.{u2} G' _inst_2) G' (Subgroup.setLike.{u2} G' _inst_2)))) (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f (derivedSeries.{u1} G _inst_1 n)) (derivedSeries.{u2} G' _inst_2 n)
but is expected to have type
  forall {G : Type.{u1}} {G' : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} G'] (f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (n : Nat), LE.le.{u2} (Subgroup.{u2} G' _inst_2) (Preorder.toLE.{u2} (Subgroup.{u2} G' _inst_2) (PartialOrder.toPreorder.{u2} (Subgroup.{u2} G' _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u2} (Subgroup.{u2} G' _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Subgroup.{u2} G' _inst_2) (Subgroup.instCompleteLatticeSubgroup.{u2} G' _inst_2))))) (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f (derivedSeries.{u1} G _inst_1 n)) (derivedSeries.{u2} G' _inst_2 n)
Case conversion may be inaccurate. Consider using '#align map_derived_series_le_derived_series map_derivedSeries_le_derivedSeriesₓ'. -/
theorem map_derivedSeries_le_derivedSeries (n : ℕ) :
    (derivedSeries G n).map f ≤ derivedSeries G' n :=
  by
  induction' n with n ih
  · exact le_top
  · simp only [derivedSeries_succ, map_commutator, commutator_mono, ih]
#align map_derived_series_le_derived_series map_derivedSeries_le_derivedSeries

variable {f}

/- warning: derived_series_le_map_derived_series -> derivedSeries_le_map_derivedSeries is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {G' : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) f)) -> (forall (n : Nat), LE.le.{u2} (Subgroup.{u2} G' _inst_2) (Preorder.toLE.{u2} (Subgroup.{u2} G' _inst_2) (PartialOrder.toPreorder.{u2} (Subgroup.{u2} G' _inst_2) (SetLike.partialOrder.{u2, u2} (Subgroup.{u2} G' _inst_2) G' (Subgroup.setLike.{u2} G' _inst_2)))) (derivedSeries.{u2} G' _inst_2 n) (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f (derivedSeries.{u1} G _inst_1 n)))
but is expected to have type
  forall {G : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Group.{u1} G'] {f : MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))}, (Function.Surjective.{succ u2, succ u1} G G' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : G) => G') _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} G' (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2))) (MonoidHom.monoidHomClass.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))))) f)) -> (forall (n : Nat), LE.le.{u1} (Subgroup.{u1} G' _inst_2) (Preorder.toLE.{u1} (Subgroup.{u1} G' _inst_2) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G' _inst_2) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G' _inst_2) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G' _inst_2) (Subgroup.instCompleteLatticeSubgroup.{u1} G' _inst_2))))) (derivedSeries.{u1} G' _inst_2 n) (Subgroup.map.{u2, u1} G _inst_1 G' _inst_2 f (derivedSeries.{u2} G _inst_1 n)))
Case conversion may be inaccurate. Consider using '#align derived_series_le_map_derived_series derivedSeries_le_map_derivedSeriesₓ'. -/
theorem derivedSeries_le_map_derivedSeries (hf : Function.Surjective f) (n : ℕ) :
    derivedSeries G' n ≤ (derivedSeries G n).map f :=
  by
  induction' n with n ih
  · exact (map_top_of_surjective f hf).ge
  · exact commutator_le_map_commutator ih ih
#align derived_series_le_map_derived_series derivedSeries_le_map_derivedSeries

/- warning: map_derived_series_eq -> map_derivedSeries_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {G' : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) f)) -> (forall (n : Nat), Eq.{succ u2} (Subgroup.{u2} G' _inst_2) (Subgroup.map.{u1, u2} G _inst_1 G' _inst_2 f (derivedSeries.{u1} G _inst_1 n)) (derivedSeries.{u2} G' _inst_2 n))
but is expected to have type
  forall {G : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Group.{u1} G'] {f : MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))}, (Function.Surjective.{succ u2, succ u1} G G' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : G) => G') _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} G' (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2))) (MonoidHom.monoidHomClass.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))))) f)) -> (forall (n : Nat), Eq.{succ u1} (Subgroup.{u1} G' _inst_2) (Subgroup.map.{u2, u1} G _inst_1 G' _inst_2 f (derivedSeries.{u2} G _inst_1 n)) (derivedSeries.{u1} G' _inst_2 n))
Case conversion may be inaccurate. Consider using '#align map_derived_series_eq map_derivedSeries_eqₓ'. -/
theorem map_derivedSeries_eq (hf : Function.Surjective f) (n : ℕ) :
    (derivedSeries G n).map f = derivedSeries G' n :=
  le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)
#align map_derived_series_eq map_derivedSeries_eq

end DerivedSeriesMap

end CommutatorMap

section Solvable

variable (G)

#print IsSolvable /-
/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
class IsSolvable : Prop where
  solvable : ∃ n : ℕ, derivedSeries G n = ⊥
#align is_solvable IsSolvable
-/

/- warning: is_solvable_def -> isSolvable_def is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G], Iff (IsSolvable.{u1} G _inst_1) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} (Subgroup.{u1} G _inst_1) (derivedSeries.{u1} G _inst_1 n) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G], Iff (IsSolvable.{u1} G _inst_1) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} (Subgroup.{u1} G _inst_1) (derivedSeries.{u1} G _inst_1 n) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_solvable_def isSolvable_defₓ'. -/
theorem isSolvable_def : IsSolvable G ↔ ∃ n : ℕ, derivedSeries G n = ⊥ :=
  ⟨fun h => h.solvable, fun h => ⟨h⟩⟩
#align is_solvable_def isSolvable_def

#print CommGroup.isSolvable /-
instance (priority := 100) CommGroup.isSolvable {G : Type _} [CommGroup G] : IsSolvable G :=
  ⟨⟨1, le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id G))⟩⟩
#align comm_group.is_solvable CommGroup.isSolvable
-/

/- warning: is_solvable_of_comm -> isSolvable_of_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [hG : Group.{u1} G], (forall (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G hG))))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G hG))))) b a)) -> (IsSolvable.{u1} G hG)
but is expected to have type
  forall {G : Type.{u1}} [hG : Group.{u1} G], (forall (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G hG))))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G hG))))) b a)) -> (IsSolvable.{u1} G hG)
Case conversion may be inaccurate. Consider using '#align is_solvable_of_comm isSolvable_of_commₓ'. -/
theorem isSolvable_of_comm {G : Type _} [hG : Group G] (h : ∀ a b : G, a * b = b * a) :
    IsSolvable G := by
  letI hG' : CommGroup G := { hG with mul_comm := h }
  cases hG
  exact CommGroup.isSolvable
#align is_solvable_of_comm isSolvable_of_comm

/- warning: is_solvable_of_top_eq_bot -> isSolvable_of_top_eq_bot is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G], (Eq.{succ u1} (Subgroup.{u1} G _inst_1) (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1)) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) -> (IsSolvable.{u1} G _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : Group.{u1} G], (Eq.{succ u1} (Subgroup.{u1} G _inst_1) (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1)) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))) -> (IsSolvable.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align is_solvable_of_top_eq_bot isSolvable_of_top_eq_botₓ'. -/
theorem isSolvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G :=
  ⟨⟨0, h⟩⟩
#align is_solvable_of_top_eq_bot isSolvable_of_top_eq_bot

#print isSolvable_of_subsingleton /-
instance (priority := 100) isSolvable_of_subsingleton [Subsingleton G] : IsSolvable G :=
  isSolvable_of_top_eq_bot G (by ext <;> simp at *)
#align is_solvable_of_subsingleton isSolvable_of_subsingleton
-/

variable {G}

/- warning: solvable_of_ker_le_range -> solvable_of_ker_le_range is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G' : Type.{u2}} {G'' : Type.{u3}} [_inst_3 : Group.{u2} G'] [_inst_4 : Group.{u3} G''] (f : MonoidHom.{u2, u1} G' G (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_3))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (g : MonoidHom.{u1, u3} G G'' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u3} G'' (DivInvMonoid.toMonoid.{u3} G'' (Group.toDivInvMonoid.{u3} G'' _inst_4)))), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) (MonoidHom.ker.{u1, u3} G _inst_1 G'' (Monoid.toMulOneClass.{u3} G'' (DivInvMonoid.toMonoid.{u3} G'' (Group.toDivInvMonoid.{u3} G'' _inst_4))) g) (MonoidHom.range.{u2, u1} G' _inst_3 G _inst_1 f)) -> (forall [hG' : IsSolvable.{u2} G' _inst_3] [hG'' : IsSolvable.{u3} G'' _inst_4], IsSolvable.{u1} G _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G' : Type.{u3}} {G'' : Type.{u2}} [_inst_3 : Group.{u3} G'] [_inst_4 : Group.{u2} G''] (f : MonoidHom.{u3, u1} G' G (Monoid.toMulOneClass.{u3} G' (DivInvMonoid.toMonoid.{u3} G' (Group.toDivInvMonoid.{u3} G' _inst_3))) (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (g : MonoidHom.{u1, u2} G G'' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G'' (DivInvMonoid.toMonoid.{u2} G'' (Group.toDivInvMonoid.{u2} G'' _inst_4)))), (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (MonoidHom.ker.{u1, u2} G _inst_1 G'' (Monoid.toMulOneClass.{u2} G'' (DivInvMonoid.toMonoid.{u2} G'' (Group.toDivInvMonoid.{u2} G'' _inst_4))) g) (MonoidHom.range.{u3, u1} G' _inst_3 G _inst_1 f)) -> (forall [hG' : IsSolvable.{u3} G' _inst_3] [hG'' : IsSolvable.{u2} G'' _inst_4], IsSolvable.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align solvable_of_ker_le_range solvable_of_ker_le_rangeₓ'. -/
theorem solvable_of_ker_le_range {G' G'' : Type _} [Group G'] [Group G''] (f : G' →* G)
    (g : G →* G'') (hfg : g.ker ≤ f.range) [hG' : IsSolvable G'] [hG'' : IsSolvable G''] :
    IsSolvable G := by
  obtain ⟨n, hn⟩ := id hG''
  obtain ⟨m, hm⟩ := id hG'
  refine' ⟨⟨n + m, le_bot_iff.mp (map_bot f ▸ hm ▸ _)⟩⟩
  clear hm
  induction' m with m hm
  ·
    exact
      f.range_eq_map ▸
        ((derivedSeries G n).map_eq_bot_iff.mp
              (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans hn.le))).trans
          hfg
  · exact commutator_le_map_commutator hm hm
#align solvable_of_ker_le_range solvable_of_ker_le_range

/- warning: solvable_of_solvable_injective -> solvable_of_solvable_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {G' : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Injective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) f)) -> (forall [h : IsSolvable.{u2} G' _inst_2], IsSolvable.{u1} G _inst_1)
but is expected to have type
  forall {G : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Group.{u1} G'] {f : MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))}, (Function.Injective.{succ u2, succ u1} G G' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : G) => G') _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} G' (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2))) (MonoidHom.monoidHomClass.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))))) f)) -> (forall [h : IsSolvable.{u1} G' _inst_2], IsSolvable.{u2} G _inst_1)
Case conversion may be inaccurate. Consider using '#align solvable_of_solvable_injective solvable_of_solvable_injectiveₓ'. -/
theorem solvable_of_solvable_injective (hf : Function.Injective f) [h : IsSolvable G'] :
    IsSolvable G :=
  solvable_of_ker_le_range (1 : G' →* G) f ((f.ker_eq_bot_iff.mpr hf).symm ▸ bot_le)
#align solvable_of_solvable_injective solvable_of_solvable_injective

/- warning: subgroup_solvable_of_solvable -> subgroup_solvable_of_solvable is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [h : IsSolvable.{u1} G _inst_1], IsSolvable.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [h : IsSolvable.{u1} G _inst_1], IsSolvable.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.toGroup.{u1} G _inst_1 H)
Case conversion may be inaccurate. Consider using '#align subgroup_solvable_of_solvable subgroup_solvable_of_solvableₓ'. -/
instance subgroup_solvable_of_solvable (H : Subgroup G) [h : IsSolvable G] : IsSolvable H :=
  solvable_of_solvable_injective H.subtype_injective
#align subgroup_solvable_of_solvable subgroup_solvable_of_solvable

/- warning: solvable_of_surjective -> solvable_of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {G' : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} G'] {f : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G G' (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) => G -> G') (MonoidHom.hasCoeToFun.{u1, u2} G G' (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} G' (DivInvMonoid.toMonoid.{u2} G' (Group.toDivInvMonoid.{u2} G' _inst_2)))) f)) -> (forall [h : IsSolvable.{u1} G _inst_1], IsSolvable.{u2} G' _inst_2)
but is expected to have type
  forall {G : Type.{u2}} {G' : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Group.{u1} G'] {f : MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))}, (Function.Surjective.{succ u2, succ u1} G G' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2372 : G) => G') _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} G' (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))) G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2))) (MonoidHom.monoidHomClass.{u2, u1} G G' (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} G' (DivInvMonoid.toMonoid.{u1} G' (Group.toDivInvMonoid.{u1} G' _inst_2)))))) f)) -> (forall [h : IsSolvable.{u2} G _inst_1], IsSolvable.{u1} G' _inst_2)
Case conversion may be inaccurate. Consider using '#align solvable_of_surjective solvable_of_surjectiveₓ'. -/
theorem solvable_of_surjective (hf : Function.Surjective f) [h : IsSolvable G] : IsSolvable G' :=
  solvable_of_ker_le_range f (1 : G' →* G) ((f.range_top_of_surjective hf).symm ▸ le_top)
#align solvable_of_surjective solvable_of_surjective

#print solvable_quotient_of_solvable /-
instance solvable_quotient_of_solvable (H : Subgroup G) [H.Normal] [h : IsSolvable G] :
    IsSolvable (G ⧸ H) :=
  solvable_of_surjective (QuotientGroup.mk'_surjective H)
#align solvable_quotient_of_solvable solvable_quotient_of_solvable
-/

/- warning: solvable_prod -> solvable_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G' : Type.{u2}} [_inst_3 : Group.{u2} G'] [h : IsSolvable.{u1} G _inst_1] [h' : IsSolvable.{u2} G' _inst_3], IsSolvable.{max u1 u2} (Prod.{u1, u2} G G') (Prod.group.{u1, u2} G G' _inst_1 _inst_3)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {G' : Type.{u2}} [_inst_3 : Group.{u2} G'] [h : IsSolvable.{u1} G _inst_1] [h' : IsSolvable.{u2} G' _inst_3], IsSolvable.{max u2 u1} (Prod.{u1, u2} G G') (Prod.instGroupProd.{u1, u2} G G' _inst_1 _inst_3)
Case conversion may be inaccurate. Consider using '#align solvable_prod solvable_prodₓ'. -/
instance solvable_prod {G' : Type _} [Group G'] [h : IsSolvable G] [h' : IsSolvable G'] :
    IsSolvable (G × G') :=
  solvable_of_ker_le_range (MonoidHom.inl G G') (MonoidHom.snd G G') fun x hx =>
    ⟨x.1, Prod.ext rfl hx.symm⟩
#align solvable_prod solvable_prod

end Solvable

section IsSimpleGroup

variable [IsSimpleGroup G]

#print IsSimpleGroup.derivedSeries_succ /-
theorem IsSimpleGroup.derivedSeries_succ {n : ℕ} : derivedSeries G n.succ = commutator G :=
  by
  induction' n with n ih
  · exact derivedSeries_one G
  rw [derivedSeries_succ, ih]
  cases' (commutator.normal G).eq_bot_or_eq_top with h h
  · rw [h, commutator_bot_left]
  · rwa [h]
#align is_simple_group.derived_series_succ IsSimpleGroup.derivedSeries_succ
-/

/- warning: is_simple_group.comm_iff_is_solvable -> IsSimpleGroup.comm_iff_isSolvable is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_3 : IsSimpleGroup.{u1} G _inst_1], Iff (forall (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a)) (IsSolvable.{u1} G _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_3 : IsSimpleGroup.{u1} G _inst_1], Iff (forall (a : G) (b : G), Eq.{succ u1} G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) b a)) (IsSolvable.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align is_simple_group.comm_iff_is_solvable IsSimpleGroup.comm_iff_isSolvableₓ'. -/
theorem IsSimpleGroup.comm_iff_isSolvable : (∀ a b : G, a * b = b * a) ↔ IsSolvable G :=
  ⟨isSolvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · intro a b
      refine' (mem_bot.1 _).trans (mem_bot.1 _).symm <;>
        · rw [← hn]
          exact mem_top _
    · rw [IsSimpleGroup.derivedSeries_succ] at hn
      intro a b
      rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← mem_bot, ← hn, commutator_eq_closure]
      exact subset_closure ⟨a, b, rfl⟩⟩
#align is_simple_group.comm_iff_is_solvable IsSimpleGroup.comm_iff_isSolvable

end IsSimpleGroup

section PermNotSolvable

/- warning: not_solvable_of_mem_derived_series -> not_solvable_of_mem_derivedSeries is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {g : G}, (Ne.{succ u1} G g (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) -> (forall (n : Nat), Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) g (derivedSeries.{u1} G _inst_1 n)) -> (Not (IsSolvable.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {g : G}, (Ne.{succ u1} G g (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))) -> (forall (n : Nat), Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) g (derivedSeries.{u1} G _inst_1 n)) -> (Not (IsSolvable.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align not_solvable_of_mem_derived_series not_solvable_of_mem_derivedSeriesₓ'. -/
theorem not_solvable_of_mem_derivedSeries {g : G} (h1 : g ≠ 1)
    (h2 : ∀ n : ℕ, g ∈ derivedSeries G n) : ¬IsSolvable G :=
  mt (isSolvable_def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (Membership.Mem g) h).mp (h2 n))))
#align not_solvable_of_mem_derived_series not_solvable_of_mem_derivedSeries

#print Equiv.Perm.fin_5_not_solvable /-
theorem Equiv.Perm.fin_5_not_solvable : ¬IsSolvable (Equiv.Perm (Fin 5)) :=
  by
  let x : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  let y : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  let z : Equiv.Perm (Fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide, by decide⟩
  have key : x = z * ⁅x, y * x * y⁻¹⁆ * z⁻¹ := by decide
  refine' not_solvable_of_mem_derivedSeries (show x ≠ 1 by decide) fun n => _
  induction' n with n ih
  · exact mem_top x
  · rw [key, (derivedSeries_normal _ _).mem_comm_iff, inv_mul_cancel_left]
    exact commutator_mem_commutator ih ((derivedSeries_normal _ _).conj_mem _ ih _)
#align equiv.perm.fin_5_not_solvable Equiv.Perm.fin_5_not_solvable
-/

/- warning: equiv.perm.not_solvable -> Equiv.Perm.not_solvable is a dubious translation:
lean 3 declaration is
  forall (X : Type.{u1}), (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 5 (OfNat.mk.{succ u1} Cardinal.{u1} 5 (bit1.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1} Cardinal.hasAdd.{u1} (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))) (Cardinal.mk.{u1} X)) -> (Not (IsSolvable.{u1} (Equiv.Perm.{succ u1} X) (Equiv.Perm.permGroup.{u1} X)))
but is expected to have type
  forall (X : Type.{u1}), (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 5 (instOfNat.{succ u1} Cardinal.{u1} 5 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 3 (instOfNatNat 3))))) (Cardinal.mk.{u1} X)) -> (Not (IsSolvable.{u1} (Equiv.Perm.{succ u1} X) (Equiv.Perm.permGroup.{u1} X)))
Case conversion may be inaccurate. Consider using '#align equiv.perm.not_solvable Equiv.Perm.not_solvableₓ'. -/
theorem Equiv.Perm.not_solvable (X : Type _) (hX : 5 ≤ Cardinal.mk X) :
    ¬IsSolvable (Equiv.Perm X) := by
  intro h
  have key : Nonempty (Fin 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_natCast, Nat.cast_bit1,
      Nat.cast_bit0, Nat.cast_one, Cardinal.lift_id]
  exact
    Equiv.Perm.fin_5_not_solvable
      (solvable_of_solvable_injective (Equiv.Perm.viaEmbeddingHom_injective (Nonempty.some key)))
#align equiv.perm.not_solvable Equiv.Perm.not_solvable

end PermNotSolvable

