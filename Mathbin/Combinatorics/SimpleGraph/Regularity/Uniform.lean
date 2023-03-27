/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.simple_graph.regularity.uniform
! leanprover-community/mathlib commit 832f7b9162039c28b9361289c8681f155cae758f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Density
import Mathbin.SetTheory.Ordinal.Basic

/-!
# Graph uniformity and uniform partitions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at most
`ε`-far from the density of any big enough `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of non `ε`-uniform pairs of parts
is less than `ε`.

## Main declarations

* `simple_graph.is_uniform`: Graph uniformity of a pair of finsets of vertices.
* `simple_graph.nonuniform_witness`: `G.nonuniform_witness ε s t` and `G.nonuniform_witness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `finpartition.non_uniforms`: Non uniform pairs of parts of a partition.
* `finpartition.is_uniform`: Uniformity of a partition.
* `finpartition.nonuniform_witnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.
-/


open Finset

variable {α 𝕜 : Type _} [LinearOrderedField 𝕜]

/-! ###  Graph uniformity -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

#print SimpleGraph.IsUniform /-
/-- A pair of finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density is close
to the density of any big enough pair of subsets. Intuitively, the edges between them are
random-like. -/
def IsUniform (s t : Finset α) : Prop :=
  ∀ ⦃s'⦄,
    s' ⊆ s →
      ∀ ⦃t'⦄,
        t' ⊆ t →
          (s.card : 𝕜) * ε ≤ s'.card →
            (t.card : 𝕜) * ε ≤ t'.card → |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε
#align simple_graph.is_uniform SimpleGraph.IsUniform
-/

variable {G ε}

#print SimpleGraph.IsUniform.mono /-
theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
  fun s' hs' t' ht' hs ht => by
  refine' (hε hs' ht' (le_trans _ hs) (le_trans _ ht)).trans_le h <;>
    exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
#align simple_graph.is_uniform.mono SimpleGraph.IsUniform.mono
-/

/- warning: simple_graph.is_uniform.symm -> SimpleGraph.IsUniform.symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] {G : SimpleGraph.{u1} α} [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, Symmetric.{succ u1} (Finset.{u1} α) (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {G : SimpleGraph.{u2} α} [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜}, Symmetric.{succ u2} (Finset.{u2} α) (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε)
Case conversion may be inaccurate. Consider using '#align simple_graph.is_uniform.symm SimpleGraph.IsUniform.symmₓ'. -/
theorem IsUniform.symm : Symmetric (IsUniform G ε) := fun s t h t' ht' s' hs' ht hs =>
  by
  rw [edge_density_comm _ t', edge_density_comm _ t]
  exact h hs' ht' hs ht
#align simple_graph.is_uniform.symm SimpleGraph.IsUniform.symm

variable (G)

/- warning: simple_graph.is_uniform_comm -> SimpleGraph.isUniform_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t) (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε t s)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, Iff (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t) (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε t s)
Case conversion may be inaccurate. Consider using '#align simple_graph.is_uniform_comm SimpleGraph.isUniform_commₓ'. -/
theorem isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨fun h => h.symm, fun h => h.symm⟩
#align simple_graph.is_uniform_comm SimpleGraph.isUniform_comm

/- warning: simple_graph.is_uniform_singleton -> SimpleGraph.isUniform_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {a : α} {b : α}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))))) ε) -> (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) b))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {a : α} {b : α}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (StrictOrderedRing.toPartialOrder.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1)))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))))) ε) -> (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) b))
Case conversion may be inaccurate. Consider using '#align simple_graph.is_uniform_singleton SimpleGraph.isUniform_singletonₓ'. -/
theorem isUniform_singleton (hε : 0 < ε) : G.IsUniform ε {a} {b} :=
  by
  intro s' hs' t' ht' hs ht
  rw [card_singleton, Nat.cast_one, one_mul] at hs ht
  obtain rfl | rfl := Finset.subset_singleton_iff.1 hs'
  · replace hs : ε ≤ 0 := by simpa using hs
    exact (hε.not_le hs).elim
  obtain rfl | rfl := Finset.subset_singleton_iff.1 ht'
  · replace ht : ε ≤ 0 := by simpa using ht
    exact (hε.not_le ht).elim
  · rwa [sub_self, abs_zero]
#align simple_graph.is_uniform_singleton SimpleGraph.isUniform_singleton

/- warning: simple_graph.not_is_uniform_zero -> SimpleGraph.not_isUniform_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s : Finset.{u1} α} {t : Finset.{u1} α}, Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))))) s t)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {s : Finset.{u2} α} {t : Finset.{u2} α}, Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (LinearOrderedSemifield.toSemifield.{u1} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u1} 𝕜 _inst_1))))))) s t)
Case conversion may be inaccurate. Consider using '#align simple_graph.not_is_uniform_zero SimpleGraph.not_isUniform_zeroₓ'. -/
theorem not_isUniform_zero : ¬G.IsUniform (0 : 𝕜) s t := fun h =>
  (abs_nonneg _).not_lt <| h (empty_subset _) (empty_subset _) (by simp) (by simp)
#align simple_graph.not_is_uniform_zero SimpleGraph.not_isUniform_zero

/- warning: simple_graph.is_uniform_one -> SimpleGraph.isUniform_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {s : Finset.{u1} α} {t : Finset.{u1} α}, SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u2} 𝕜 1 (OfNat.mk.{u2} 𝕜 1 (One.one.{u2} 𝕜 (AddMonoidWithOne.toOne.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) s t
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {s : Finset.{u2} α} {t : Finset.{u2} α}, SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) s t
Case conversion may be inaccurate. Consider using '#align simple_graph.is_uniform_one SimpleGraph.isUniform_oneₓ'. -/
theorem isUniform_one : G.IsUniform (1 : 𝕜) s t :=
  by
  intro s' hs' t' ht' hs ht
  rw [mul_one] at hs ht
  rw [eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs),
    eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht), sub_self, abs_zero]
  exact zero_lt_one
#align simple_graph.is_uniform_one SimpleGraph.isUniform_one

variable {G}

/- warning: simple_graph.not_is_uniform_iff -> SimpleGraph.not_isUniform_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] {G : SimpleGraph.{u1} α} [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, Iff (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) (Exists.{succ u1} (Finset.{u1} α) (fun (s' : Finset.{u1} α) => And (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s' s) (Exists.{succ u1} (Finset.{u1} α) (fun (t' : Finset.{u1} α) => And (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) t' t) (And (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α s)) ε) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α s'))) (And (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α t)) ε) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α t'))) (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) ε (Abs.abs.{u2} 𝕜 (Neg.toHasAbs.{u2} 𝕜 (SubNegMonoid.toHasNeg.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))) (SemilatticeSup.toHasSup.{u2} 𝕜 (Lattice.toSemilatticeSup.{u2} 𝕜 (LinearOrder.toLattice.{u2} 𝕜 (LinearOrderedRing.toLinearOrder.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (SubNegMonoid.toHasSub.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) s' t')) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) s t)))))))))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] {G : SimpleGraph.{u2} α} [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, Iff (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) (Exists.{succ u2} (Finset.{u2} α) (fun (s' : Finset.{u2} α) => And (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s' s) (Exists.{succ u2} (Finset.{u2} α) (fun (t' : Finset.{u2} α) => And (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) t' t) (And (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α s)) ε) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α s'))) (And (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α t)) ε) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α t'))) (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) ε (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (SimpleGraph.edgeDensity.{u2} α G (fun (a : α) (b : α) => _inst_2 a b) s' t') (SimpleGraph.edgeDensity.{u2} α G (fun (a : α) (b : α) => _inst_2 a b) s t)))))))))))
Case conversion may be inaccurate. Consider using '#align simple_graph.not_is_uniform_iff SimpleGraph.not_isUniform_iffₓ'. -/
theorem not_isUniform_iff :
    ¬G.IsUniform ε s t ↔
      ∃ s',
        s' ⊆ s ∧
          ∃ t',
            t' ⊆ t ∧
              ↑s.card * ε ≤ s'.card ∧
                ↑t.card * ε ≤ t'.card ∧ ε ≤ |G.edgeDensity s' t' - G.edgeDensity s t| :=
  by
  unfold is_uniform
  simp only [not_forall, not_lt, exists_prop]
#align simple_graph.not_is_uniform_iff SimpleGraph.not_isUniform_iff

open Classical

variable (G)

#print SimpleGraph.nonuniformWitnesses /-
/-- An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. See
`simple_graph.nonuniform_witness`. -/
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α) : Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).some, (not_isUniform_iff.1 h).choose_spec.2.some)
  else (s, t)
#align simple_graph.nonuniform_witnesses SimpleGraph.nonuniformWitnesses
-/

/- warning: simple_graph.left_nonuniform_witnesses_subset -> SimpleGraph.left_nonuniformWitnesses_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (SimpleGraph.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) s)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Prod.fst.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) (SimpleGraph.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) s)
Case conversion may be inaccurate. Consider using '#align simple_graph.left_nonuniform_witnesses_subset SimpleGraph.left_nonuniformWitnesses_subsetₓ'. -/
theorem left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1 ⊆ s :=
  by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).choose_spec.1
#align simple_graph.left_nonuniform_witnesses_subset SimpleGraph.left_nonuniformWitnesses_subset

/- warning: simple_graph.left_nonuniform_witnesses_card -> SimpleGraph.left_nonuniformWitnesses_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α s)) ε) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (SimpleGraph.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α s)) ε) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α (Prod.fst.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) (SimpleGraph.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.left_nonuniform_witnesses_card SimpleGraph.left_nonuniformWitnesses_cardₓ'. -/
theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    (s.card : 𝕜) * ε ≤ (G.nonuniformWitnesses ε s t).1.card :=
  by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).choose_spec.2.choose_spec.2.1
#align simple_graph.left_nonuniform_witnesses_card SimpleGraph.left_nonuniformWitnesses_card

/- warning: simple_graph.right_nonuniform_witnesses_subset -> SimpleGraph.right_nonuniformWitnesses_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (SimpleGraph.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) t)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Prod.snd.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) (SimpleGraph.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) t)
Case conversion may be inaccurate. Consider using '#align simple_graph.right_nonuniform_witnesses_subset SimpleGraph.right_nonuniformWitnesses_subsetₓ'. -/
theorem right_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).2 ⊆ t :=
  by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).choose_spec.2.choose_spec.1
#align simple_graph.right_nonuniform_witnesses_subset SimpleGraph.right_nonuniformWitnesses_subset

/- warning: simple_graph.right_nonuniform_witnesses_card -> SimpleGraph.right_nonuniformWitnesses_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α t)) ε) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (SimpleGraph.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α t)) ε) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α (Prod.snd.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) (SimpleGraph.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.right_nonuniform_witnesses_card SimpleGraph.right_nonuniformWitnesses_cardₓ'. -/
theorem right_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    (t.card : 𝕜) * ε ≤ (G.nonuniformWitnesses ε s t).2.card :=
  by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).choose_spec.2.choose_spec.2.2.1
#align simple_graph.right_nonuniform_witnesses_card SimpleGraph.right_nonuniformWitnesses_card

/- warning: simple_graph.nonuniform_witnesses_spec -> SimpleGraph.nonuniformWitnesses_spec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) ε (Abs.abs.{u2} 𝕜 (Neg.toHasAbs.{u2} 𝕜 (SubNegMonoid.toHasNeg.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))) (SemilatticeSup.toHasSup.{u2} 𝕜 (Lattice.toSemilatticeSup.{u2} 𝕜 (LinearOrder.toLattice.{u2} 𝕜 (LinearOrderedRing.toLinearOrder.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (SubNegMonoid.toHasSub.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (SimpleGraph.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (SimpleGraph.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) s t)))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) ε (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (SimpleGraph.edgeDensity.{u2} α G (fun (a : α) (b : α) => _inst_2 a b) (Prod.fst.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) (SimpleGraph.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) (Prod.snd.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) (SimpleGraph.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t))) (SimpleGraph.edgeDensity.{u2} α G (fun (a : α) (b : α) => _inst_2 a b) s t)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.nonuniform_witnesses_spec SimpleGraph.nonuniformWitnesses_specₓ'. -/
theorem nonuniformWitnesses_spec (h : ¬G.IsUniform ε s t) :
    ε ≤
      |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 -
          G.edgeDensity s t| :=
  by
  rw [nonuniform_witnesses, dif_pos h]
  exact (not_is_uniform_iff.1 h).choose_spec.2.choose_spec.2.2.2
#align simple_graph.nonuniform_witnesses_spec SimpleGraph.nonuniformWitnesses_spec

#print SimpleGraph.nonuniformWitness /-
/-- Arbitrary witness of non-uniformity. `G.nonuniform_witness ε s t` and
`G.nonuniform_witness ε t s` form a pair of subsets witnessing the non-uniformity of `(s, t)`. If
`(s, t)` is uniform, returns `s`. -/
noncomputable def nonuniformWitness (ε : 𝕜) (s t : Finset α) : Finset α :=
  if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2
#align simple_graph.nonuniform_witness SimpleGraph.nonuniformWitness
-/

/- warning: simple_graph.nonuniform_witness_subset -> SimpleGraph.nonuniformWitness_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (SimpleGraph.nonuniformWitness.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t) s)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (SimpleGraph.nonuniformWitness.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t) s)
Case conversion may be inaccurate. Consider using '#align simple_graph.nonuniform_witness_subset SimpleGraph.nonuniformWitness_subsetₓ'. -/
theorem nonuniformWitness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε s t ⊆ s :=
  by
  unfold nonuniform_witness
  split_ifs
  · exact G.left_nonuniform_witnesses_subset h
  · exact G.right_nonuniform_witnesses_subset fun i => h i.symm
#align simple_graph.nonuniform_witness_subset SimpleGraph.nonuniformWitness_subset

/- warning: simple_graph.nonuniform_witness_card_le -> SimpleGraph.nonuniformWitness_card_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (Distrib.toHasMul.{u2} 𝕜 (Ring.toDistrib.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α s)) ε) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat 𝕜 (HasLiftT.mk.{1, succ u2} Nat 𝕜 (CoeTCₓ.coe.{1, succ u2} Nat 𝕜 (Nat.castCoe.{u2} 𝕜 (AddMonoidWithOne.toNatCast.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))))) (Finset.card.{u1} α (SimpleGraph.nonuniformWitness.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))))) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α s)) ε) (Nat.cast.{u1} 𝕜 (NonAssocRing.toNatCast.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1))))) (Finset.card.{u2} α (SimpleGraph.nonuniformWitness.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t))))
Case conversion may be inaccurate. Consider using '#align simple_graph.nonuniform_witness_card_le SimpleGraph.nonuniformWitness_card_leₓ'. -/
theorem nonuniformWitness_card_le (h : ¬G.IsUniform ε s t) :
    (s.card : 𝕜) * ε ≤ (G.nonuniformWitness ε s t).card :=
  by
  unfold nonuniform_witness
  split_ifs
  · exact G.left_nonuniform_witnesses_card h
  · exact G.right_nonuniform_witnesses_card fun i => h i.symm
#align simple_graph.nonuniform_witness_card_le SimpleGraph.nonuniformWitness_card_le

/- warning: simple_graph.nonuniform_witness_spec -> SimpleGraph.nonuniformWitness_spec is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] (G : SimpleGraph.{u1} α) [_inst_2 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Ne.{succ u1} (Finset.{u1} α) s t) -> (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) ε (Abs.abs.{u2} 𝕜 (Neg.toHasAbs.{u2} 𝕜 (SubNegMonoid.toHasNeg.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))))) (SemilatticeSup.toHasSup.{u2} 𝕜 (Lattice.toSemilatticeSup.{u2} 𝕜 (LinearOrder.toLattice.{u2} 𝕜 (LinearOrderedRing.toLinearOrder.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (SubNegMonoid.toHasSub.{u2} 𝕜 (AddGroup.toSubNegMonoid.{u2} 𝕜 (AddGroupWithOne.toAddGroup.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) (SimpleGraph.nonuniformWitness.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t) (SimpleGraph.nonuniformWitness.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε t s))) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Rat 𝕜 (HasLiftT.mk.{1, succ u2} Rat 𝕜 (CoeTCₓ.coe.{1, succ u2} Rat 𝕜 (Rat.castCoe.{u2} 𝕜 (DivisionRing.toHasRatCast.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1)))))) (SimpleGraph.edgeDensity.{u1} α G (fun (a : α) (b : α) => _inst_2 a b) s t)))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] (G : SimpleGraph.{u2} α) [_inst_2 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Ne.{succ u2} (Finset.{u2} α) s t) -> (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t)) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) ε (Rat.cast.{u1} 𝕜 (LinearOrderedField.toRatCast.{u1} 𝕜 _inst_1) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instSupRat) (HSub.hSub.{0, 0, 0} Rat Rat Rat (instHSub.{0} Rat Rat.instSubRat) (SimpleGraph.edgeDensity.{u2} α G (fun (a : α) (b : α) => _inst_2 a b) (SimpleGraph.nonuniformWitness.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε s t) (SimpleGraph.nonuniformWitness.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_2 a b) ε t s)) (SimpleGraph.edgeDensity.{u2} α G (fun (a : α) (b : α) => _inst_2 a b) s t)))))
Case conversion may be inaccurate. Consider using '#align simple_graph.nonuniform_witness_spec SimpleGraph.nonuniformWitness_specₓ'. -/
theorem nonuniformWitness_spec (h₁ : s ≠ t) (h₂ : ¬G.IsUniform ε s t) :
    ε ≤
      |G.edgeDensity (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) - G.edgeDensity s t| :=
  by
  unfold nonuniform_witness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [if_pos lt, if_neg (asymm lt)]
    exact G.nonuniform_witnesses_spec h₂
  · cases h₁ rfl
  · rw [if_neg (asymm GT.gt), if_pos GT.gt, edge_density_comm, edge_density_comm _ s]
    apply G.nonuniform_witnesses_spec fun i => h₂ i.symm
#align simple_graph.nonuniform_witness_spec SimpleGraph.nonuniformWitness_spec

end SimpleGraph

/-! ### Uniform partitions -/


variable [DecidableEq α] {A : Finset α} (P : Finpartition A) (G : SimpleGraph α)
  [DecidableRel G.Adj] {ε : 𝕜}

namespace Finpartition

open Classical

/- warning: finpartition.non_uniforms -> Finpartition.nonUniforms is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) -> (forall (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], 𝕜 -> (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) A) -> (forall (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], 𝕜 -> (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))))
Case conversion may be inaccurate. Consider using '#align finpartition.non_uniforms Finpartition.nonUniformsₓ'. -/
/-- The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself. -/
noncomputable def nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filterₓ fun uv => ¬G.IsUniform ε uv.1 uv.2
#align finpartition.non_uniforms Finpartition.nonUniforms

/- warning: finpartition.mk_mem_non_uniforms_iff -> Finpartition.mk_mem_nonUniforms_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] (u : Finset.{u1} α) (v : Finset.{u1} α) (ε : 𝕜), Iff (Membership.Mem.{u1, u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finset.hasMem.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Prod.mk.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) u v) (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε)) (And (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) u (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A P)) (And (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) v (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A P)) (And (Ne.{succ u1} (Finset.{u1} α) u v) (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_3 a b) ε u v)))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {A : Finset.{u2} α} (P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A) (G : SimpleGraph.{u2} α) [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] (u : Finset.{u2} α) (v : Finset.{u2} α) (ε : 𝕜), Iff (Membership.mem.{u2, u2} (Prod.{u2, u2} (Finset.{u2} α) (Finset.{u2} α)) (Finset.{u2} (Prod.{u2, u2} (Finset.{u2} α) (Finset.{u2} α))) (Finset.instMembershipFinset.{u2} (Prod.{u2, u2} (Finset.{u2} α) (Finset.{u2} α))) (Prod.mk.{u2, u2} (Finset.{u2} α) (Finset.{u2} α) u v) (Finpartition.nonUniforms.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε)) (And (Membership.mem.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Finset.{u2} α)) (Finset.instMembershipFinset.{u2} (Finset.{u2} α)) u (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A P)) (And (Membership.mem.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Finset.{u2} α)) (Finset.instMembershipFinset.{u2} (Finset.{u2} α)) v (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A P)) (And (Ne.{succ u2} (Finset.{u2} α) u v) (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_3 a b) ε u v)))))
Case conversion may be inaccurate. Consider using '#align finpartition.mk_mem_non_uniforms_iff Finpartition.mk_mem_nonUniforms_iffₓ'. -/
theorem mk_mem_nonUniforms_iff (u v : Finset α) (ε : 𝕜) :
    (u, v) ∈ P.nonUniforms G ε ↔ u ∈ P.parts ∧ v ∈ P.parts ∧ u ≠ v ∧ ¬G.IsUniform ε u v := by
  rw [non_uniforms, mem_filter, mem_off_diag, and_assoc', and_assoc']
#align finpartition.mk_mem_non_uniforms_iff Finpartition.mk_mem_nonUniforms_iff

/- warning: finpartition.non_uniforms_mono -> Finpartition.nonUniforms_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {ε' : 𝕜}, (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) ε ε') -> (HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finset.hasSubset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε') (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) A) (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {ε' : 𝕜}, (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (StrictOrderedRing.toPartialOrder.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1)))))) ε ε') -> (HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finset.instHasSubsetFinset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε') (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε))
Case conversion may be inaccurate. Consider using '#align finpartition.non_uniforms_mono Finpartition.nonUniforms_monoₓ'. -/
theorem nonUniforms_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.nonUniforms G ε' ⊆ P.nonUniforms G ε :=
  monotone_filter_right _ fun uv => mt <| SimpleGraph.IsUniform.mono h
#align finpartition.non_uniforms_mono Finpartition.nonUniforms_mono

/- warning: finpartition.non_uniforms_bot -> Finpartition.nonUniforms_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))))) ε) -> (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A (Bot.bot.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) (Finpartition.hasBot.{u1} α (fun (a : α) (b : α) => _inst_2 a b) A)) G (fun (a : α) (b : α) => _inst_3 a b) ε) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finset.hasEmptyc.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (StrictOrderedRing.toPartialOrder.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1)))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))))) ε) -> (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finpartition.nonUniforms.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A (Bot.bot.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) A) (Finpartition.instBotFinpartitionFinsetInstLatticeFinsetInstOrderBotFinsetToLEToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_2 a b) A)) G (fun (a : α) (b : α) => _inst_3 a b) ε) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α))) (Finset.instEmptyCollectionFinset.{u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align finpartition.non_uniforms_bot Finpartition.nonUniforms_botₓ'. -/
theorem nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅ :=
  by
  rw [eq_empty_iff_forall_not_mem]
  rintro ⟨u, v⟩
  simp only [Finpartition.mk_mem_nonUniforms_iff, Finpartition.parts_bot, mem_map, not_and,
    Classical.not_not, exists_imp]
  rintro x hx rfl y hy rfl h
  exact G.is_uniform_singleton hε
#align finpartition.non_uniforms_bot Finpartition.nonUniforms_bot

/- warning: finpartition.is_uniform -> Finpartition.IsUniform is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) -> (forall (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], 𝕜 -> Prop)
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) A) -> (forall (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], 𝕜 -> Prop)
Case conversion may be inaccurate. Consider using '#align finpartition.is_uniform Finpartition.IsUniformₓ'. -/
/-- A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`. -/
def IsUniform (ε : 𝕜) : Prop :=
  ((P.nonUniforms G ε).card : 𝕜) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε
#align finpartition.is_uniform Finpartition.IsUniform

/- warning: finpartition.bot_is_uniform -> Finpartition.botIsUniform is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) (OfNat.ofNat.{u2} 𝕜 0 (OfNat.mk.{u2} 𝕜 0 (Zero.zero.{u2} 𝕜 (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))))) ε) -> (Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A (Bot.bot.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) (Finpartition.hasBot.{u1} α (fun (a : α) (b : α) => _inst_2 a b) A)) G (fun (a : α) (b : α) => _inst_3 a b) ε)
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, (LT.lt.{u2} 𝕜 (Preorder.toLT.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (StrictOrderedRing.toPartialOrder.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1)))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (LinearOrderedSemifield.toSemifield.{u2} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u2} 𝕜 _inst_1))))))) ε) -> (Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A (Bot.bot.{u1} (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) A) (Finpartition.instBotFinpartitionFinsetInstLatticeFinsetInstOrderBotFinsetToLEToPreorderPartialOrder.{u1} α (fun (a : α) (b : α) => _inst_2 a b) A)) G (fun (a : α) (b : α) => _inst_3 a b) ε)
Case conversion may be inaccurate. Consider using '#align finpartition.bot_is_uniform Finpartition.botIsUniformₓ'. -/
theorem botIsUniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε :=
  by
  rw [Finpartition.IsUniform, Finpartition.card_bot, non_uniforms_bot _ hε, Finset.card_empty,
    Nat.cast_zero]
  exact mul_nonneg (Nat.cast_nonneg _) hε.le
#align finpartition.bot_is_uniform Finpartition.botIsUniform

/- warning: finpartition.is_uniform_one -> Finpartition.isUniformOne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} (P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) (OfNat.ofNat.{u2} 𝕜 1 (OfNat.mk.{u2} 𝕜 1 (One.one.{u2} 𝕜 (AddMonoidWithOne.toOne.{u2} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u2} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u2} 𝕜 (Ring.toAddCommGroupWithOne.{u2} 𝕜 (DivisionRing.toRing.{u2} 𝕜 (Field.toDivisionRing.{u2} 𝕜 (LinearOrderedField.toField.{u2} 𝕜 _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {A : Finset.{u2} α} (P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A) (G : SimpleGraph.{u2} α) [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)], Finpartition.IsUniform.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (NonAssocRing.toOne.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (DivisionRing.toRing.{u1} 𝕜 (Field.toDivisionRing.{u1} 𝕜 (LinearOrderedField.toField.{u1} 𝕜 _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align finpartition.is_uniform_one Finpartition.isUniformOneₓ'. -/
theorem isUniformOne : P.IsUniform G (1 : 𝕜) :=
  by
  rw [is_uniform, mul_one, Nat.cast_le]
  refine' (card_filter_le _ _).trans _
  rw [off_diag_card, Nat.mul_sub_left_distrib, mul_one]
#align finpartition.is_uniform_one Finpartition.isUniformOne

variable {P G}

/- warning: finpartition.is_uniform.mono -> Finpartition.IsUniform.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A} {G : SimpleGraph.{u1} α} [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {ε' : 𝕜}, (Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε) -> (LE.le.{u2} 𝕜 (Preorder.toLE.{u2} 𝕜 (PartialOrder.toPreorder.{u2} 𝕜 (OrderedAddCommGroup.toPartialOrder.{u2} 𝕜 (StrictOrderedRing.toOrderedAddCommGroup.{u2} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u2} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u2} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u2} 𝕜 _inst_1))))))) ε ε') -> (Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε')
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {A : Finset.{u2} α} {P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A} {G : SimpleGraph.{u2} α} [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {ε' : 𝕜}, (Finpartition.IsUniform.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε) -> (LE.le.{u1} 𝕜 (Preorder.toLE.{u1} 𝕜 (PartialOrder.toPreorder.{u1} 𝕜 (StrictOrderedRing.toPartialOrder.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1)))))) ε ε') -> (Finpartition.IsUniform.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε')
Case conversion may be inaccurate. Consider using '#align finpartition.is_uniform.mono Finpartition.IsUniform.monoₓ'. -/
theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε ≤ ε') : P.IsUniform G ε' :=
  ((Nat.cast_le.2 <| card_le_of_subset <| P.nonUniforms_mono G h).trans hP).trans <|
    mul_le_mul_of_nonneg_left h <| Nat.cast_nonneg _
#align finpartition.is_uniform.mono Finpartition.IsUniform.mono

/- warning: finpartition.is_uniform_of_empty -> Finpartition.isUniformOfEmpty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A} {G : SimpleGraph.{u1} α} [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, (Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A P) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Finset.{u1} α)) (Finset.hasEmptyc.{u1} (Finset.{u1} α)))) -> (Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε)
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {A : Finset.{u2} α} {P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A} {G : SimpleGraph.{u2} α} [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜}, (Eq.{succ u2} (Finset.{u2} (Finset.{u2} α)) (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A P) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} (Finset.{u2} α)) (Finset.instEmptyCollectionFinset.{u2} (Finset.{u2} α)))) -> (Finpartition.IsUniform.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε)
Case conversion may be inaccurate. Consider using '#align finpartition.is_uniform_of_empty Finpartition.isUniformOfEmptyₓ'. -/
theorem isUniformOfEmpty (hP : P.parts = ∅) : P.IsUniform G ε := by
  simp [is_uniform, hP, non_uniforms]
#align finpartition.is_uniform_of_empty Finpartition.isUniformOfEmpty

/- warning: finpartition.nonempty_of_not_uniform -> Finpartition.nonempty_of_not_uniform is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A} {G : SimpleGraph.{u1} α} [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜}, (Not (Finpartition.IsUniform.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε)) -> (Finset.Nonempty.{u1} (Finset.{u1} α) (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A P))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {A : Finset.{u2} α} {P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A} {G : SimpleGraph.{u2} α} [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜}, (Not (Finpartition.IsUniform.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε)) -> (Finset.Nonempty.{u2} (Finset.{u2} α) (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A P))
Case conversion may be inaccurate. Consider using '#align finpartition.nonempty_of_not_uniform Finpartition.nonempty_of_not_uniformₓ'. -/
theorem nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty :=
  nonempty_of_ne_empty fun h₁ => h <| isUniformOfEmpty h₁
#align finpartition.nonempty_of_not_uniform Finpartition.nonempty_of_not_uniform

variable (P G ε) (s : Finset α)

/- warning: finpartition.nonuniform_witnesses -> Finpartition.nonuniformWitnesses is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A) -> (forall (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], 𝕜 -> (Finset.{u1} α) -> (Finset.{u1} (Finset.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α}, (Finpartition.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) A) -> (forall (G : SimpleGraph.{u1} α) [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)], 𝕜 -> (Finset.{u1} α) -> (Finset.{u1} (Finset.{u1} α)))
Case conversion may be inaccurate. Consider using '#align finpartition.nonuniform_witnesses Finpartition.nonuniformWitnessesₓ'. -/
/-- A choice of witnesses of non-uniformity among the parts of a finpartition. -/
noncomputable def nonuniformWitnesses : Finset (Finset α) :=
  (P.parts.filterₓ fun t => s ≠ t ∧ ¬G.IsUniform ε s t).image (G.nonuniformWitness ε s)
#align finpartition.nonuniform_witnesses Finpartition.nonuniformWitnesses

variable {P G ε s} {t : Finset α}

/- warning: finpartition.nonuniform_witness_mem_nonuniform_witnesses -> Finpartition.nonuniformWitness_mem_nonuniformWitnesses is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_1 : LinearOrderedField.{u2} 𝕜] [_inst_2 : DecidableEq.{succ u1} α] {A : Finset.{u1} α} {P : Finpartition.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A} {G : SimpleGraph.{u1} α} [_inst_3 : DecidableRel.{succ u1} α (SimpleGraph.Adj.{u1} α G)] {ε : 𝕜} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Not (SimpleGraph.IsUniform.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_3 a b) ε s t)) -> (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) t (Finpartition.parts.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.orderBot.{u1} α) A P)) -> (Ne.{succ u1} (Finset.{u1} α) s t) -> (Membership.Mem.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Finset.{u1} α)) (Finset.hasMem.{u1} (Finset.{u1} α)) (SimpleGraph.nonuniformWitness.{u1, u2} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_3 a b) ε s t) (Finpartition.nonuniformWitnesses.{u1, u2} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε s))
but is expected to have type
  forall {α : Type.{u2}} {𝕜 : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : DecidableEq.{succ u2} α] {A : Finset.{u2} α} {P : Finpartition.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A} {G : SimpleGraph.{u2} α} [_inst_3 : DecidableRel.{succ u2} α (SimpleGraph.Adj.{u2} α G)] {ε : 𝕜} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Not (SimpleGraph.IsUniform.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_3 a b) ε s t)) -> (Membership.mem.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Finset.{u2} α)) (Finset.instMembershipFinset.{u2} (Finset.{u2} α)) t (Finpartition.parts.{u2} (Finset.{u2} α) (Finset.instLatticeFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) A P)) -> (Ne.{succ u2} (Finset.{u2} α) s t) -> (Membership.mem.{u2, u2} (Finset.{u2} α) (Finset.{u2} (Finset.{u2} α)) (Finset.instMembershipFinset.{u2} (Finset.{u2} α)) (SimpleGraph.nonuniformWitness.{u2, u1} α 𝕜 _inst_1 G (fun (a : α) (b : α) => _inst_3 a b) ε s t) (Finpartition.nonuniformWitnesses.{u2, u1} α 𝕜 _inst_1 (fun (a : α) (b : α) => _inst_2 a b) A P G (fun (a : α) (b : α) => _inst_3 a b) ε s))
Case conversion may be inaccurate. Consider using '#align finpartition.nonuniform_witness_mem_nonuniform_witnesses Finpartition.nonuniformWitness_mem_nonuniformWitnessesₓ'. -/
theorem nonuniformWitness_mem_nonuniformWitnesses (h : ¬G.IsUniform ε s t) (ht : t ∈ P.parts)
    (hst : s ≠ t) : G.nonuniformWitness ε s t ∈ P.nonuniformWitnesses G ε s :=
  mem_image_of_mem _ <| mem_filter.2 ⟨ht, hst, h⟩
#align finpartition.nonuniform_witness_mem_nonuniform_witnesses Finpartition.nonuniformWitness_mem_nonuniformWitnesses

end Finpartition

