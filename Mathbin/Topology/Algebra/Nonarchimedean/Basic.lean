/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Ashwin Iyengar, Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.nonarchimedean.basic
! leanprover-community/mathlib commit 932872382355f00112641d305ba0619305dc8642
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Topology.Algebra.OpenSubgroup
import Mathbin.Topology.Algebra.Ring.Basic

/-!
# Nonarchimedean Topology

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `nonarchimedean_add_group`: nonarchimedean additive group.
- `nonarchimedean_group`: nonarchimedean multiplicative group.
- `nonarchimedean_ring`: nonarchimedean ring.

-/


open Pointwise

#print NonarchimedeanAddGroup /-
/-- An topological additive group is nonarchimedean if every neighborhood of 0
  contains an open subgroup. -/
class NonarchimedeanAddGroup (G : Type _) [AddGroup G] [TopologicalSpace G] extends
  TopologicalAddGroup G : Prop where
  is_nonarchimedean : ∀ U ∈ nhds (0 : G), ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U
#align nonarchimedean_add_group NonarchimedeanAddGroup
-/

#print NonarchimedeanGroup /-
/-- A topological group is nonarchimedean if every neighborhood of 1 contains an open subgroup. -/
@[to_additive]
class NonarchimedeanGroup (G : Type _) [Group G] [TopologicalSpace G] extends TopologicalGroup G :
  Prop where
  is_nonarchimedean : ∀ U ∈ nhds (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ U
#align nonarchimedean_group NonarchimedeanGroup
#align nonarchimedean_add_group NonarchimedeanAddGroup
-/

#print NonarchimedeanRing /-
/-- An topological ring is nonarchimedean if its underlying topological additive
  group is nonarchimedean. -/
class NonarchimedeanRing (R : Type _) [Ring R] [TopologicalSpace R] extends TopologicalRing R :
  Prop where
  is_nonarchimedean : ∀ U ∈ nhds (0 : R), ∃ V : OpenAddSubgroup R, (V : Set R) ⊆ U
#align nonarchimedean_ring NonarchimedeanRing
-/

#print NonarchimedeanRing.to_nonarchimedeanAddGroup /-
-- see Note [lower instance priority]
/-- Every nonarchimedean ring is naturally a nonarchimedean additive group. -/
instance (priority := 100) NonarchimedeanRing.to_nonarchimedeanAddGroup (R : Type _) [Ring R]
    [TopologicalSpace R] [t : NonarchimedeanRing R] : NonarchimedeanAddGroup R :=
  { t with }
#align nonarchimedean_ring.to_nonarchimedean_add_group NonarchimedeanRing.to_nonarchimedeanAddGroup
-/

namespace NonarchimedeanGroup

variable {G : Type _} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

variable {H : Type _} [Group H] [TopologicalSpace H] [TopologicalGroup H]

variable {K : Type _} [Group K] [TopologicalSpace K] [NonarchimedeanGroup K]

/- warning: nonarchimedean_group.nonarchimedean_of_emb -> NonarchimedeanGroup.nonarchimedean_of_emb is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : NonarchimedeanGroup.{u1} G _inst_1 _inst_2] {H : Type.{u2}} [_inst_4 : Group.{u2} H] [_inst_5 : TopologicalSpace.{u2} H] [_inst_6 : TopologicalGroup.{u2} H _inst_5 _inst_4] (f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_4)))), (OpenEmbedding.{u1, u2} G H _inst_2 _inst_5 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_4)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_4)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_4)))) f)) -> (NonarchimedeanGroup.{u2} H _inst_4 _inst_5)
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : TopologicalSpace.{u2} G] [_inst_3 : NonarchimedeanGroup.{u2} G _inst_1 _inst_2] {H : Type.{u1}} [_inst_4 : Group.{u1} H] [_inst_5 : TopologicalSpace.{u1} H] [_inst_6 : TopologicalGroup.{u1} H _inst_5 _inst_4] (f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4)))), (OpenEmbedding.{u2, u1} G H _inst_2 _inst_5 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_4)))))) f)) -> (NonarchimedeanGroup.{u1} H _inst_4 _inst_5)
Case conversion may be inaccurate. Consider using '#align nonarchimedean_group.nonarchimedean_of_emb NonarchimedeanGroup.nonarchimedean_of_embₓ'. -/
/-- If a topological group embeds into a nonarchimedean group, then it is nonarchimedean. -/
@[to_additive NonarchimedeanAddGroup.nonarchimedean_of_emb
      "If a topological group embeds into a\nnonarchimedean group, then it is nonarchimedean."]
theorem nonarchimedean_of_emb (f : G →* H) (emb : OpenEmbedding f) : NonarchimedeanGroup H :=
  {
    is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U ∈ nhds (1 : G) :=
        by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with is_open' := emb.IsOpenMap _ V.IsOpen }, Set.image_subset_iff.2 hV⟩ }
#align nonarchimedean_group.nonarchimedean_of_emb NonarchimedeanGroup.nonarchimedean_of_emb
#align nonarchimedean_add_group.nonarchimedean_of_emb NonarchimedeanAddGroup.nonarchimedean_of_emb

/- warning: nonarchimedean_group.prod_subset -> NonarchimedeanGroup.prod_subset is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : NonarchimedeanGroup.{u1} G _inst_1 _inst_2] {K : Type.{u2}} [_inst_7 : Group.{u2} K] [_inst_8 : TopologicalSpace.{u2} K] [_inst_9 : NonarchimedeanGroup.{u2} K _inst_7 _inst_8] {U : Set.{max u1 u2} (Prod.{u1, u2} G K)}, (Membership.Mem.{max u1 u2, max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} G K)) (Filter.{max u1 u2} (Prod.{u1, u2} G K)) (Filter.hasMem.{max u1 u2} (Prod.{u1, u2} G K)) U (nhds.{max u1 u2} (Prod.{u1, u2} G K) (Prod.topologicalSpace.{u1, u2} G K _inst_2 _inst_8) (OfNat.ofNat.{max u1 u2} (Prod.{u1, u2} G K) 1 (OfNat.mk.{max u1 u2} (Prod.{u1, u2} G K) 1 (One.one.{max u1 u2} (Prod.{u1, u2} G K) (Prod.hasOne.{u1, u2} G K (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u2} K (Monoid.toMulOneClass.{u2} K (DivInvMonoid.toMonoid.{u2} K (Group.toDivInvMonoid.{u2} K _inst_7)))))))))) -> (Exists.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (fun (V : OpenSubgroup.{u1} G _inst_1 _inst_2) => Exists.{succ u2} (OpenSubgroup.{u2} K _inst_7 _inst_8) (fun (W : OpenSubgroup.{u2} K _inst_7 _inst_8) => HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} G K)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} G K)) (Set.prod.{u1, u2} G K ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) V) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (OpenSubgroup.{u2} K _inst_7 _inst_8) (Set.{u2} K) (HasLiftT.mk.{succ u2, succ u2} (OpenSubgroup.{u2} K _inst_7 _inst_8) (Set.{u2} K) (CoeTCₓ.coe.{succ u2, succ u2} (OpenSubgroup.{u2} K _inst_7 _inst_8) (Set.{u2} K) (SetLike.Set.hasCoeT.{u2, u2} (OpenSubgroup.{u2} K _inst_7 _inst_8) K (OpenSubgroup.setLike.{u2} K _inst_7 _inst_8)))) W)) U)))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : TopologicalSpace.{u2} G] [_inst_3 : NonarchimedeanGroup.{u2} G _inst_1 _inst_2] {K : Type.{u1}} [_inst_7 : Group.{u1} K] [_inst_8 : TopologicalSpace.{u1} K] [_inst_9 : NonarchimedeanGroup.{u1} K _inst_7 _inst_8] {U : Set.{max u2 u1} (Prod.{u2, u1} G K)}, (Membership.mem.{max u2 u1, max u2 u1} (Set.{max u2 u1} (Prod.{u2, u1} G K)) (Filter.{max u2 u1} (Prod.{u2, u1} G K)) (instMembershipSetFilter.{max u2 u1} (Prod.{u2, u1} G K)) U (nhds.{max u2 u1} (Prod.{u2, u1} G K) (instTopologicalSpaceProd.{u2, u1} G K _inst_2 _inst_8) (OfNat.ofNat.{max u2 u1} (Prod.{u2, u1} G K) 1 (One.toOfNat1.{max u2 u1} (Prod.{u2, u1} G K) (Prod.instOneProd.{u2, u1} G K (InvOneClass.toOne.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_1)))) (InvOneClass.toOne.{u1} K (DivInvOneMonoid.toInvOneClass.{u1} K (DivisionMonoid.toDivInvOneMonoid.{u1} K (Group.toDivisionMonoid.{u1} K _inst_7))))))))) -> (Exists.{succ u2} (OpenSubgroup.{u2} G _inst_1 _inst_2) (fun (V : OpenSubgroup.{u2} G _inst_1 _inst_2) => Exists.{succ u1} (OpenSubgroup.{u1} K _inst_7 _inst_8) (fun (W : OpenSubgroup.{u1} K _inst_7 _inst_8) => HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} G K)) (Set.instHasSubsetSet.{max u2 u1} (Prod.{u2, u1} G K)) (Set.prod.{u2, u1} G K (SetLike.coe.{u2, u2} (OpenSubgroup.{u2} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u2} G _inst_1 _inst_2) V) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} K _inst_7 _inst_8) K (OpenSubgroup.instSetLikeOpenSubgroup.{u1} K _inst_7 _inst_8) W)) U)))
Case conversion may be inaccurate. Consider using '#align nonarchimedean_group.prod_subset NonarchimedeanGroup.prod_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An open neighborhood of the identity in the cartesian product of two nonarchimedean groups
contains the cartesian product of an open neighborhood in each group. -/
@[to_additive NonarchimedeanAddGroup.prod_subset
      "An open neighborhood of the identity in the\ncartesian product of two nonarchimedean groups contains the cartesian product of an open\nneighborhood in each group."]
theorem prod_subset {U} (hU : U ∈ nhds (1 : G × K)) :
    ∃ (V : OpenSubgroup G)(W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K) ⊆ U :=
  by
  erw [nhds_prod_eq, Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  cases' is_nonarchimedean _ hU₁ with V hV
  cases' is_nonarchimedean _ hU₂ with W hW
  use V; use W
  rw [Set.prod_subset_iff]
  intro x hX y hY
  exact Set.Subset.trans (Set.prod_mono hV hW) h (Set.mem_sep hX hY)
#align nonarchimedean_group.prod_subset NonarchimedeanGroup.prod_subset
#align nonarchimedean_add_group.prod_subset NonarchimedeanAddGroup.prod_subset

/- warning: nonarchimedean_group.prod_self_subset -> NonarchimedeanGroup.prod_self_subset is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : NonarchimedeanGroup.{u1} G _inst_1 _inst_2] {U : Set.{u1} (Prod.{u1, u1} G G)}, (Membership.Mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} G G)) (Filter.{u1} (Prod.{u1, u1} G G)) (Filter.hasMem.{u1} (Prod.{u1, u1} G G)) U (nhds.{u1} (Prod.{u1, u1} G G) (Prod.topologicalSpace.{u1, u1} G G _inst_2 _inst_2) (OfNat.ofNat.{u1} (Prod.{u1, u1} G G) 1 (OfNat.mk.{u1} (Prod.{u1, u1} G G) 1 (One.one.{u1} (Prod.{u1, u1} G G) (Prod.hasOne.{u1, u1} G G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))))) -> (Exists.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (fun (V : OpenSubgroup.{u1} G _inst_1 _inst_2) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} G G)) (Set.hasSubset.{u1} (Prod.{u1, u1} G G)) (Set.prod.{u1, u1} G G ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) V) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) V)) U))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : NonarchimedeanGroup.{u1} G _inst_1 _inst_2] {U : Set.{u1} (Prod.{u1, u1} G G)}, (Membership.mem.{u1, u1} (Set.{u1} (Prod.{u1, u1} G G)) (Filter.{u1} (Prod.{u1, u1} G G)) (instMembershipSetFilter.{u1} (Prod.{u1, u1} G G)) U (nhds.{u1} (Prod.{u1, u1} G G) (instTopologicalSpaceProd.{u1, u1} G G _inst_2 _inst_2) (OfNat.ofNat.{u1} (Prod.{u1, u1} G G) 1 (One.toOfNat1.{u1} (Prod.{u1, u1} G G) (Prod.instOneProd.{u1, u1} G G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))))))))) -> (Exists.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (fun (V : OpenSubgroup.{u1} G _inst_1 _inst_2) => HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} G G)) (Set.instHasSubsetSet.{u1} (Prod.{u1, u1} G G)) (Set.prod.{u1, u1} G G (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) V) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) V)) U))
Case conversion may be inaccurate. Consider using '#align nonarchimedean_group.prod_self_subset NonarchimedeanGroup.prod_self_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An open neighborhood of the identity in the cartesian square of a nonarchimedean group
contains the cartesian square of an open neighborhood in the group. -/
@[to_additive NonarchimedeanAddGroup.prod_self_subset
      "An open neighborhood of the identity in the\ncartesian square of a nonarchimedean group contains the cartesian square of an open neighborhood in\nthe group."]
theorem prod_self_subset {U} (hU : U ∈ nhds (1 : G × G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ×ˢ (V : Set G) ⊆ U :=
  let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine' Set.Subset.trans (Set.prod_mono _ _) ‹_› <;> simp⟩
#align nonarchimedean_group.prod_self_subset NonarchimedeanGroup.prod_self_subset
#align nonarchimedean_add_group.prod_self_subset NonarchimedeanAddGroup.prod_self_subset

/-- The cartesian product of two nonarchimedean groups is nonarchimedean. -/
@[to_additive "The cartesian product of two nonarchimedean groups is nonarchimedean."]
instance : NonarchimedeanGroup (G × K)
    where is_nonarchimedean U hU :=
    let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.Prod W, ‹_›⟩

end NonarchimedeanGroup

namespace NonarchimedeanRing

open NonarchimedeanRing

open NonarchimedeanAddGroup

variable {R S : Type _}

variable [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]

variable [Ring S] [TopologicalSpace S] [NonarchimedeanRing S]

/-- The cartesian product of two nonarchimedean rings is nonarchimedean. -/
instance : NonarchimedeanRing (R × S)
    where is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/- warning: nonarchimedean_ring.left_mul_subset -> NonarchimedeanRing.left_mul_subset is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : NonarchimedeanRing.{u1} R _inst_1 _inst_2] (U : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (r : R), Exists.{succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (fun (V : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) => HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) (SMul.smul.{u1, u1} R (Set.{u1} R) (Set.smulSet.{u1, u1} R R (Mul.toSMul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)))) r ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) R (OpenAddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2)))) V)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) R (OpenAddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2)))) U))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : NonarchimedeanRing.{u1} R _inst_1 _inst_2] (U : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) (r : R), Exists.{succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) (fun (V : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) => HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) (HSMul.hSMul.{u1, u1, u1} R (Set.{u1} R) (Set.{u1} R) (instHSMul.{u1, u1} R (Set.{u1} R) (Set.smulSet.{u1, u1} R R (SMulZeroClass.toSMul.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (SMulWithZero.toSMulZeroClass.{u1, u1} R R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R (Ring.toSemiring.{u1} R _inst_1))) (MulZeroClass.toSMulWithZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))))))) r (SetLike.coe.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) R (OpenAddSubgroup.instSetLikeOpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) V)) (SetLike.coe.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) R (OpenAddSubgroup.instSetLikeOpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) U))
Case conversion may be inaccurate. Consider using '#align nonarchimedean_ring.left_mul_subset NonarchimedeanRing.left_mul_subsetₓ'. -/
/-- Given an open subgroup `U` and an element `r` of a nonarchimedean ring, there is an open
  subgroup `V` such that `r • V` is contained in `U`. -/
theorem left_mul_subset (U : OpenAddSubgroup R) (r : R) :
    ∃ V : OpenAddSubgroup R, r • (V : Set R) ⊆ U :=
  ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_mul_left r), (U : Set R).image_preimage_subset _⟩
#align nonarchimedean_ring.left_mul_subset NonarchimedeanRing.left_mul_subset

/- warning: nonarchimedean_ring.mul_subset -> NonarchimedeanRing.mul_subset is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : NonarchimedeanRing.{u1} R _inst_1 _inst_2] (U : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2), Exists.{succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (fun (V : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) => HasSubset.Subset.{u1} (Set.{u1} R) (Set.hasSubset.{u1} R) (HMul.hMul.{u1, u1, u1} (Set.{u1} R) (Set.{u1} R) (Set.{u1} R) (instHMul.{u1} (Set.{u1} R) (Set.mul.{u1} R (Distrib.toHasMul.{u1} R (Ring.toDistrib.{u1} R _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) R (OpenAddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2)))) V) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) R (OpenAddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2)))) V)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2) R (OpenAddSubgroup.setLike.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (NonAssocRing.toAddGroupWithOne.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))) _inst_2)))) U))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Ring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : NonarchimedeanRing.{u1} R _inst_1 _inst_2] (U : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2), Exists.{succ u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) (fun (V : OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) => HasSubset.Subset.{u1} (Set.{u1} R) (Set.instHasSubsetSet.{u1} R) (HMul.hMul.{u1, u1, u1} (Set.{u1} R) (Set.{u1} R) (Set.{u1} R) (instHMul.{u1} (Set.{u1} R) (Set.mul.{u1} R (NonUnitalNonAssocRing.toMul.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R _inst_1))))) (SetLike.coe.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) R (OpenAddSubgroup.instSetLikeOpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) V) (SetLike.coe.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) R (OpenAddSubgroup.instSetLikeOpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) V)) (SetLike.coe.{u1, u1} (OpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) R (OpenAddSubgroup.instSetLikeOpenAddSubgroup.{u1} R (AddGroupWithOne.toAddGroup.{u1} R (Ring.toAddGroupWithOne.{u1} R _inst_1)) _inst_2) U))
Case conversion may be inaccurate. Consider using '#align nonarchimedean_ring.mul_subset NonarchimedeanRing.mul_subsetₓ'. -/
/-- An open subgroup of a nonarchimedean ring contains the square of another one. -/
theorem mul_subset (U : OpenAddSubgroup R) : ∃ V : OpenAddSubgroup R, (V : Set R) * V ⊆ U :=
  by
  let ⟨V, H⟩ :=
    prod_self_subset
      (IsOpen.mem_nhds (IsOpen.preimage continuous_mul U.IsOpen)
        (by
          simpa only [Set.mem_preimage, SetLike.mem_coe, Prod.snd_zero, MulZeroClass.mul_zero] using
            U.zero_mem))
  use V
  rintro v ⟨a, b, ha, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe] at hy
  rwa [hv] at hy
#align nonarchimedean_ring.mul_subset NonarchimedeanRing.mul_subset

end NonarchimedeanRing

