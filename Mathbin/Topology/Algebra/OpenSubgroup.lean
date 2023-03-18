/-
Copyright (c) 2019 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.algebra.open_subgroup
! leanprover-community/mathlib commit 83f81aea33931a1edb94ce0f32b9a5d484de6978
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.Topology.Algebra.Ring.Basic
import Mathbin.Topology.Sets.Opens

/-!
# Open subgroups of a topological groups

This files builds the lattice `open_subgroup G` of open subgroups in a topological group `G`,
and its additive version `open_add_subgroup`.  This lattice has a top element, the subgroup of all
elements, but no bottom element in general. The trivial subgroup which is the natural candidate
bottom has no reason to be open (this happens only in discrete groups).

Note that this notion is especially relevant in a non-archimedean context, for instance for
`p`-adic groups.

## Main declarations

* `open_subgroup.is_closed`: An open subgroup is automatically closed.
* `subgroup.is_open_mono`: A subgroup containing an open subgroup is open.
                           There are also versions for additive groups, submodules and ideals.
* `open_subgroup.comap`: Open subgroups can be pulled back by a continuous group morphism.

## TODO
* Prove that the identity component of a locally path connected group is an open subgroup.
  Up to now this file is really geared towards non-archimedean algebra, not Lie groups.
-/


open TopologicalSpace

open Topology

#print OpenAddSubgroup /-
/-- The type of open subgroups of a topological additive group. -/
structure OpenAddSubgroup (G : Type _) [AddGroup G] [TopologicalSpace G] extends AddSubgroup G where
  is_open' : IsOpen carrier
#align open_add_subgroup OpenAddSubgroup
-/

#print OpenSubgroup /-
/-- The type of open subgroups of a topological group. -/
@[to_additive]
structure OpenSubgroup (G : Type _) [Group G] [TopologicalSpace G] extends Subgroup G where
  is_open' : IsOpen carrier
#align open_subgroup OpenSubgroup
#align open_add_subgroup OpenAddSubgroup
-/

/-- Reinterpret an `open_subgroup` as a `subgroup`. -/
add_decl_doc OpenSubgroup.toSubgroup

/-- Reinterpret an `open_add_subgroup` as an `add_subgroup`. -/
add_decl_doc OpenAddSubgroup.toAddSubgroup

namespace OpenSubgroup

open Function TopologicalSpace

variable {G : Type _} [Group G] [TopologicalSpace G]

variable {U V : OpenSubgroup G} {g : G}

/- warning: open_subgroup.has_coe_subgroup -> OpenSubgroup.hasCoeSubgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], CoeTCₓ.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], CoeTC.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align open_subgroup.has_coe_subgroup OpenSubgroup.hasCoeSubgroupₓ'. -/
@[to_additive]
instance hasCoeSubgroup : CoeTC (OpenSubgroup G) (Subgroup G) :=
  ⟨toSubgroup⟩
#align open_subgroup.has_coe_subgroup OpenSubgroup.hasCoeSubgroup
#align open_add_subgroup.has_coe_add_subgroup OpenAddSubgroup.hasCoeAddSubgroup

#print OpenSubgroup.toSubgroup_injective /-
@[to_additive]
theorem toSubgroup_injective : Injective (coe : OpenSubgroup G → Subgroup G)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align open_subgroup.coe_subgroup_injective OpenSubgroup.toSubgroup_injective
#align open_add_subgroup.coe_add_subgroup_injective OpenAddSubgroup.toAddSubgroup_injective
-/

@[to_additive]
instance : SetLike (OpenSubgroup G) G where
  coe U := U.1
  coe_injective' _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : SubgroupClass (OpenSubgroup G) G
    where
  mul_mem U _ _ := U.mul_mem'
  one_mem U := U.one_mem'
  inv_mem U _ := U.inv_mem'

/- warning: open_subgroup.has_coe_opens -> OpenSubgroup.hasCoeOpens is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], CoeTCₓ.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], CoeTC.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2)
Case conversion may be inaccurate. Consider using '#align open_subgroup.has_coe_opens OpenSubgroup.hasCoeOpensₓ'. -/
@[to_additive]
instance hasCoeOpens : CoeTC (OpenSubgroup G) (Opens G) :=
  ⟨fun U => ⟨U, U.is_open'⟩⟩
#align open_subgroup.has_coe_opens OpenSubgroup.hasCoeOpens
#align open_add_subgroup.has_coe_opens OpenAddSubgroup.hasCoeOpens

/- warning: open_subgroup.coe_coe_opens -> OpenSubgroup.coe_toOpens is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Set.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (TopologicalSpace.Opens.{u1} G _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} G _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (TopologicalSpace.Opens.{u1} G _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (TopologicalSpace.Opens.{u1} G _inst_2) G (TopologicalSpace.Opens.setLike.{u1} G _inst_2)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.hasCoeOpens.{u1} G _inst_1 _inst_2))) U)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Set.{u1} G) (SetLike.coe.{u1, u1} (TopologicalSpace.Opens.{u1} G _inst_2) G (TopologicalSpace.Opens.instSetLikeOpens.{u1} G _inst_2) (OpenSubgroup.toOpens.{u1} G _inst_1 _inst_2 U)) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_coe_opens OpenSubgroup.coe_toOpensₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_toOpens : ((U : Opens G) : Set G) = U :=
  rfl
#align open_subgroup.coe_coe_opens OpenSubgroup.coe_toOpens
#align open_add_subgroup.coe_coe_opens OpenAddSubgroup.coe_toOpens

/- warning: open_subgroup.coe_coe_subgroup -> OpenSubgroup.coe_toSubgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Set.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Set.{u1} G) (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 U)) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_coe_subgroup OpenSubgroup.coe_toSubgroupₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_toSubgroup : ((U : Subgroup G) : Set G) = U :=
  rfl
#align open_subgroup.coe_coe_subgroup OpenSubgroup.coe_toSubgroup
#align open_add_subgroup.coe_coe_add_subgroup OpenAddSubgroup.coe_toAddSubgroup

/- warning: open_subgroup.mem_coe_opens -> OpenSubgroup.mem_toOpens is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {g : G}, Iff (Membership.Mem.{u1, u1} G (TopologicalSpace.Opens.{u1} G _inst_2) (SetLike.hasMem.{u1, u1} (TopologicalSpace.Opens.{u1} G _inst_2) G (TopologicalSpace.Opens.setLike.{u1} G _inst_2)) g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.hasCoeOpens.{u1} G _inst_1 _inst_2))) U)) (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) g U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {g : G}, Iff (Membership.mem.{u1, u1} G (TopologicalSpace.Opens.{u1} G _inst_2) (SetLike.instMembership.{u1, u1} (TopologicalSpace.Opens.{u1} G _inst_2) G (TopologicalSpace.Opens.instSetLikeOpens.{u1} G _inst_2)) g (OpenSubgroup.toOpens.{u1} G _inst_1 _inst_2 U)) (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) g U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.mem_coe_opens OpenSubgroup.mem_toOpensₓ'. -/
@[simp, norm_cast, to_additive]
theorem mem_toOpens : g ∈ (U : Opens G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe_opens OpenSubgroup.mem_toOpens
#align open_add_subgroup.mem_coe_opens OpenAddSubgroup.mem_toOpens

/- warning: open_subgroup.mem_coe_subgroup -> OpenSubgroup.mem_toSubgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {g : G}, Iff (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U)) (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) g U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {g : G}, Iff (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) g (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 U)) (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) g U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.mem_coe_subgroup OpenSubgroup.mem_toSubgroupₓ'. -/
@[simp, norm_cast, to_additive]
theorem mem_toSubgroup : g ∈ (U : Subgroup G) ↔ g ∈ U :=
  Iff.rfl
#align open_subgroup.mem_coe_subgroup OpenSubgroup.mem_toSubgroup
#align open_add_subgroup.mem_coe_add_subgroup OpenAddSubgroup.mem_toAddSubgroup

/- warning: open_subgroup.ext -> OpenSubgroup.ext is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, (forall (x : G), Iff (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x U) (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x V)) -> (Eq.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) U V)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, (forall (x : G), Iff (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x U) (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x V)) -> (Eq.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) U V)
Case conversion may be inaccurate. Consider using '#align open_subgroup.ext OpenSubgroup.extₓ'. -/
@[ext, to_additive]
theorem ext (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h
#align open_subgroup.ext OpenSubgroup.ext
#align open_add_subgroup.ext OpenAddSubgroup.ext

variable (U)

/- warning: open_subgroup.is_open -> OpenSubgroup.isOpen is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), IsOpen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), IsOpen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.is_open OpenSubgroup.isOpenₓ'. -/
@[to_additive]
protected theorem isOpen : IsOpen (U : Set G) :=
  U.is_open'
#align open_subgroup.is_open OpenSubgroup.isOpen
#align open_add_subgroup.is_open OpenAddSubgroup.isOpen

/- warning: open_subgroup.mem_nhds_one -> OpenSubgroup.mem_nhds_one is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U) (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U) (nhds.{u1} G _inst_2 (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align open_subgroup.mem_nhds_one OpenSubgroup.mem_nhds_oneₓ'. -/
@[to_additive]
theorem mem_nhds_one : (U : Set G) ∈ 𝓝 (1 : G) :=
  IsOpen.mem_nhds U.IsOpen U.one_mem
#align open_subgroup.mem_nhds_one OpenSubgroup.mem_nhds_one
#align open_add_subgroup.mem_nhds_zero OpenAddSubgroup.mem_nhds_zero

variable {U}

@[to_additive]
instance : Top (OpenSubgroup G) :=
  ⟨{ (⊤ : Subgroup G) with is_open' := isOpen_univ }⟩

/- warning: open_subgroup.mem_top -> OpenSubgroup.mem_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] (x : G), Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasTop.{u1} G _inst_1 _inst_2))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] (x : G), Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instTopOpenSubgroup.{u1} G _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align open_subgroup.mem_top OpenSubgroup.mem_topₓ'. -/
@[simp, to_additive]
theorem mem_top (x : G) : x ∈ (⊤ : OpenSubgroup G) :=
  trivial
#align open_subgroup.mem_top OpenSubgroup.mem_top
#align open_add_subgroup.mem_top OpenAddSubgroup.mem_top

/- warning: open_subgroup.coe_top -> OpenSubgroup.coe_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], Eq.{succ u1} (Set.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasTop.{u1} G _inst_1 _inst_2))) (Set.univ.{u1} G)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], Eq.{succ u1} (Set.{u1} G) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instTopOpenSubgroup.{u1} G _inst_1 _inst_2))) (Set.univ.{u1} G)
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_top OpenSubgroup.coe_topₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_top : ((⊤ : OpenSubgroup G) : Set G) = Set.univ :=
  rfl
#align open_subgroup.coe_top OpenSubgroup.coe_top
#align open_add_subgroup.coe_top OpenAddSubgroup.coe_top

/- warning: open_subgroup.coe_subgroup_top -> OpenSubgroup.toSubgroup_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], Eq.{succ u1} (Subgroup.{u1} G _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasTop.{u1} G _inst_1 _inst_2))) (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], Eq.{succ u1} (Subgroup.{u1} G _inst_1) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instTopOpenSubgroup.{u1} G _inst_1 _inst_2))) (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_subgroup_top OpenSubgroup.toSubgroup_topₓ'. -/
@[simp, norm_cast, to_additive]
theorem toSubgroup_top : ((⊤ : OpenSubgroup G) : Subgroup G) = ⊤ :=
  rfl
#align open_subgroup.coe_subgroup_top OpenSubgroup.toSubgroup_top
#align open_add_subgroup.coe_add_subgroup_top OpenAddSubgroup.toAddSubgroup_top

/- warning: open_subgroup.coe_opens_top -> OpenSubgroup.toOpens_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], Eq.{succ u1} (TopologicalSpace.Opens.{u1} G _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.hasCoeOpens.{u1} G _inst_1 _inst_2))) (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasTop.{u1} G _inst_1 _inst_2))) (Top.top.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (CompleteLattice.toHasTop.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} G _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G], Eq.{succ u1} (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.toOpens.{u1} G _inst_1 _inst_2 (Top.top.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instTopOpenSubgroup.{u1} G _inst_1 _inst_2))) (Top.top.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (CompleteLattice.toTop.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} G _inst_2)))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_opens_top OpenSubgroup.toOpens_topₓ'. -/
@[simp, norm_cast, to_additive]
theorem toOpens_top : ((⊤ : OpenSubgroup G) : Opens G) = ⊤ :=
  rfl
#align open_subgroup.coe_opens_top OpenSubgroup.toOpens_top
#align open_add_subgroup.coe_opens_top OpenAddSubgroup.toOpens_top

@[to_additive]
instance : Inhabited (OpenSubgroup G) :=
  ⟨⊤⟩

/- warning: open_subgroup.is_closed -> OpenSubgroup.isClosed is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), IsClosed.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), IsClosed.{u1} G _inst_2 (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.is_closed OpenSubgroup.isClosedₓ'. -/
@[to_additive]
theorem isClosed [ContinuousMul G] (U : OpenSubgroup G) : IsClosed (U : Set G) :=
  by
  apply isOpen_compl_iff.1
  refine' isOpen_iff_forall_mem_open.2 fun x hx => ⟨(fun y => y * x⁻¹) ⁻¹' U, _, _, _⟩
  · refine' fun u hux hu => hx _
    simp only [Set.mem_preimage, SetLike.mem_coe] at hux hu⊢
    convert U.mul_mem (U.inv_mem hux) hu
    simp
  · exact U.is_open.preimage (continuous_mul_right _)
  · simp [one_mem]
#align open_subgroup.is_closed OpenSubgroup.isClosed
#align open_add_subgroup.is_closed OpenAddSubgroup.isClosed

/- warning: open_subgroup.is_clopen -> OpenSubgroup.isClopen is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), IsClopen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (U : OpenSubgroup.{u1} G _inst_1 _inst_2), IsClopen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U)
Case conversion may be inaccurate. Consider using '#align open_subgroup.is_clopen OpenSubgroup.isClopenₓ'. -/
@[to_additive]
theorem isClopen [ContinuousMul G] (U : OpenSubgroup G) : IsClopen (U : Set G) :=
  ⟨U.IsOpen, U.IsClosed⟩
#align open_subgroup.is_clopen OpenSubgroup.isClopen
#align open_add_subgroup.is_clopen OpenAddSubgroup.isClopen

section

variable {H : Type _} [Group H] [TopologicalSpace H]

/- warning: open_subgroup.prod -> OpenSubgroup.prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] [_inst_4 : TopologicalSpace.{u2} H], (OpenSubgroup.{u1} G _inst_1 _inst_2) -> (OpenSubgroup.{u2} H _inst_3 _inst_4) -> (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] [_inst_4 : TopologicalSpace.{u2} H], (OpenSubgroup.{u1} G _inst_1 _inst_2) -> (OpenSubgroup.{u2} H _inst_3 _inst_4) -> (OpenSubgroup.{max u2 u1} (Prod.{u1, u2} G H) (Prod.instGroupProd.{u1, u2} G H _inst_1 _inst_3) (instTopologicalSpaceProd.{u1, u2} G H _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align open_subgroup.prod OpenSubgroup.prodₓ'. -/
/-- The product of two open subgroups as an open subgroup of the product group. -/
@[to_additive "The product of two open subgroups as an open subgroup of the product group."]
def prod (U : OpenSubgroup G) (V : OpenSubgroup H) : OpenSubgroup (G × H) :=
  { (U : Subgroup G).Prod (V : Subgroup H) with is_open' := U.IsOpen.Prod V.IsOpen }
#align open_subgroup.prod OpenSubgroup.prod
#align open_add_subgroup.sum OpenAddSubgroup.sum

/- warning: open_subgroup.coe_prod -> OpenSubgroup.coe_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] [_inst_4 : TopologicalSpace.{u2} H] (U : OpenSubgroup.{u1} G _inst_1 _inst_2) (V : OpenSubgroup.{u2} H _inst_3 _inst_4), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} G H)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Set.{max u1 u2} (Prod.{u1, u2} G H)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Set.{max u1 u2} (Prod.{u1, u2} G H)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Set.{max u1 u2} (Prod.{u1, u2} G H)) (SetLike.Set.hasCoeT.{max u1 u2, max u1 u2} (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Prod.{u1, u2} G H) (OpenSubgroup.setLike.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4))))) (OpenSubgroup.prod.{u1, u2} G _inst_1 _inst_2 H _inst_3 _inst_4 U V)) (Set.prod.{u1, u2} G H ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (OpenSubgroup.{u2} H _inst_3 _inst_4) (Set.{u2} H) (HasLiftT.mk.{succ u2, succ u2} (OpenSubgroup.{u2} H _inst_3 _inst_4) (Set.{u2} H) (CoeTCₓ.coe.{succ u2, succ u2} (OpenSubgroup.{u2} H _inst_3 _inst_4) (Set.{u2} H) (SetLike.Set.hasCoeT.{u2, u2} (OpenSubgroup.{u2} H _inst_3 _inst_4) H (OpenSubgroup.setLike.{u2} H _inst_3 _inst_4)))) V))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : TopologicalSpace.{u2} G] {H : Type.{u1}} [_inst_3 : Group.{u1} H] [_inst_4 : TopologicalSpace.{u1} H] (U : OpenSubgroup.{u2} G _inst_1 _inst_2) (V : OpenSubgroup.{u1} H _inst_3 _inst_4), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} G H)) (SetLike.coe.{max u2 u1, max u2 u1} (OpenSubgroup.{max u1 u2} (Prod.{u2, u1} G H) (Prod.instGroupProd.{u2, u1} G H _inst_1 _inst_3) (instTopologicalSpaceProd.{u2, u1} G H _inst_2 _inst_4)) (Prod.{u2, u1} G H) (OpenSubgroup.instSetLikeOpenSubgroup.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instGroupProd.{u2, u1} G H _inst_1 _inst_3) (instTopologicalSpaceProd.{u2, u1} G H _inst_2 _inst_4)) (OpenSubgroup.prod.{u2, u1} G _inst_1 _inst_2 H _inst_3 _inst_4 U V)) (Set.prod.{u2, u1} G H (SetLike.coe.{u2, u2} (OpenSubgroup.{u2} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u2} G _inst_1 _inst_2) U) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} H _inst_3 _inst_4) H (OpenSubgroup.instSetLikeOpenSubgroup.{u1} H _inst_3 _inst_4) V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_prod OpenSubgroup.coe_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, norm_cast, to_additive]
theorem coe_prod (U : OpenSubgroup G) (V : OpenSubgroup H) : (U.Prod V : Set (G × H)) = U ×ˢ V :=
  rfl
#align open_subgroup.coe_prod OpenSubgroup.coe_prod
#align open_add_subgroup.coe_sum OpenAddSubgroup.coe_sum

/- warning: open_subgroup.coe_subgroup_prod -> OpenSubgroup.toSubgroup_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {H : Type.{u2}} [_inst_3 : Group.{u2} H] [_inst_4 : TopologicalSpace.{u2} H] (U : OpenSubgroup.{u1} G _inst_1 _inst_2) (V : OpenSubgroup.{u2} H _inst_3 _inst_4), Eq.{succ (max u1 u2)} (Subgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Subgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Subgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (OpenSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)) (Subgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3)) (OpenSubgroup.hasCoeSubgroup.{max u1 u2} (Prod.{u1, u2} G H) (Prod.group.{u1, u2} G H _inst_1 _inst_3) (Prod.topologicalSpace.{u1, u2} G H _inst_2 _inst_4)))) (OpenSubgroup.prod.{u1, u2} G _inst_1 _inst_2 H _inst_3 _inst_4 U V)) (Subgroup.prod.{u1, u2} G _inst_1 H _inst_3 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (OpenSubgroup.{u2} H _inst_3 _inst_4) (Subgroup.{u2} H _inst_3) (HasLiftT.mk.{succ u2, succ u2} (OpenSubgroup.{u2} H _inst_3 _inst_4) (Subgroup.{u2} H _inst_3) (CoeTCₓ.coe.{succ u2, succ u2} (OpenSubgroup.{u2} H _inst_3 _inst_4) (Subgroup.{u2} H _inst_3) (OpenSubgroup.hasCoeSubgroup.{u2} H _inst_3 _inst_4))) V))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] [_inst_2 : TopologicalSpace.{u2} G] {H : Type.{u1}} [_inst_3 : Group.{u1} H] [_inst_4 : TopologicalSpace.{u1} H] (U : OpenSubgroup.{u2} G _inst_1 _inst_2) (V : OpenSubgroup.{u1} H _inst_3 _inst_4), Eq.{max (succ u2) (succ u1)} (Subgroup.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instGroupProd.{u2, u1} G H _inst_1 _inst_3)) (OpenSubgroup.toSubgroup.{max u2 u1} (Prod.{u2, u1} G H) (Prod.instGroupProd.{u2, u1} G H _inst_1 _inst_3) (instTopologicalSpaceProd.{u2, u1} G H _inst_2 _inst_4) (OpenSubgroup.prod.{u2, u1} G _inst_1 _inst_2 H _inst_3 _inst_4 U V)) (Subgroup.prod.{u2, u1} G _inst_1 H _inst_3 (OpenSubgroup.toSubgroup.{u2} G _inst_1 _inst_2 U) (OpenSubgroup.toSubgroup.{u1} H _inst_3 _inst_4 V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_subgroup_prod OpenSubgroup.toSubgroup_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem toSubgroup_prod (U : OpenSubgroup G) (V : OpenSubgroup H) :
    (U.Prod V : Subgroup (G × H)) = (U : Subgroup G).Prod V :=
  rfl
#align open_subgroup.coe_subgroup_prod OpenSubgroup.toSubgroup_prod
#align open_add_subgroup.coe_add_subgroup_sum OpenAddSubgroup.toAddSubgroup_sum

end

@[to_additive]
instance : Inf (OpenSubgroup G) :=
  ⟨fun U V => ⟨U ⊓ V, U.IsOpen.inter V.IsOpen⟩⟩

/- warning: open_subgroup.coe_inf -> OpenSubgroup.coe_inf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Set.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasInf.{u1} G _inst_1 _inst_2) U V)) (Inter.inter.{u1} (Set.{u1} G) (Set.hasInter.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) V))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Set.{u1} G) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instInfOpenSubgroup.{u1} G _inst_1 _inst_2) U V)) (Inter.inter.{u1} (Set.{u1} G) (Set.instInterSet.{u1} G) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) U) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_inf OpenSubgroup.coe_infₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_inf : (↑(U ⊓ V) : Set G) = (U : Set G) ∩ V :=
  rfl
#align open_subgroup.coe_inf OpenSubgroup.coe_inf
#align open_add_subgroup.coe_inf OpenAddSubgroup.coe_inf

/- warning: open_subgroup.coe_subgroup_inf -> OpenSubgroup.toSubgroup_inf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Subgroup.{u1} G _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasInf.{u1} G _inst_1 _inst_2) U V)) (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasInf.{u1} G _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) V))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (Subgroup.{u1} G _inst_1) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instInfOpenSubgroup.{u1} G _inst_1 _inst_2) U V)) (Inf.inf.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instInfSubgroup.{u1} G _inst_1) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 U) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_subgroup_inf OpenSubgroup.toSubgroup_infₓ'. -/
@[simp, norm_cast, to_additive]
theorem toSubgroup_inf : (↑(U ⊓ V) : Subgroup G) = ↑U ⊓ ↑V :=
  rfl
#align open_subgroup.coe_subgroup_inf OpenSubgroup.toSubgroup_inf
#align open_add_subgroup.coe_add_subgroup_inf OpenAddSubgroup.toAddSubgroup_inf

/- warning: open_subgroup.coe_opens_inf -> OpenSubgroup.toOpens_inf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (TopologicalSpace.Opens.{u1} G _inst_2) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.hasCoeOpens.{u1} G _inst_1 _inst_2))) (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasInf.{u1} G _inst_1 _inst_2) U V)) (Inf.inf.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (SemilatticeInf.toHasInf.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (Lattice.toSemilatticeInf.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (TopologicalSpace.Opens.completeLattice.{u1} G _inst_2))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.hasCoeOpens.{u1} G _inst_1 _inst_2))) U) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.hasCoeOpens.{u1} G _inst_1 _inst_2))) V))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Eq.{succ u1} (TopologicalSpace.Opens.{u1} G _inst_2) (OpenSubgroup.toOpens.{u1} G _inst_1 _inst_2 (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instInfOpenSubgroup.{u1} G _inst_1 _inst_2) U V)) (Inf.inf.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (Lattice.toInf.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (ConditionallyCompleteLattice.toLattice.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (CompleteLattice.toConditionallyCompleteLattice.{u1} (TopologicalSpace.Opens.{u1} G _inst_2) (TopologicalSpace.Opens.instCompleteLatticeOpens.{u1} G _inst_2)))) (OpenSubgroup.toOpens.{u1} G _inst_1 _inst_2 U) (OpenSubgroup.toOpens.{u1} G _inst_1 _inst_2 V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_opens_inf OpenSubgroup.toOpens_infₓ'. -/
@[simp, norm_cast, to_additive]
theorem toOpens_inf : (↑(U ⊓ V) : Opens G) = ↑U ⊓ ↑V :=
  rfl
#align open_subgroup.coe_opens_inf OpenSubgroup.toOpens_inf
#align open_add_subgroup.coe_opens_inf OpenAddSubgroup.toOpens_inf

/- warning: open_subgroup.mem_inf -> OpenSubgroup.mem_inf is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2} {x : G}, Iff (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasInf.{u1} G _inst_1 _inst_2) U V)) (And (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x U) (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x V))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2} {x : G}, Iff (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x (Inf.inf.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instInfOpenSubgroup.{u1} G _inst_1 _inst_2) U V)) (And (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x U) (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.mem_inf OpenSubgroup.mem_infₓ'. -/
@[simp, to_additive]
theorem mem_inf {x} : x ∈ U ⊓ V ↔ x ∈ U ∧ x ∈ V :=
  Iff.rfl
#align open_subgroup.mem_inf OpenSubgroup.mem_inf
#align open_add_subgroup.mem_inf OpenAddSubgroup.mem_inf

@[to_additive]
instance : SemilatticeInf (OpenSubgroup G) :=
  { SetLike.partialOrder,
    SetLike.coe_injective.SemilatticeInf (coe : OpenSubgroup G → Set G) fun _ _ => rfl with }

@[to_additive]
instance : OrderTop (OpenSubgroup G) where
  top := ⊤
  le_top U := Set.subset_univ _

/- warning: open_subgroup.coe_subgroup_le -> OpenSubgroup.toSubgroup_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Iff (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) V)) (LE.le.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Preorder.toLE.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (PartialOrder.toPreorder.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.partialOrder.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) U V)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {U : OpenSubgroup.{u1} G _inst_1 _inst_2} {V : OpenSubgroup.{u1} G _inst_1 _inst_2}, Iff (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 U) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 V)) (LE.le.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Preorder.toLE.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (PartialOrder.toPreorder.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instPartialOrderOpenSubgroup.{u1} G _inst_1 _inst_2))) U V)
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_subgroup_le OpenSubgroup.toSubgroup_leₓ'. -/
@[simp, norm_cast, to_additive]
theorem toSubgroup_le : (U : Subgroup G) ≤ (V : Subgroup G) ↔ U ≤ V :=
  Iff.rfl
#align open_subgroup.coe_subgroup_le OpenSubgroup.toSubgroup_le
#align open_add_subgroup.coe_add_subgroup_le OpenAddSubgroup.toAddSubgroup_le

variable {N : Type _} [Group N] [TopologicalSpace N]

/- warning: open_subgroup.comap -> OpenSubgroup.comap is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))), (Continuous.{u1, u2} G N _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f)) -> (OpenSubgroup.{u2} N _inst_3 _inst_4) -> (OpenSubgroup.{u1} G _inst_1 _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))), (Continuous.{u1, u2} G N _inst_2 _inst_4 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f)) -> (OpenSubgroup.{u2} N _inst_3 _inst_4) -> (OpenSubgroup.{u1} G _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align open_subgroup.comap OpenSubgroup.comapₓ'. -/
/-- The preimage of an `open_subgroup` along a continuous `monoid` homomorphism
  is an `open_subgroup`. -/
@[to_additive
      "The preimage of an `open_add_subgroup` along a continuous `add_monoid` homomorphism\nis an `open_add_subgroup`."]
def comap (f : G →* N) (hf : Continuous f) (H : OpenSubgroup N) : OpenSubgroup G :=
  { (H : Subgroup N).comap f with is_open' := H.IsOpen.Preimage hf }
#align open_subgroup.comap OpenSubgroup.comap
#align open_add_subgroup.comap OpenAddSubgroup.comap

/- warning: open_subgroup.coe_comap -> OpenSubgroup.coe_comap is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] (H : OpenSubgroup.{u2} N _inst_3 _inst_4) (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (hf : Continuous.{u1, u2} G N _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f)), Eq.{succ u1} (Set.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)))) (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f hf H)) (Set.preimage.{u1, u2} G N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (OpenSubgroup.{u2} N _inst_3 _inst_4) (Set.{u2} N) (HasLiftT.mk.{succ u2, succ u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) (Set.{u2} N) (CoeTCₓ.coe.{succ u2, succ u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) (Set.{u2} N) (SetLike.Set.hasCoeT.{u2, u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) N (OpenSubgroup.setLike.{u2} N _inst_3 _inst_4)))) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] (H : OpenSubgroup.{u2} N _inst_3 _inst_4) (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (hf : Continuous.{u1, u2} G N _inst_2 _inst_4 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f)), Eq.{succ u1} (Set.{u1} G) (SetLike.coe.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f hf H)) (Set.preimage.{u1, u2} G N (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f) (SetLike.coe.{u2, u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) N (OpenSubgroup.instSetLikeOpenSubgroup.{u2} N _inst_3 _inst_4) H))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_comap OpenSubgroup.coe_comapₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Set G) = f ⁻¹' H :=
  rfl
#align open_subgroup.coe_comap OpenSubgroup.coe_comap
#align open_add_subgroup.coe_comap OpenAddSubgroup.coe_comap

/- warning: open_subgroup.coe_subgroup_comap -> OpenSubgroup.toSubgroup_comap is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] (H : OpenSubgroup.{u2} N _inst_3 _inst_4) (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (hf : Continuous.{u1, u2} G N _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f)), Eq.{succ u1} (Subgroup.{u1} G _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f hf H)) (Subgroup.comap.{u1, u2} G _inst_1 N _inst_3 f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (OpenSubgroup.{u2} N _inst_3 _inst_4) (Subgroup.{u2} N _inst_3) (HasLiftT.mk.{succ u2, succ u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) (Subgroup.{u2} N _inst_3) (CoeTCₓ.coe.{succ u2, succ u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) (Subgroup.{u2} N _inst_3) (OpenSubgroup.hasCoeSubgroup.{u2} N _inst_3 _inst_4))) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] (H : OpenSubgroup.{u2} N _inst_3 _inst_4) (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (hf : Continuous.{u1, u2} G N _inst_2 _inst_4 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f)), Eq.{succ u1} (Subgroup.{u1} G _inst_1) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f hf H)) (Subgroup.comap.{u1, u2} G _inst_1 N _inst_3 f (OpenSubgroup.toSubgroup.{u2} N _inst_3 _inst_4 H))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_subgroup_comap OpenSubgroup.toSubgroup_comapₓ'. -/
@[simp, norm_cast, to_additive]
theorem toSubgroup_comap (H : OpenSubgroup N) (f : G →* N) (hf : Continuous f) :
    (H.comap f hf : Subgroup G) = (H : Subgroup N).comap f :=
  rfl
#align open_subgroup.coe_subgroup_comap OpenSubgroup.toSubgroup_comap
#align open_add_subgroup.coe_add_subgroup_comap OpenAddSubgroup.toAddSubgroup_comap

/- warning: open_subgroup.mem_comap -> OpenSubgroup.mem_comap is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] {H : OpenSubgroup.{u2} N _inst_3 _inst_4} {f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))} {hf : Continuous.{u1, u2} G N _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f)} {x : G}, Iff (Membership.Mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.hasMem.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.setLike.{u1} G _inst_1 _inst_2)) x (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f hf H)) (Membership.Mem.{u2, u2} N (OpenSubgroup.{u2} N _inst_3 _inst_4) (SetLike.hasMem.{u2, u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) N (OpenSubgroup.setLike.{u2} N _inst_3 _inst_4)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f x) H)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] {H : OpenSubgroup.{u2} N _inst_3 _inst_4} {f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))} {hf : Continuous.{u1, u2} G N _inst_2 _inst_4 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f)} {x : G}, Iff (Membership.mem.{u1, u1} G (OpenSubgroup.{u1} G _inst_1 _inst_2) (SetLike.instMembership.{u1, u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) G (OpenSubgroup.instSetLikeOpenSubgroup.{u1} G _inst_1 _inst_2)) x (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f hf H)) (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) x) (OpenSubgroup.{u2} N _inst_3 _inst_4) (SetLike.instMembership.{u2, u2} (OpenSubgroup.{u2} N _inst_3 _inst_4) N (OpenSubgroup.instSetLikeOpenSubgroup.{u2} N _inst_3 _inst_4)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f x) H)
Case conversion may be inaccurate. Consider using '#align open_subgroup.mem_comap OpenSubgroup.mem_comapₓ'. -/
@[simp, to_additive]
theorem mem_comap {H : OpenSubgroup N} {f : G →* N} {hf : Continuous f} {x : G} :
    x ∈ H.comap f hf ↔ f x ∈ H :=
  Iff.rfl
#align open_subgroup.mem_comap OpenSubgroup.mem_comap
#align open_add_subgroup.mem_comap OpenAddSubgroup.mem_comap

/- warning: open_subgroup.comap_comap -> OpenSubgroup.comap_comap is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] {P : Type.{u3}} [_inst_5 : Group.{u3} P] [_inst_6 : TopologicalSpace.{u3} P] (K : OpenSubgroup.{u3} P _inst_5 _inst_6) (f₂ : MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) (hf₂ : Continuous.{u2, u3} N P _inst_4 _inst_6 (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) (fun (_x : MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) => N -> P) (MonoidHom.hasCoeToFun.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) f₂)) (f₁ : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (hf₁ : Continuous.{u1, u2} G N _inst_2 _inst_4 (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f₁)), Eq.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f₁ hf₁ (OpenSubgroup.comap.{u2, u3} N _inst_3 _inst_4 P _inst_5 _inst_6 f₂ hf₂ K)) (OpenSubgroup.comap.{u1, u3} G _inst_1 _inst_2 P _inst_5 _inst_6 (MonoidHom.comp.{u1, u2, u3} G N P (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5))) f₂ f₁) (Continuous.comp.{u1, u2, u3} G N P _inst_2 _inst_4 _inst_6 (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) (fun (_x : MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) => N -> P) (MonoidHom.hasCoeToFun.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) f₂) (fun (x : G) => coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (fun (_x : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) => G -> N) (MonoidHom.hasCoeToFun.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) f₁ x) hf₂ hf₁) K)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : TopologicalSpace.{u2} N] {P : Type.{u3}} [_inst_5 : Group.{u3} P] [_inst_6 : TopologicalSpace.{u3} P] (K : OpenSubgroup.{u3} P _inst_5 _inst_6) (f₂ : MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) (hf₂ : Continuous.{u2, u3} N P _inst_4 _inst_6 (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) N P (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MulOneClass.toMul.{u3} P (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5))) (MonoidHom.monoidHomClass.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))))) f₂)) (f₁ : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (hf₁ : Continuous.{u1, u2} G N _inst_2 _inst_4 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f₁)), Eq.{succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.comap.{u1, u2} G _inst_1 _inst_2 N _inst_3 _inst_4 f₁ hf₁ (OpenSubgroup.comap.{u2, u3} N _inst_3 _inst_4 P _inst_5 _inst_6 f₂ hf₂ K)) (OpenSubgroup.comap.{u1, u3} G _inst_1 _inst_2 P _inst_5 _inst_6 (MonoidHom.comp.{u1, u2, u3} G N P (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5))) f₂ f₁) (Continuous.comp.{u1, u3, u2} G N P _inst_2 _inst_4 _inst_6 (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) N (fun (_x : N) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : N) => P) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) N P (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MulOneClass.toMul.{u3} P (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))) N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5))) (MonoidHom.monoidHomClass.{u2, u3} N P (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (Monoid.toMulOneClass.{u3} P (DivInvMonoid.toMonoid.{u3} P (Group.toDivInvMonoid.{u3} P _inst_5)))))) f₂) (fun (x : G) => FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => N) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3))) (MonoidHom.monoidHomClass.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))))) f₁ x) hf₂ hf₁) K)
Case conversion may be inaccurate. Consider using '#align open_subgroup.comap_comap OpenSubgroup.comap_comapₓ'. -/
@[to_additive]
theorem comap_comap {P : Type _} [Group P] [TopologicalSpace P] (K : OpenSubgroup P) (f₂ : N →* P)
    (hf₂ : Continuous f₂) (f₁ : G →* N) (hf₁ : Continuous f₁) :
    (K.comap f₂ hf₂).comap f₁ hf₁ = K.comap (f₂.comp f₁) (hf₂.comp hf₁) :=
  rfl
#align open_subgroup.comap_comap OpenSubgroup.comap_comap
#align open_add_subgroup.comap_comap OpenAddSubgroup.comap_comap

end OpenSubgroup

namespace Subgroup

variable {G : Type _} [Group G] [TopologicalSpace G] [ContinuousMul G] (H : Subgroup G)

/- warning: subgroup.is_open_of_mem_nhds -> Subgroup.isOpen_of_mem_nhds is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (H : Subgroup.{u1} G _inst_1) {g : G}, (Membership.Mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (Filter.hasMem.{u1} G) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H) (nhds.{u1} G _inst_2 g)) -> (IsOpen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (H : Subgroup.{u1} G _inst_1) {g : G}, (Membership.mem.{u1, u1} (Set.{u1} G) (Filter.{u1} G) (instMembershipSetFilter.{u1} G) (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H) (nhds.{u1} G _inst_2 g)) -> (IsOpen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H))
Case conversion may be inaccurate. Consider using '#align subgroup.is_open_of_mem_nhds Subgroup.isOpen_of_mem_nhdsₓ'. -/
@[to_additive]
theorem isOpen_of_mem_nhds {g : G} (hg : (H : Set G) ∈ 𝓝 g) : IsOpen (H : Set G) :=
  by
  refine' isOpen_iff_mem_nhds.2 fun x hx => _
  have hg' : g ∈ H := SetLike.mem_coe.1 (mem_of_mem_nhds hg)
  have : Filter.Tendsto (fun y => y * (x⁻¹ * g)) (𝓝 x) (𝓝 g) :=
    (continuous_id.mul continuous_const).tendsto' _ _ (mul_inv_cancel_left _ _)
  simpa only [SetLike.mem_coe, Filter.mem_map',
    H.mul_mem_cancel_right (H.mul_mem (H.inv_mem hx) hg')] using this hg
#align subgroup.is_open_of_mem_nhds Subgroup.isOpen_of_mem_nhds
#align add_subgroup.is_open_of_mem_nhds AddSubgroup.isOpen_of_mem_nhds

/- warning: subgroup.is_open_mono -> Subgroup.isOpen_mono is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {H₁ : Subgroup.{u1} G _inst_1} {H₂ : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H₁ H₂) -> (IsOpen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H₁)) -> (IsOpen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H₂))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] {H₁ : Subgroup.{u1} G _inst_1} {H₂ : Subgroup.{u1} G _inst_1}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) H₁ H₂) -> (IsOpen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H₁)) -> (IsOpen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H₂))
Case conversion may be inaccurate. Consider using '#align subgroup.is_open_mono Subgroup.isOpen_monoₓ'. -/
@[to_additive]
theorem isOpen_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) (h₁ : IsOpen (H₁ : Set G)) :
    IsOpen (H₂ : Set G) :=
  isOpen_of_mem_nhds _ <| Filter.mem_of_superset (h₁.mem_nhds <| one_mem H₁) h
#align subgroup.is_open_mono Subgroup.isOpen_mono
#align add_subgroup.is_open_mono AddSubgroup.isOpen_mono

/- warning: subgroup.is_open_of_open_subgroup -> Subgroup.isOpen_of_openSubgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (H : Subgroup.{u1} G _inst_1) {U : OpenSubgroup.{u1} G _inst_1 _inst_2}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (SetLike.partialOrder.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U) H) -> (IsOpen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (H : Subgroup.{u1} G _inst_1) {U : OpenSubgroup.{u1} G _inst_1 _inst_2}, (LE.le.{u1} (Subgroup.{u1} G _inst_1) (Preorder.toLE.{u1} (Subgroup.{u1} G _inst_1) (PartialOrder.toPreorder.{u1} (Subgroup.{u1} G _inst_1) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 U) H) -> (IsOpen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H))
Case conversion may be inaccurate. Consider using '#align subgroup.is_open_of_open_subgroup Subgroup.isOpen_of_openSubgroupₓ'. -/
@[to_additive]
theorem isOpen_of_openSubgroup {U : OpenSubgroup G} (h : ↑U ≤ H) : IsOpen (H : Set G) :=
  isOpen_mono h U.IsOpen
#align subgroup.is_open_of_open_subgroup Subgroup.isOpen_of_openSubgroup
#align add_subgroup.is_open_of_open_add_subgroup AddSubgroup.isOpen_of_openAddSubgroup

/- warning: subgroup.is_open_of_one_mem_interior -> Subgroup.isOpen_of_one_mem_interior is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (H : Subgroup.{u1} G _inst_1), (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))))) (interior.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H))) -> (IsOpen.{u1} G _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subgroup.{u1} G _inst_1) (Set.{u1} G) (HasLiftT.mk.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (CoeTCₓ.coe.{succ u1, succ u1} (Subgroup.{u1} G _inst_1) (Set.{u1} G) (SetLike.Set.hasCoeT.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)))) H))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (H : Subgroup.{u1} G _inst_1), (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))))) (interior.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H))) -> (IsOpen.{u1} G _inst_2 (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H))
Case conversion may be inaccurate. Consider using '#align subgroup.is_open_of_one_mem_interior Subgroup.isOpen_of_one_mem_interiorₓ'. -/
/-- If a subgroup of a topological group has `1` in its interior, then it is open. -/
@[to_additive
      "If a subgroup of an additive topological group has `0` in its interior, then it is\nopen."]
theorem isOpen_of_one_mem_interior (h_1_int : (1 : G) ∈ interior (H : Set G)) :
    IsOpen (H : Set G) :=
  isOpen_of_mem_nhds H <| mem_interior_iff_mem_nhds.1 h_1_int
#align subgroup.is_open_of_one_mem_interior Subgroup.isOpen_of_one_mem_interior
#align add_subgroup.is_open_of_zero_mem_interior AddSubgroup.isOpen_of_zero_mem_interior

end Subgroup

namespace OpenSubgroup

variable {G : Type _} [Group G] [TopologicalSpace G] [ContinuousMul G]

@[to_additive]
instance : Sup (OpenSubgroup G) :=
  ⟨fun U V => ⟨U ⊔ V, Subgroup.isOpen_mono (le_sup_left : U.1 ≤ U ⊔ V) U.IsOpen⟩⟩

/- warning: open_subgroup.coe_subgroup_sup -> OpenSubgroup.toSubgroup_sup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (U : OpenSubgroup.{u1} G _inst_1 _inst_2) (V : OpenSubgroup.{u1} G _inst_1 _inst_2), Eq.{succ u1} (Subgroup.{u1} G _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) (Sup.sup.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.hasSup.{u1} G _inst_1 _inst_2 _inst_3) U V)) (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toHasSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.completeLattice.{u1} G _inst_1))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) U) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (HasLiftT.mk.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (Subgroup.{u1} G _inst_1) (OpenSubgroup.hasCoeSubgroup.{u1} G _inst_1 _inst_2))) V))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] [_inst_2 : TopologicalSpace.{u1} G] [_inst_3 : ContinuousMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))] (U : OpenSubgroup.{u1} G _inst_1 _inst_2) (V : OpenSubgroup.{u1} G _inst_1 _inst_2), Eq.{succ u1} (Subgroup.{u1} G _inst_1) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 (Sup.sup.{u1} (OpenSubgroup.{u1} G _inst_1 _inst_2) (OpenSubgroup.instSupOpenSubgroup.{u1} G _inst_1 _inst_2 _inst_3) U V)) (Sup.sup.{u1} (Subgroup.{u1} G _inst_1) (SemilatticeSup.toSup.{u1} (Subgroup.{u1} G _inst_1) (Lattice.toSemilatticeSup.{u1} (Subgroup.{u1} G _inst_1) (ConditionallyCompleteLattice.toLattice.{u1} (Subgroup.{u1} G _inst_1) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instCompleteLatticeSubgroup.{u1} G _inst_1))))) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 U) (OpenSubgroup.toSubgroup.{u1} G _inst_1 _inst_2 V))
Case conversion may be inaccurate. Consider using '#align open_subgroup.coe_subgroup_sup OpenSubgroup.toSubgroup_supₓ'. -/
@[simp, norm_cast, to_additive]
theorem toSubgroup_sup (U V : OpenSubgroup G) : (↑(U ⊔ V) : Subgroup G) = ↑U ⊔ ↑V :=
  rfl
#align open_subgroup.coe_subgroup_sup OpenSubgroup.toSubgroup_sup
#align open_add_subgroup.coe_add_subgroup_sup OpenAddSubgroup.toAddSubgroup_sup

@[to_additive]
instance : Lattice (OpenSubgroup G) :=
  { OpenSubgroup.semilatticeInf,
    toSubgroup_injective.SemilatticeSup (coe : OpenSubgroup G → Subgroup G) fun _ _ => rfl with }

end OpenSubgroup

namespace Submodule

open OpenAddSubgroup

variable {R : Type _} {M : Type _} [CommRing R]

variable [AddCommGroup M] [TopologicalSpace M] [TopologicalAddGroup M] [Module R M]

/- warning: submodule.is_open_mono -> Submodule.isOpen_mono is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommRing.{u1} R] [_inst_2 : AddCommGroup.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : TopologicalAddGroup.{u2} M _inst_3 (AddCommGroup.toAddGroup.{u2} M _inst_2)] [_inst_5 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2)] {U : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5} {P : Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5}, (LE.le.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Preorder.toLE.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (PartialOrder.toPreorder.{u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (SetLike.partialOrder.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5)))) U P) -> (IsOpen.{u2} M _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5)))) U)) -> (IsOpen.{u2} M _inst_3 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Set.{u2} M) (HasLiftT.mk.{succ u2, succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Set.{u2} M) (CoeTCₓ.coe.{succ u2, succ u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) (Set.{u2} M) (SetLike.Set.hasCoeT.{u2, u2} (Submodule.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5) M (Submodule.setLike.{u1, u2} R M (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u2} M _inst_2) _inst_5)))) P))
but is expected to have type
  forall {R : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommRing.{u2} R] [_inst_2 : AddCommGroup.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : TopologicalAddGroup.{u1} M _inst_3 (AddCommGroup.toAddGroup.{u1} M _inst_2)] [_inst_5 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2)] {U : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5} {P : Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5}, (LE.le.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) (Preorder.toLE.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) (PartialOrder.toPreorder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) (Submodule.completeLattice.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5))))) U P) -> (IsOpen.{u1} M _inst_3 (SetLike.coe.{u1, u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) M (Submodule.setLike.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) U)) -> (IsOpen.{u1} M _inst_3 (SetLike.coe.{u1, u1} (Submodule.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) M (Submodule.setLike.{u2, u1} R M (Ring.toSemiring.{u2} R (CommRing.toRing.{u2} R _inst_1)) (AddCommGroup.toAddCommMonoid.{u1} M _inst_2) _inst_5) P))
Case conversion may be inaccurate. Consider using '#align submodule.is_open_mono Submodule.isOpen_monoₓ'. -/
theorem isOpen_mono {U P : Submodule R M} (h : U ≤ P) (hU : IsOpen (U : Set M)) :
    IsOpen (P : Set M) :=
  @AddSubgroup.isOpen_mono M _ _ _ U.toAddSubgroup P.toAddSubgroup h hU
#align submodule.is_open_mono Submodule.isOpen_mono

end Submodule

namespace Ideal

variable {R : Type _} [CommRing R]

variable [TopologicalSpace R] [TopologicalRing R]

/- warning: ideal.is_open_of_open_subideal -> Ideal.isOpen_of_open_subideal is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalRing.{u1} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))] {U : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))}, (LE.le.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Preorder.toLE.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (SetLike.partialOrder.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) U I) -> (IsOpen.{u1} R _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) U)) -> (IsOpen.{u1} R _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} R) (HasLiftT.mk.{succ u1, succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} R) (CoeTCₓ.coe.{succ u1, succ u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Set.{u1} R) (SetLike.Set.hasCoeT.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))))) I))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalRing.{u1} R _inst_2 (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))] {U : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {I : Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))}, (LE.le.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Preorder.toLE.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (PartialOrder.toPreorder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Submodule.completeLattice.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))) U I) -> (IsOpen.{u1} R _inst_2 (SetLike.coe.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) U)) -> (IsOpen.{u1} R _inst_2 (SetLike.coe.{u1, u1} (Ideal.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) R (Submodule.setLike.{u1, u1} R R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))))) (Semiring.toModule.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))) I))
Case conversion may be inaccurate. Consider using '#align ideal.is_open_of_open_subideal Ideal.isOpen_of_open_subidealₓ'. -/
theorem isOpen_of_open_subideal {U I : Ideal R} (h : U ≤ I) (hU : IsOpen (U : Set R)) :
    IsOpen (I : Set R) :=
  Submodule.isOpen_mono h hU
#align ideal.is_open_of_open_subideal Ideal.isOpen_of_open_subideal

end Ideal

