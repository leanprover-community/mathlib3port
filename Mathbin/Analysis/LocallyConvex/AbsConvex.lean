/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.locally_convex.abs_convex
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.LocallyConvex.BalancedCoreHull
import Mathbin.Analysis.LocallyConvex.WithSeminorms
import Mathbin.Analysis.Convex.Gauge

/-!
# Absolutely convex sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A set is called absolutely convex or disked if it is convex and balanced.
The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `gauge_seminorm_family`: the seminorm family induced by all open absolutely convex neighborhoods
of zero.

## Main statements

* `with_gauge_seminorm_family`: the topology of a locally convex space is induced by the family
`gauge_seminorm_family`.

## Todo

* Define the disked hull

## Tags

disks, convex, balanced
-/


open NormedField Set

open BigOperators NNReal Pointwise Topology

variable {𝕜 E F G ι : Type _}

section NontriviallyNormedField

variable (𝕜 E) {s : Set E}

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [Module ℝ E] [SMulCommClass ℝ 𝕜 E]

variable [TopologicalSpace E] [LocallyConvexSpace ℝ E] [ContinuousSMul 𝕜 E]

/- warning: nhds_basis_abs_convex -> nhds_basis_abs_convex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nhds_basis_abs_convex nhds_basis_abs_convexₓ'. -/
theorem nhds_basis_abs_convex :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 s ∧ Convex ℝ s) id :=
  by
  refine'
    (LocallyConvexSpace.convex_basis_zero ℝ E).to_hasBasis (fun s hs => _) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine' ⟨convexHull ℝ (balancedCore 𝕜 s), _, convexHull_min (balancedCore_subset s) hs.2⟩
  refine' ⟨Filter.mem_of_superset (balancedCore_mem_nhds_zero hs.1) (subset_convexHull ℝ _), _⟩
  refine' ⟨balanced_convexHull_of_balanced (balancedCore_balanced s), _⟩
  exact convex_convexHull ℝ (balancedCore 𝕜 s)
#align nhds_basis_abs_convex nhds_basis_abs_convex

variable [ContinuousSMul ℝ E] [TopologicalAddGroup E]

/- warning: nhds_basis_abs_convex_open -> nhds_basis_abs_convex_open is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align nhds_basis_abs_convex_open nhds_basis_abs_convex_openₓ'. -/
theorem nhds_basis_abs_convex_open :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => (0 : E) ∈ s ∧ IsOpen s ∧ Balanced 𝕜 s ∧ Convex ℝ s) id :=
  by
  refine' (nhds_basis_abs_convex 𝕜 E).to_hasBasis _ _
  · rintro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine' ⟨interior s, _, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, isOpen_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩
  rintro s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩
#align nhds_basis_abs_convex_open nhds_basis_abs_convex_open

end NontriviallyNormedField

section AbsolutelyConvexSets

variable [TopologicalSpace E] [AddCommMonoid E] [Zero E] [SeminormedRing 𝕜]

variable [SMul 𝕜 E] [SMul ℝ E]

variable (𝕜 E)

#print AbsConvexOpenSets /-
/-- The type of absolutely convex open sets. -/
def AbsConvexOpenSets :=
  { s : Set E // (0 : E) ∈ s ∧ IsOpen s ∧ Balanced 𝕜 s ∧ Convex ℝ s }
#align abs_convex_open_sets AbsConvexOpenSets
-/

/- warning: abs_convex_open_sets.has_coe -> AbsConvexOpenSets.instCoeTC is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E], Coe.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E)
but is expected to have type
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E], CoeTC.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E)
Case conversion may be inaccurate. Consider using '#align abs_convex_open_sets.has_coe AbsConvexOpenSets.instCoeTCₓ'. -/
instance AbsConvexOpenSets.instCoeTC : Coe (AbsConvexOpenSets 𝕜 E) (Set E) :=
  ⟨Subtype.val⟩
#align abs_convex_open_sets.has_coe AbsConvexOpenSets.instCoeTC

namespace AbsConvexOpenSets

variable {𝕜 E}

/- warning: abs_convex_open_sets.coe_zero_mem -> AbsConvexOpenSets.coe_zero_mem is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E] (s : AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E _inst_3))) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (coeBase.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (AbsConvexOpenSets.instCoeTC.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)))) s)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Zero.{u1} E] [_inst_4 : SeminormedRing.{u2} 𝕜] [_inst_5 : SMul.{u2, u1} 𝕜 E] [_inst_6 : SMul.{0, u1} Real E] (s : AbsConvexOpenSets.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)) (Subtype.val.{succ u1} (Set.{u1} E) (fun (s : Set.{u1} E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)) s) (And (IsOpen.{u1} E _inst_1 s) (And (Balanced.{u2, u1} 𝕜 E _inst_4 _inst_5 s) (Convex.{0, u1} Real E Real.orderedSemiring _inst_2 _inst_6 s)))) s)
Case conversion may be inaccurate. Consider using '#align abs_convex_open_sets.coe_zero_mem AbsConvexOpenSets.coe_zero_memₓ'. -/
theorem coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) ∈ (s : Set E) :=
  s.2.1
#align abs_convex_open_sets.coe_zero_mem AbsConvexOpenSets.coe_zero_mem

/- warning: abs_convex_open_sets.coe_is_open -> AbsConvexOpenSets.coe_isOpen is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E] (s : AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), IsOpen.{u2} E _inst_1 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (coeBase.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (AbsConvexOpenSets.instCoeTC.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)))) s)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Zero.{u1} E] [_inst_4 : SeminormedRing.{u2} 𝕜] [_inst_5 : SMul.{u2, u1} 𝕜 E] [_inst_6 : SMul.{0, u1} Real E] (s : AbsConvexOpenSets.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), IsOpen.{u1} E _inst_1 (Subtype.val.{succ u1} (Set.{u1} E) (fun (s : Set.{u1} E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)) s) (And (IsOpen.{u1} E _inst_1 s) (And (Balanced.{u2, u1} 𝕜 E _inst_4 _inst_5 s) (Convex.{0, u1} Real E Real.orderedSemiring _inst_2 _inst_6 s)))) s)
Case conversion may be inaccurate. Consider using '#align abs_convex_open_sets.coe_is_open AbsConvexOpenSets.coe_isOpenₓ'. -/
theorem coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E) :=
  s.2.2.1
#align abs_convex_open_sets.coe_is_open AbsConvexOpenSets.coe_isOpen

/- warning: abs_convex_open_sets.coe_nhds -> AbsConvexOpenSets.coe_nhds is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E] (s : AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Membership.Mem.{u2, u2} (Set.{u2} E) (Filter.{u2} E) (Filter.hasMem.{u2} E) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (coeBase.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (AbsConvexOpenSets.instCoeTC.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)))) s) (nhds.{u2} E _inst_1 (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E _inst_3))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Zero.{u1} E] [_inst_4 : SeminormedRing.{u2} 𝕜] [_inst_5 : SMul.{u2, u1} 𝕜 E] [_inst_6 : SMul.{0, u1} Real E] (s : AbsConvexOpenSets.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Membership.mem.{u1, u1} (Set.{u1} E) (Filter.{u1} E) (instMembershipSetFilter.{u1} E) (Subtype.val.{succ u1} (Set.{u1} E) (fun (s : Set.{u1} E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)) s) (And (IsOpen.{u1} E _inst_1 s) (And (Balanced.{u2, u1} 𝕜 E _inst_4 _inst_5 s) (Convex.{0, u1} Real E Real.orderedSemiring _inst_2 _inst_6 s)))) s) (nhds.{u1} E _inst_1 (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)))
Case conversion may be inaccurate. Consider using '#align abs_convex_open_sets.coe_nhds AbsConvexOpenSets.coe_nhdsₓ'. -/
theorem coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) ∈ 𝓝 (0 : E) :=
  s.coe_isOpen.mem_nhds s.coe_zero_mem
#align abs_convex_open_sets.coe_nhds AbsConvexOpenSets.coe_nhds

/- warning: abs_convex_open_sets.coe_balanced -> AbsConvexOpenSets.coe_balanced is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E] (s : AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Balanced.{u1, u2} 𝕜 E _inst_4 _inst_5 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (coeBase.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (AbsConvexOpenSets.instCoeTC.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)))) s)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Zero.{u1} E] [_inst_4 : SeminormedRing.{u2} 𝕜] [_inst_5 : SMul.{u2, u1} 𝕜 E] [_inst_6 : SMul.{0, u1} Real E] (s : AbsConvexOpenSets.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Balanced.{u2, u1} 𝕜 E _inst_4 _inst_5 (Subtype.val.{succ u1} (Set.{u1} E) (fun (s : Set.{u1} E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)) s) (And (IsOpen.{u1} E _inst_1 s) (And (Balanced.{u2, u1} 𝕜 E _inst_4 _inst_5 s) (Convex.{0, u1} Real E Real.orderedSemiring _inst_2 _inst_6 s)))) s)
Case conversion may be inaccurate. Consider using '#align abs_convex_open_sets.coe_balanced AbsConvexOpenSets.coe_balancedₓ'. -/
theorem coe_balanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E) :=
  s.2.2.2.1
#align abs_convex_open_sets.coe_balanced AbsConvexOpenSets.coe_balanced

/- warning: abs_convex_open_sets.coe_convex -> AbsConvexOpenSets.coe_convex is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} E] [_inst_2 : AddCommMonoid.{u2} E] [_inst_3 : Zero.{u2} E] [_inst_4 : SeminormedRing.{u1} 𝕜] [_inst_5 : SMul.{u1, u2} 𝕜 E] [_inst_6 : SMul.{0, u2} Real E] (s : AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Convex.{0, u2} Real E Real.orderedSemiring _inst_2 _inst_6 ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (coeBase.{succ u2, succ u2} (AbsConvexOpenSets.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6) (Set.{u2} E) (AbsConvexOpenSets.instCoeTC.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6)))) s)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} E] [_inst_2 : AddCommMonoid.{u1} E] [_inst_3 : Zero.{u1} E] [_inst_4 : SeminormedRing.{u2} 𝕜] [_inst_5 : SMul.{u2, u1} 𝕜 E] [_inst_6 : SMul.{0, u1} Real E] (s : AbsConvexOpenSets.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6), Convex.{0, u1} Real E Real.orderedSemiring _inst_2 _inst_6 (Subtype.val.{succ u1} (Set.{u1} E) (fun (s : Set.{u1} E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)) s) (And (IsOpen.{u1} E _inst_1 s) (And (Balanced.{u2, u1} 𝕜 E _inst_4 _inst_5 s) (Convex.{0, u1} Real E Real.orderedSemiring _inst_2 _inst_6 s)))) s)
Case conversion may be inaccurate. Consider using '#align abs_convex_open_sets.coe_convex AbsConvexOpenSets.coe_convexₓ'. -/
theorem coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex ℝ (s : Set E) :=
  s.2.2.2.2
#align abs_convex_open_sets.coe_convex AbsConvexOpenSets.coe_convex

end AbsConvexOpenSets

instance : Nonempty (AbsConvexOpenSets 𝕜 E) :=
  by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

end AbsolutelyConvexSets

variable [IsROrC 𝕜]

variable [AddCommGroup E] [TopologicalSpace E]

variable [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

variable [ContinuousSMul ℝ E]

variable (𝕜 E)

/- warning: gauge_seminorm_family -> gaugeSeminormFamily is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align gauge_seminorm_family gaugeSeminormFamilyₓ'. -/
/-- The family of seminorms defined by the gauges of absolute convex open sets. -/
noncomputable def gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E) := fun s =>
  gaugeSeminorm s.coe_balanced s.coe_convex (absorbent_nhds_zero s.coe_nhds)
#align gauge_seminorm_family gaugeSeminormFamily

variable {𝕜 E}

/- warning: gauge_seminorm_family_ball -> gaugeSeminormFamily_ball is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align gauge_seminorm_family_ball gaugeSeminormFamily_ballₓ'. -/
theorem gaugeSeminormFamily_ball (s : AbsConvexOpenSets 𝕜 E) :
    (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E) :=
  by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_to_fun]
  exact gauge_lt_one_eq_self_of_open s.coe_convex s.coe_zero_mem s.coe_is_open
#align gauge_seminorm_family_ball gaugeSeminormFamily_ball

variable [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]

variable [SMulCommClass ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/- warning: with_gauge_seminorm_family -> with_gaugeSeminormFamily is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align with_gauge_seminorm_family with_gaugeSeminormFamilyₓ'. -/
/-- The topology of a locally convex space is induced by the gauge seminorm family. -/
theorem with_gaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E) :=
  by
  refine' SeminormFamily.withSeminorms_of_hasBasis _ _
  refine' (nhds_basis_abs_convex_open 𝕜 E).to_hasBasis (fun s hs => _) fun s hs => _
  · refine' ⟨s, ⟨_, rfl.subset⟩⟩
    convert(gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball, Subtype.coe_mk]
  refine' ⟨s, ⟨_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine'
    ⟨mem_Inter₂.mpr fun _ _ => by simp [Seminorm.mem_ball_zero, hr],
      isOpen_biInter (to_finite _) fun S _ => _,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => Seminorm.convex_ball _ _ _⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) ≠ 0 := by simp [hr.ne']
  rw [hr', ← Seminorm.smul_ball_zero hr'', gaugeSeminormFamily_ball]
  exact S.coe_is_open.smul₀ hr''
#align with_gauge_seminorm_family with_gaugeSeminormFamily

