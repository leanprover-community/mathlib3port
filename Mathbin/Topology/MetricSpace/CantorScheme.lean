/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher

! This file was ported from Lean 3 source module topology.metric_space.cantor_scheme
! leanprover-community/mathlib commit 49b7f94aab3a3bdca1f9f34c5d818afb253b3993
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.PiNat

/-!
# (Topological) Schemes and their induced maps

In topology, and especially descriptive set theory, one often constructs functions `(ℕ → β) → α`,
where α is some topological space and β is a discrete space, as an appropriate limit of some map
`list β → set α`. We call the latter type of map a "`β`-scheme on `α`".

This file develops the basic, abstract theory of these schemes and the functions they induce.

## Main Definitions

* `cantor_scheme.induced_map A` : The aforementioned "limit" of a scheme `A : list β → set α`.
  This is a partial function from `ℕ → β` to `a`,
  implemented here as an object of type `Σ s : set (ℕ → β), s → α`.
  That is, `(induced_map A).1` is the domain and `(induced_map A).2` is the function.

## Implementation Notes

We consider end-appending to be the fundamental way to build lists (say on `β`) inductively,
as this interacts better with the topology on `ℕ → β`.
As a result, functions like `list.nth` or `stream.take` do not have their intended meaning
in this file. See instead `pi_nat.res`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

scheme, cantor scheme, lusin scheme, approximation.

-/


namespace CantorScheme

open List Function Filter Set PiNat

open Classical Topology

variable {β α : Type _} (A : List β → Set α)

#print CantorScheme.inducedMap /-
/-- From a `β`-scheme on `α` `A`, we define a partial function from `(ℕ → β)` to `α`
which sends each infinite sequence `x` to an element of the intersection along the
branch corresponding to `x`, if it exists.
We call this the map induced by the scheme. -/
noncomputable def inducedMap : Σs : Set (ℕ → β), s → α :=
  ⟨fun x => Set.Nonempty (⋂ n : ℕ, A (res x n)), fun x => x.property.some⟩
#align cantor_scheme.induced_map CantorScheme.inducedMap
-/

section Topology

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CantorScheme.Antitone /-
/-- A scheme is antitone if each set contains its children. -/
protected def Antitone : Prop :=
  ∀ l : List β, ∀ a : β, A (a::l) ⊆ A l
#align cantor_scheme.antitone CantorScheme.Antitone
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CantorScheme.ClosureAntitone /-
/-- A useful strengthening of being antitone is to require that each set contains
the closure of each of its children. -/
def ClosureAntitone [TopologicalSpace α] : Prop :=
  ∀ l : List β, ∀ a : β, closure (A (a::l)) ⊆ A l
#align cantor_scheme.closure_antitone CantorScheme.ClosureAntitone
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CantorScheme.Disjoint /-
/-- A scheme is disjoint if the children of each set of pairwise disjoint. -/
protected def Disjoint : Prop :=
  ∀ l : List β, Pairwise fun a b => Disjoint (A (a::l)) (A (b::l))
#align cantor_scheme.disjoint CantorScheme.Disjoint
-/

variable {A}

/- warning: cantor_scheme.map_mem -> CantorScheme.map_mem is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {A : (List.{u1} β) -> (Set.{u2} α)} (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) (n : Nat), Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (Sigma.snd.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A) x) (A (PiNat.res.{u1} β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) (Nat -> β) (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) (Nat -> β) (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) (Nat -> β) (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) (Nat -> β) (coeSubtype.{succ u1} (Nat -> β) (fun (x : Nat -> β) => Membership.Mem.{u1, u1} (Nat -> β) (Set.{u1} (Nat -> β)) (Set.hasMem.{u1} (Nat -> β)) x (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))))))) x) n))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} {A : (List.{u2} β) -> (Set.{u1} α)} (x : Set.Elem.{u2} (Nat -> β) (Sigma.fst.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A))) (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Sigma.snd.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A) x) (A (PiNat.res.{u2} β (Subtype.val.{succ u2} (Nat -> β) (fun (x : Nat -> β) => Membership.mem.{u2, u2} (Nat -> β) (Set.{u2} (Nat -> β)) (Set.instMembershipSet.{u2} (Nat -> β)) x (Sigma.fst.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A))) x) n))
Case conversion may be inaccurate. Consider using '#align cantor_scheme.map_mem CantorScheme.map_memₓ'. -/
/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
theorem map_mem (x : (inducedMap A).1) (n : ℕ) : (inducedMap A).2 x ∈ A (res x n) :=
  by
  have := x.property.some_mem
  rw [mem_Inter] at this
  exact this n
#align cantor_scheme.map_mem CantorScheme.map_mem

#print CantorScheme.ClosureAntitone.antitone /-
protected theorem ClosureAntitone.antitone [TopologicalSpace α] (hA : ClosureAntitone A) :
    CantorScheme.Antitone A := fun l a => subset_closure.trans (hA l a)
#align cantor_scheme.closure_antitone.antitone CantorScheme.ClosureAntitone.antitone
-/

#print CantorScheme.Antitone.closureAntitone /-
protected theorem Antitone.closureAntitone [TopologicalSpace α] (hanti : CantorScheme.Antitone A)
    (hclosed : ∀ l, IsClosed (A l)) : ClosureAntitone A := fun l a =>
  (hclosed _).closure_eq.Subset.trans (hanti _ _)
#align cantor_scheme.antitone.closure_antitone CantorScheme.Antitone.closureAntitone
-/

/- warning: cantor_scheme.disjoint.map_injective -> CantorScheme.Disjoint.map_injective is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {A : (List.{u1} β) -> (Set.{u2} α)}, (CantorScheme.Disjoint.{u1, u2} β α A) -> (Function.Injective.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) α (Sigma.snd.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A)))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} {A : (List.{u2} β) -> (Set.{u1} α)}, (CantorScheme.Disjoint.{u2, u1} β α A) -> (Function.Injective.{succ u2, succ u1} (Set.Elem.{u2} (Nat -> β) (Sigma.fst.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A))) α (Sigma.snd.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A)))
Case conversion may be inaccurate. Consider using '#align cantor_scheme.disjoint.map_injective CantorScheme.Disjoint.map_injectiveₓ'. -/
/-- A scheme where the children of each set are pairwise disjoint induces an injective map. -/
theorem Disjoint.map_injective (hA : CantorScheme.Disjoint A) : Injective (inducedMap A).2 :=
  by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  refine' Subtype.coe_injective (res_injective _)
  dsimp
  ext n : 1
  induction' n with n ih; · simp
  simp only [res_succ]
  refine' ⟨_, ih⟩
  contrapose hA
  simp only [CantorScheme.Disjoint, _root_.pairwise, Ne.def, not_forall, exists_prop]
  refine' ⟨res x n, _, _, hA, _⟩
  rw [not_disjoint_iff]
  refine' ⟨([anonymous] A).2 ⟨x, hx⟩, _, _⟩
  · rw [← res_succ]
    apply map_mem
  rw [hxy, ih, ← res_succ]
  apply map_mem
#align cantor_scheme.disjoint.map_injective CantorScheme.Disjoint.map_injective

end Topology

section Metric

variable [PseudoMetricSpace α]

variable (A)

#print CantorScheme.VanishingDiam /-
/-- A scheme on a metric space has vanishing diameter if diameter approaches 0 along each branch. -/
def VanishingDiam : Prop :=
  ∀ x : ℕ → β, Tendsto (fun n : ℕ => EMetric.diam (A (res x n))) atTop (𝓝 0)
#align cantor_scheme.vanishing_diam CantorScheme.VanishingDiam
-/

variable {A}

/- warning: cantor_scheme.vanishing_diam.dist_lt -> CantorScheme.VanishingDiam.dist_lt is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {A : (List.{u1} β) -> (Set.{u2} α)} [_inst_1 : PseudoMetricSpace.{u2} α], (CantorScheme.VanishingDiam.{u1, u2} β α A _inst_1) -> (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall (x : Nat -> β), Exists.{1} Nat (fun (n : Nat) => forall (y : α), (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) y (A (PiNat.res.{u1} β x n))) -> (forall (z : α), (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) z (A (PiNat.res.{u1} β x n))) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} α (PseudoMetricSpace.toHasDist.{u2} α _inst_1) y z) ε)))))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} {A : (List.{u2} β) -> (Set.{u1} α)} [_inst_1 : PseudoMetricSpace.{u1} α], (CantorScheme.VanishingDiam.{u2, u1} β α A _inst_1) -> (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall (x : Nat -> β), Exists.{1} Nat (fun (n : Nat) => forall (y : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y (A (PiNat.res.{u2} β x n))) -> (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (A (PiNat.res.{u2} β x n))) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u1} α (PseudoMetricSpace.toDist.{u1} α _inst_1) y z) ε)))))
Case conversion may be inaccurate. Consider using '#align cantor_scheme.vanishing_diam.dist_lt CantorScheme.VanishingDiam.dist_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y z «expr ∈ » A (res[pi_nat.res] x n)) -/
theorem VanishingDiam.dist_lt (hA : VanishingDiam A) (ε : ℝ) (ε_pos : 0 < ε) (x : ℕ → β) :
    ∃ n : ℕ, ∀ (y) (_ : y ∈ A (res x n)) (z) (_ : z ∈ A (res x n)), dist y z < ε :=
  by
  specialize hA x
  rw [ENNReal.tendsto_atTop_zero] at hA
  cases'
    hA (ENNReal.ofReal (ε / 2))
      (by
        simp only [gt_iff_lt, ENNReal.ofReal_pos]
        linarith) with
    n hn
  use n
  intro y hy z hz
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos, ← edist_dist]
  apply lt_of_le_of_lt (EMetric.edist_le_diam_of_mem hy hz)
  apply lt_of_le_of_lt (hn _ (le_refl _))
  rw [ENNReal.ofReal_lt_ofReal_iff ε_pos]
  linarith
#align cantor_scheme.vanishing_diam.dist_lt CantorScheme.VanishingDiam.dist_lt

/- warning: cantor_scheme.vanishing_diam.map_continuous -> CantorScheme.VanishingDiam.map_continuous is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} {A : (List.{u1} β) -> (Set.{u2} α)} [_inst_1 : PseudoMetricSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : DiscreteTopology.{u1} β _inst_2], (CantorScheme.VanishingDiam.{u1, u2} β α A _inst_1) -> (Continuous.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) α (Subtype.topologicalSpace.{u1} (Nat -> β) (fun (x : Nat -> β) => Membership.Mem.{u1, u1} (Nat -> β) (Set.{u1} (Nat -> β)) (Set.hasMem.{u1} (Nat -> β)) x (Sigma.fst.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A))) (Pi.topologicalSpace.{0, u1} Nat (fun (ᾰ : Nat) => β) (fun (a : Nat) => _inst_2))) (UniformSpace.toTopologicalSpace.{u2} α (PseudoMetricSpace.toUniformSpace.{u2} α _inst_1)) (Sigma.snd.{u1, max u1 u2} (Set.{u1} (Nat -> β)) (fun (s : Set.{u1} (Nat -> β)) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} (Nat -> β)) Type.{u1} (Set.hasCoeToSort.{u1} (Nat -> β)) s) -> α) (CantorScheme.inducedMap.{u1, u2} β α A)))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} {A : (List.{u2} β) -> (Set.{u1} α)} [_inst_1 : PseudoMetricSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : DiscreteTopology.{u2} β _inst_2], (CantorScheme.VanishingDiam.{u2, u1} β α A _inst_1) -> (Continuous.{u2, u1} (Set.Elem.{u2} (Nat -> β) (Sigma.fst.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A))) α (instTopologicalSpaceSubtype.{u2} (Nat -> β) (fun (x : Nat -> β) => Membership.mem.{u2, u2} (Nat -> β) (Set.{u2} (Nat -> β)) (Set.instMembershipSet.{u2} (Nat -> β)) x (Sigma.fst.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A))) (Pi.topologicalSpace.{0, u2} Nat (fun (ᾰ : Nat) => β) (fun (a : Nat) => _inst_2))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α _inst_1)) (Sigma.snd.{u2, max u2 u1} (Set.{u2} (Nat -> β)) (fun (s : Set.{u2} (Nat -> β)) => (Set.Elem.{u2} (Nat -> β) s) -> α) (CantorScheme.inducedMap.{u2, u1} β α A)))
Case conversion may be inaccurate. Consider using '#align cantor_scheme.vanishing_diam.map_continuous CantorScheme.VanishingDiam.map_continuousₓ'. -/
/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 :=
  by
  rw [Metric.continuous_iff']
  rintro ⟨x, hx⟩ ε ε_pos
  cases' hA.dist_lt _ ε_pos x with n hn
  rw [_root_.eventually_nhds_iff]
  refine' ⟨coe ⁻¹' cylinder x n, _, _, by simp⟩
  · rintro ⟨y, hy⟩ hyx
    rw [mem_preimage, Subtype.coe_mk, cylinder_eq_res, mem_set_of] at hyx
    apply hn
    · rw [← hyx]
      apply map_mem
    apply map_mem
  apply continuous_subtype_coe.is_open_preimage
  apply is_open_cylinder
#align cantor_scheme.vanishing_diam.map_continuous CantorScheme.VanishingDiam.map_continuous

#print CantorScheme.ClosureAntitone.map_of_vanishingDiam /-
/-- A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children
induces a total map. -/
theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : ∀ l, (A l).Nonempty) : (inducedMap A).1 = univ :=
  by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n) :=
    by
    have : Antitone fun n : ℕ => A (res x n) :=
      by
      refine' antitone_nat_of_succ_le _
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    cases' hdiam.dist_lt _ ε_pos x with n hn
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  cases' cauchySeq_tendsto_of_complete this with y hy
  use y
  rw [mem_Inter]
  intro n
  apply hanti _ (x n)
  apply mem_closure_of_tendsto hy
  rw [eventually_at_top]
  exact ⟨n.succ, umem _⟩
#align cantor_scheme.closure_antitone.map_of_vanishing_diam CantorScheme.ClosureAntitone.map_of_vanishingDiam
-/

end Metric

end CantorScheme

