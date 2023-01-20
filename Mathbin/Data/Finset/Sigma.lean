/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module data.finset.sigma
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Set.Sigma

/-!
# Finite sets in a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a few `finset` constructions on `Σ i, α i`.

## Main declarations

* `finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
* `finset.sigma_lift`: Lifts maps `α i → β i → finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → finset (Σ i, γ i)`.

## TODO

`finset.sigma_lift` can be generalized to any alternative functor. But to make the generalization
worth it, we must first refactor the functor library so that the `alternative` instance for `finset`
is computable and universe-polymorphic.
-/


open Function Multiset

variable {ι : Type _}

namespace Finset

section Sigma

variable {α : ι → Type _} {β : Type _} (s s₁ s₂ : Finset ι) (t t₁ t₂ : ∀ i, Finset (α i))

#print Finset.sigma /-
/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
protected def sigma : Finset (Σi, α i) :=
  ⟨_, s.Nodup.Sigma fun i => (t i).Nodup⟩
#align finset.sigma Finset.sigma
-/

variable {s s₁ s₂ t t₁ t₂}

/- warning: finset.mem_sigma -> Finset.mem_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Finset.{u1} ι} {t : forall (i : ι), Finset.{u2} (α i)} {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Finset.hasMem.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) a (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (And (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) s) (Membership.Mem.{u2, u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a)) (Finset.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a))) (Finset.hasMem.{u2} (α (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a))) (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (t (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Finset.{u2} ι} {t : forall (i : ι), Finset.{u1} (α i)} {a : Sigma.{u2, u1} ι (fun (i : ι) => α i)}, Iff (Membership.mem.{max u2 u1, max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Finset.instMembershipFinset.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) a (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (And (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a) s) (Membership.mem.{u1, u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a)) (Finset.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a))) (Finset.instMembershipFinset.{u1} (α (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a))) (Sigma.snd.{u2, u1} ι (fun (i : ι) => α i) a) (t (Sigma.fst.{u2, u1} ι (fun (i : ι) => α i) a))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sigma Finset.mem_sigmaₓ'. -/
@[simp]
theorem mem_sigma {a : Σi, α i} : a ∈ s.Sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 :=
  mem_sigma
#align finset.mem_sigma Finset.mem_sigma

/- warning: finset.coe_sigma -> Finset.coe_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Finset.{u1} ι) (t : forall (i : ι), Finset.{u2} (α i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Set.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Finset.Set.hasCoeT.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))))) (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (Set.Sigma.{u1, u2} ι (fun (i : ι) => α i) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s) (fun (i : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} (α i)) (Set.{u2} (α i)) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} (α i)) (Set.{u2} (α i)) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} (α i)) (Set.{u2} (α i)) (Finset.Set.hasCoeT.{u2} (α i)))) (t i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u1} (α i)), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Finset.toSet.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (Set.Sigma.{u2, u1} ι (fun (i : ι) => α i) (Finset.toSet.{u2} ι s) (fun (i : ι) => Finset.toSet.{u1} (α i) (t i)))
Case conversion may be inaccurate. Consider using '#align finset.coe_sigma Finset.coe_sigmaₓ'. -/
@[simp, norm_cast]
theorem coe_sigma (s : Finset ι) (t : ∀ i, Finset (α i)) :
    (s.Sigma t : Set (Σi, α i)) = (s : Set ι).Sigma fun i => t i :=
  Set.ext fun _ => mem_sigma
#align finset.coe_sigma Finset.coe_sigma

/- warning: finset.sigma_nonempty -> Finset.sigma_nonempty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Finset.{u1} ι} {t : forall (i : ι), Finset.{u2} (α i)}, Iff (Finset.Nonempty.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i)) (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s t)) (Exists.{succ u1} ι (fun (i : ι) => Exists.{0} (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => Finset.Nonempty.{u2} (α i) (t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Finset.{u2} ι} {t : forall (i : ι), Finset.{u1} (α i)}, Iff (Finset.Nonempty.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i)) (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s t)) (Exists.{succ u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (Finset.Nonempty.{u1} (α i) (t i))))
Case conversion may be inaccurate. Consider using '#align finset.sigma_nonempty Finset.sigma_nonemptyₓ'. -/
@[simp]
theorem sigma_nonempty : (s.Sigma t).Nonempty ↔ ∃ i ∈ s, (t i).Nonempty := by simp [Finset.Nonempty]
#align finset.sigma_nonempty Finset.sigma_nonempty

/- warning: finset.sigma_eq_empty -> Finset.sigma_eq_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Finset.{u1} ι} {t : forall (i : ι), Finset.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Finset.hasEmptyc.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))))) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Eq.{succ u2} (Finset.{u2} (α i)) (t i) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} (α i)) (Finset.hasEmptyc.{u2} (α i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Finset.{u2} ι} {t : forall (i : ι), Finset.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Finset.instEmptyCollectionFinset.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))))) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} (Finset.{u1} (α i)) (t i) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (α i)) (Finset.instEmptyCollectionFinset.{u1} (α i)))))
Case conversion may be inaccurate. Consider using '#align finset.sigma_eq_empty Finset.sigma_eq_emptyₓ'. -/
@[simp]
theorem sigma_eq_empty : s.Sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ := by
  simp only [← not_nonempty_iff_eq_empty, sigma_nonempty, not_exists]
#align finset.sigma_eq_empty Finset.sigma_eq_empty

/- warning: finset.sigma_mono -> Finset.sigma_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Finset.{u1} ι} {s₂ : Finset.{u1} ι} {t₁ : forall (i : ι), Finset.{u2} (α i)} {t₂ : forall (i : ι), Finset.{u2} (α i)}, (HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) s₁ s₂) -> (forall (i : ι), HasSubset.Subset.{u2} (Finset.{u2} (α i)) (Finset.hasSubset.{u2} (α i)) (t₁ i) (t₂ i)) -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Finset.hasSubset.{max u1 u2} (Sigma.{u1, u2} ι (fun (i : ι) => α i))) (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s₁ t₁) (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s₂ t₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Finset.{u2} ι} {s₂ : Finset.{u2} ι} {t₁ : forall (i : ι), Finset.{u1} (α i)} {t₂ : forall (i : ι), Finset.{u1} (α i)}, (HasSubset.Subset.{u2} (Finset.{u2} ι) (Finset.instHasSubsetFinset.{u2} ι) s₁ s₂) -> (forall (i : ι), HasSubset.Subset.{u1} (Finset.{u1} (α i)) (Finset.instHasSubsetFinset.{u1} (α i)) (t₁ i) (t₂ i)) -> (HasSubset.Subset.{max u2 u1} (Finset.{max u1 u2} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Finset.instHasSubsetFinset.{max u2 u1} (Sigma.{u2, u1} ι (fun (i : ι) => α i))) (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s₁ t₁) (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align finset.sigma_mono Finset.sigma_monoₓ'. -/
@[mono]
theorem sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.Sigma t₁ ⊆ s₂.Sigma t₂ :=
  fun ⟨i, a⟩ h =>
  let ⟨hi, ha⟩ := mem_sigma.1 h
  mem_sigma.2 ⟨hs hi, ht i ha⟩
#align finset.sigma_mono Finset.sigma_mono

/- warning: finset.pairwise_disjoint_map_sigma_mk -> Finset.pairwiseDisjoint_map_sigmaMk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Finset.{u1} ι} {t : forall (i : ι), Finset.{u2} (α i)}, Set.PairwiseDisjoint.{max u1 u2, u1} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (x : ι) => α x))) ι (Finset.partialOrder.{max u1 u2} (Sigma.{u1, u2} ι (fun (x : ι) => α x))) (Finset.orderBot.{max u1 u2} (Sigma.{u1, u2} ι (fun (x : ι) => α x))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s) (fun (i : ι) => Finset.map.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u1, u2} ι α i) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Finset.{u2} ι} {t : forall (i : ι), Finset.{u1} (α i)}, Set.PairwiseDisjoint.{max u2 u1, u2} (Finset.{max u2 u1} (Sigma.{u2, u1} ι (fun (x : ι) => α x))) ι (Finset.partialOrder.{max u2 u1} (Sigma.{u2, u1} ι (fun (x : ι) => α x))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u2 u1} (Sigma.{u2, u1} ι (fun (x : ι) => α x))) (Finset.toSet.{u2} ι s) (fun (i : ι) => Finset.map.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u2, u1} ι (fun (i : ι) => α i) i) (t i))
Case conversion may be inaccurate. Consider using '#align finset.pairwise_disjoint_map_sigma_mk Finset.pairwiseDisjoint_map_sigmaMkₓ'. -/
theorem pairwiseDisjoint_map_sigmaMk :
    (s : Set ι).PairwiseDisjoint fun i => (t i).map (Embedding.sigmaMk i) :=
  by
  intro i hi j hj hij
  rw [Function.onFun, disjoint_left]
  simp_rw [mem_map, Function.Embedding.sigmaMk_apply]
  rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hz'⟩
  exact hij (congr_arg Sigma.fst hz'.symm)
#align finset.pairwise_disjoint_map_sigma_mk Finset.pairwiseDisjoint_map_sigmaMk

/- warning: finset.disj_Union_map_sigma_mk -> Finset.disjUnionᵢ_map_sigma_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Finset.{u1} ι} {t : forall (i : ι), Finset.{u2} (α i)}, Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sigma.{u1, u2} ι (fun (x : ι) => α x))) (Finset.disjUnionₓ.{u1, max u1 u2} ι (Sigma.{u1, u2} ι (fun (x : ι) => α x)) s (fun (i : ι) => Finset.map.{u2, max u1 u2} (α i) (Sigma.{u1, u2} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u1, u2} ι α i) (t i)) (Finset.pairwiseDisjoint_map_sigmaMk.{u1, u2} ι α s (fun (i : ι) => t i))) (Finset.sigma.{u1, u2} ι (fun (x : ι) => α x) s t)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Finset.{u2} ι} {t : forall (i : ι), Finset.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Sigma.{u2, u1} ι (fun (x : ι) => α x))) (Finset.disjUnionᵢ.{u2, max u2 u1} ι (Sigma.{u2, u1} ι (fun (x : ι) => α x)) s (fun (i : ι) => Finset.map.{u1, max u2 u1} (α i) (Sigma.{u2, u1} ι (fun (x : ι) => α x)) (Function.Embedding.sigmaMk.{u2, u1} ι (fun (i : ι) => α i) i) (t i)) (Finset.pairwiseDisjoint_map_sigmaMk.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => t i))) (Finset.sigma.{u2, u1} ι (fun (x : ι) => α x) s t)
Case conversion may be inaccurate. Consider using '#align finset.disj_Union_map_sigma_mk Finset.disjUnionᵢ_map_sigma_mkₓ'. -/
@[simp]
theorem disjUnionᵢ_map_sigma_mk :
    s.disjUnion (fun i => (t i).map (Embedding.sigmaMk i)) pairwiseDisjoint_map_sigmaMk =
      s.Sigma t :=
  rfl
#align finset.disj_Union_map_sigma_mk Finset.disjUnionᵢ_map_sigma_mk

#print Finset.sigma_eq_bunionᵢ /-
theorem sigma_eq_bunionᵢ [DecidableEq (Σi, α i)] (s : Finset ι) (t : ∀ i, Finset (α i)) :
    s.Sigma t = s.bUnion fun i => (t i).map <| Embedding.sigmaMk i :=
  by
  ext ⟨x, y⟩
  simp [and_left_comm]
#align finset.sigma_eq_bUnion Finset.sigma_eq_bunionᵢ
-/

variable (s t) (f : (Σi, α i) → β)

/- warning: finset.sup_sigma -> Finset.sup_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : Type.{u3}} (s : Finset.{u1} ι) (t : forall (i : ι), Finset.{u2} (α i)) (f : (Sigma.{u1, u2} ι (fun (i : ι) => α i)) -> β) [_inst_1 : SemilatticeSup.{u3} β] [_inst_2 : OrderBot.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_1)))], Eq.{succ u3} β (Finset.sup.{u3, max u1 u2} β (Sigma.{u1, u2} ι (fun (i : ι) => α i)) _inst_1 _inst_2 (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s t) f) (Finset.sup.{u3, u1} β ι _inst_1 _inst_2 s (fun (i : ι) => Finset.sup.{u3, u2} β (α i) _inst_1 _inst_2 (t i) (fun (b : α i) => f (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i b))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {β : Type.{u3}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u1} (α i)) (f : (Sigma.{u2, u1} ι (fun (i : ι) => α i)) -> β) [_inst_1 : SemilatticeSup.{u3} β] [_inst_2 : OrderBot.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeSup.toPartialOrder.{u3} β _inst_1)))], Eq.{succ u3} β (Finset.sup.{u3, max u2 u1} β (Sigma.{u2, u1} ι (fun (i : ι) => α i)) _inst_1 _inst_2 (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s t) f) (Finset.sup.{u3, u2} β ι _inst_1 _inst_2 s (fun (i : ι) => Finset.sup.{u3, u1} β (α i) _inst_1 _inst_2 (t i) (fun (b : α i) => f (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i b))))
Case conversion may be inaccurate. Consider using '#align finset.sup_sigma Finset.sup_sigmaₓ'. -/
theorem sup_sigma [SemilatticeSup β] [OrderBot β] :
    (s.Sigma t).sup f = s.sup fun i => (t i).sup fun b => f ⟨i, b⟩ :=
  by
  simp only [le_antisymm_iff, Finset.sup_le_iff, mem_sigma, and_imp, Sigma.forall]
  exact
    ⟨fun i a hi ha => (le_sup hi).trans' <| le_sup ha, fun i hi a ha =>
      le_sup <| mem_sigma.2 ⟨hi, ha⟩⟩
#align finset.sup_sigma Finset.sup_sigma

/- warning: finset.inf_sigma -> Finset.inf_sigma is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : Type.{u3}} (s : Finset.{u1} ι) (t : forall (i : ι), Finset.{u2} (α i)) (f : (Sigma.{u1, u2} ι (fun (i : ι) => α i)) -> β) [_inst_1 : SemilatticeInf.{u3} β] [_inst_2 : OrderTop.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_1)))], Eq.{succ u3} β (Finset.inf.{u3, max u1 u2} β (Sigma.{u1, u2} ι (fun (i : ι) => α i)) _inst_1 _inst_2 (Finset.sigma.{u1, u2} ι (fun (i : ι) => α i) s t) f) (Finset.inf.{u3, u1} β ι _inst_1 _inst_2 s (fun (i : ι) => Finset.inf.{u3, u2} β (α i) _inst_1 _inst_2 (t i) (fun (b : α i) => f (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i b))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {β : Type.{u3}} (s : Finset.{u2} ι) (t : forall (i : ι), Finset.{u1} (α i)) (f : (Sigma.{u2, u1} ι (fun (i : ι) => α i)) -> β) [_inst_1 : SemilatticeInf.{u3} β] [_inst_2 : OrderTop.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (SemilatticeInf.toPartialOrder.{u3} β _inst_1)))], Eq.{succ u3} β (Finset.inf.{u3, max u2 u1} β (Sigma.{u2, u1} ι (fun (i : ι) => α i)) _inst_1 _inst_2 (Finset.sigma.{u2, u1} ι (fun (i : ι) => α i) s t) f) (Finset.inf.{u3, u2} β ι _inst_1 _inst_2 s (fun (i : ι) => Finset.inf.{u3, u1} β (α i) _inst_1 _inst_2 (t i) (fun (b : α i) => f (Sigma.mk.{u2, u1} ι (fun (i : ι) => α i) i b))))
Case conversion may be inaccurate. Consider using '#align finset.inf_sigma Finset.inf_sigmaₓ'. -/
theorem inf_sigma [SemilatticeInf β] [OrderTop β] :
    (s.Sigma t).inf f = s.inf fun i => (t i).inf fun b => f ⟨i, b⟩ :=
  @sup_sigma _ _ βᵒᵈ _ _ _ _ _
#align finset.inf_sigma Finset.inf_sigma

end Sigma

section SigmaLift

variable {α β γ : ι → Type _} [DecidableEq ι]

#print Finset.sigmaLift /-
/-- Lifts maps `α i → β i → finset (γ i)` to a map `Σ i, α i → Σ i, β i → finset (Σ i, γ i)`. -/
def sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β) :
    Finset (Sigma γ) :=
  dite (a.1 = b.1) (fun h => (f (h.rec a.2) b.2).map <| Embedding.sigmaMk _) fun _ => ∅
#align finset.sigma_lift Finset.sigmaLift
-/

/- warning: finset.mem_sigma_lift -> Finset.mem_sigmaLift is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (a : Sigma.{u1, u2} ι α) (b : Sigma.{u1, u3} ι β) (x : Sigma.{u1, u4} ι γ), Iff (Membership.Mem.{max u1 u4, max u1 u4} (Sigma.{u1, u4} ι γ) (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.hasMem.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) x (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)) (Exists.{0} (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι α a) (Sigma.fst.{u1, u4} ι γ x)) (fun (ha : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι α a) (Sigma.fst.{u1, u4} ι γ x)) => Exists.{0} (Eq.{succ u1} ι (Sigma.fst.{u1, u3} ι β b) (Sigma.fst.{u1, u4} ι γ x)) (fun (hb : Eq.{succ u1} ι (Sigma.fst.{u1, u3} ι β b) (Sigma.fst.{u1, u4} ι γ x)) => Membership.Mem.{u4, u4} (γ (Sigma.fst.{u1, u4} ι γ x)) (Finset.{u4} (γ (Sigma.fst.{u1, u4} ι γ x))) (Finset.hasMem.{u4} (γ (Sigma.fst.{u1, u4} ι γ x))) (Sigma.snd.{u1, u4} ι γ x) (f (Sigma.fst.{u1, u4} ι γ x) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι α a) α (Sigma.snd.{u1, u2} ι α a) (Sigma.fst.{u1, u4} ι γ x) ha) (Eq.ndrec.{succ u3, succ u1} ι (Sigma.fst.{u1, u3} ι β b) β (Sigma.snd.{u1, u3} ι β b) (Sigma.fst.{u1, u4} ι γ x) hb)))))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u3} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (a : Sigma.{u3, u2} ι α) (b : Sigma.{u3, u1} ι β) (x : Sigma.{u3, u4} ι γ), Iff (Membership.mem.{max u3 u4, max u4 u3} (Sigma.{u3, u4} ι γ) (Finset.{max u4 u3} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Finset.instMembershipFinset.{max u3 u4} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) x (Finset.sigmaLift.{u3, u2, u1, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)) (Exists.{0} (Eq.{succ u3} ι (Sigma.fst.{u3, u2} ι α a) (Sigma.fst.{u3, u4} ι γ x)) (fun (ha : Eq.{succ u3} ι (Sigma.fst.{u3, u2} ι α a) (Sigma.fst.{u3, u4} ι γ x)) => Exists.{0} (Eq.{succ u3} ι (Sigma.fst.{u3, u1} ι β b) (Sigma.fst.{u3, u4} ι γ x)) (fun (hb : Eq.{succ u3} ι (Sigma.fst.{u3, u1} ι β b) (Sigma.fst.{u3, u4} ι γ x)) => Membership.mem.{u4, u4} (γ (Sigma.fst.{u3, u4} ι γ x)) (Finset.{u4} (γ (Sigma.fst.{u3, u4} ι γ x))) (Finset.instMembershipFinset.{u4} (γ (Sigma.fst.{u3, u4} ι γ x))) (Sigma.snd.{u3, u4} ι γ x) (f (Sigma.fst.{u3, u4} ι γ x) (Eq.rec.{succ u2, succ u3} ι (Sigma.fst.{u3, u2} ι α a) (fun (x._@.Mathlib.Data.Finset.Sigma._hyg.1294 : ι) (h._@.Mathlib.Data.Finset.Sigma._hyg.1295 : Eq.{succ u3} ι (Sigma.fst.{u3, u2} ι α a) x._@.Mathlib.Data.Finset.Sigma._hyg.1294) => α x._@.Mathlib.Data.Finset.Sigma._hyg.1294) (Sigma.snd.{u3, u2} ι α a) (Sigma.fst.{u3, u4} ι γ x) ha) (Eq.rec.{succ u1, succ u3} ι (Sigma.fst.{u3, u1} ι β b) (fun (x._@.Mathlib.Data.Finset.Sigma._hyg.1299 : ι) (h._@.Mathlib.Data.Finset.Sigma._hyg.1300 : Eq.{succ u3} ι (Sigma.fst.{u3, u1} ι β b) x._@.Mathlib.Data.Finset.Sigma._hyg.1299) => β x._@.Mathlib.Data.Finset.Sigma._hyg.1299) (Sigma.snd.{u3, u1} ι β b) (Sigma.fst.{u3, u4} ι γ x) hb)))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sigma_lift Finset.mem_sigmaLiftₓ'. -/
theorem mem_sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α) (b : Sigma β)
    (x : Sigma γ) :
    x ∈ sigmaLift f a b ↔ ∃ (ha : a.1 = x.1)(hb : b.1 = x.1), x.2 ∈ f (ha.rec a.2) (hb.rec b.2) :=
  by
  obtain ⟨⟨i, a⟩, j, b⟩ := a, b
  obtain rfl | h := Decidable.eq_or_ne i j
  · constructor
    · simp_rw [sigma_lift, dif_pos rfl, mem_map, embedding.sigma_mk_apply]
      rintro ⟨x, hx, rfl⟩
      exact ⟨rfl, rfl, hx⟩
    · rintro ⟨⟨⟩, ⟨⟩, hx⟩
      rw [sigma_lift, dif_pos rfl, mem_map]
      exact ⟨_, hx, by simp [Sigma.ext_iff]⟩
  · rw [sigma_lift, dif_neg h]
    refine' iff_of_false (not_mem_empty _) _
    rintro ⟨⟨⟩, ⟨⟩, _⟩
    exact h rfl
#align finset.mem_sigma_lift Finset.mem_sigmaLift

/- warning: finset.mk_mem_sigma_lift -> Finset.mk_mem_sigmaLift is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (i : ι) (a : α i) (b : β i) (x : γ i), Iff (Membership.Mem.{max u1 u4, max u1 u4} (Sigma.{u1, u4} ι γ) (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.hasMem.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Sigma.mk.{u1, u4} ι γ i x) (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f (Sigma.mk.{u1, u2} ι (fun (i : ι) => α i) i a) (Sigma.mk.{u1, u3} ι (fun (i : ι) => β i) i b))) (Membership.Mem.{u4, u4} (γ i) (Finset.{u4} (γ i)) (Finset.hasMem.{u4} (γ i)) x (f i a b))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u3} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (i : ι) (a : α i) (b : β i) (x : γ i), Iff (Membership.mem.{max u3 u4, max u4 u3} (Sigma.{u3, u4} ι γ) (Finset.{max u4 u3} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Finset.instMembershipFinset.{max u3 u4} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Sigma.mk.{u3, u4} ι γ i x) (Finset.sigmaLift.{u3, u2, u1, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f (Sigma.mk.{u3, u2} ι (fun (i : ι) => α i) i a) (Sigma.mk.{u3, u1} ι (fun (i : ι) => β i) i b))) (Membership.mem.{u4, u4} (γ i) (Finset.{u4} (γ i)) (Finset.instMembershipFinset.{u4} (γ i)) x (f i a b))
Case conversion may be inaccurate. Consider using '#align finset.mk_mem_sigma_lift Finset.mk_mem_sigmaLiftₓ'. -/
theorem mk_mem_sigmaLift (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (i : ι) (a : α i) (b : β i)
    (x : γ i) : (⟨i, x⟩ : Sigma γ) ∈ sigmaLift f ⟨i, a⟩ ⟨i, b⟩ ↔ x ∈ f a b :=
  by
  rw [sigma_lift, dif_pos rfl, mem_map]
  refine' ⟨_, fun hx => ⟨_, hx, rfl⟩⟩
  rintro ⟨x, hx, _, rfl⟩
  exact hx
#align finset.mk_mem_sigma_lift Finset.mk_mem_sigmaLift

/- warning: finset.not_mem_sigma_lift_of_ne_left -> Finset.not_mem_sigmaLift_of_ne_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (a : Sigma.{u1, u2} ι α) (b : Sigma.{u1, u3} ι β) (x : Sigma.{u1, u4} ι γ), (Ne.{succ u1} ι (Sigma.fst.{u1, u2} ι α a) (Sigma.fst.{u1, u4} ι γ x)) -> (Not (Membership.Mem.{max u1 u4, max u1 u4} (Sigma.{u1, u4} ι γ) (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.hasMem.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) x (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u3} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (a : Sigma.{u3, u2} ι α) (b : Sigma.{u3, u1} ι β) (x : Sigma.{u3, u4} ι γ), (Ne.{succ u3} ι (Sigma.fst.{u3, u2} ι α a) (Sigma.fst.{u3, u4} ι γ x)) -> (Not (Membership.mem.{max u3 u4, max u4 u3} (Sigma.{u3, u4} ι γ) (Finset.{max u4 u3} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Finset.instMembershipFinset.{max u3 u4} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) x (Finset.sigmaLift.{u3, u2, u1, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)))
Case conversion may be inaccurate. Consider using '#align finset.not_mem_sigma_lift_of_ne_left Finset.not_mem_sigmaLift_of_ne_leftₓ'. -/
theorem not_mem_sigmaLift_of_ne_left (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) (a : Sigma α)
    (b : Sigma β) (x : Sigma γ) (h : a.1 ≠ x.1) : x ∉ sigmaLift f a b :=
  by
  rw [mem_sigma_lift]
  exact fun H => h H.fst
#align finset.not_mem_sigma_lift_of_ne_left Finset.not_mem_sigmaLift_of_ne_left

/- warning: finset.not_mem_sigma_lift_of_ne_right -> Finset.not_mem_sigmaLift_of_ne_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) {a : Sigma.{u1, u2} ι α} (b : Sigma.{u1, u3} ι β) {x : Sigma.{u1, u4} ι γ}, (Ne.{succ u1} ι (Sigma.fst.{u1, u3} ι β b) (Sigma.fst.{u1, u4} ι γ x)) -> (Not (Membership.Mem.{max u1 u4, max u1 u4} (Sigma.{u1, u4} ι γ) (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.hasMem.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) x (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u3} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) {a : Sigma.{u3, u2} ι α} (b : Sigma.{u3, u1} ι β) {x : Sigma.{u3, u4} ι γ}, (Ne.{succ u3} ι (Sigma.fst.{u3, u1} ι β b) (Sigma.fst.{u3, u4} ι γ x)) -> (Not (Membership.mem.{max u3 u4, max u4 u3} (Sigma.{u3, u4} ι γ) (Finset.{max u4 u3} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Finset.instMembershipFinset.{max u3 u4} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) x (Finset.sigmaLift.{u3, u2, u1, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)))
Case conversion may be inaccurate. Consider using '#align finset.not_mem_sigma_lift_of_ne_right Finset.not_mem_sigmaLift_of_ne_rightₓ'. -/
theorem not_mem_sigmaLift_of_ne_right (f : ∀ ⦃i⦄, α i → β i → Finset (γ i)) {a : Sigma α}
    (b : Sigma β) {x : Sigma γ} (h : b.1 ≠ x.1) : x ∉ sigmaLift f a b :=
  by
  rw [mem_sigma_lift]
  exact fun H => h H.snd.fst
#align finset.not_mem_sigma_lift_of_ne_right Finset.not_mem_sigmaLift_of_ne_right

variable {f g : ∀ ⦃i⦄, α i → β i → Finset (γ i)} {a : Σi, α i} {b : Σi, β i}

/- warning: finset.sigma_lift_nonempty -> Finset.sigmaLift_nonempty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] {f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))} {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u3} ι (fun (i : ι) => β i)}, Iff (Finset.Nonempty.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i)) (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)) (Exists.{0} (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) => Finset.Nonempty.{u4} (γ (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) (f (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b) h) (Sigma.snd.{u1, u3} ι (fun (i : ι) => β i) b))))
but is expected to have type
  forall {ι : Type.{u4}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u3}} [_inst_1 : DecidableEq.{succ u4} ι] {f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u3} (γ i))} {a : Sigma.{u4, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u4, u1} ι (fun (i : ι) => β i)}, Iff (Finset.Nonempty.{max u4 u3} (Sigma.{u4, u3} ι (fun (i : ι) => γ i)) (Finset.sigmaLift.{u4, u2, u1, u3} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)) (Exists.{0} (Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) (fun (h : Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) => Finset.Nonempty.{u3} (γ (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) (f (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b) (Eq.rec.{succ u2, succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Finset.Sigma._hyg.1922 : ι) (h._@.Mathlib.Data.Finset.Sigma._hyg.1923 : Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Finset.Sigma._hyg.1922) => α x._@.Mathlib.Data.Finset.Sigma._hyg.1922) (Sigma.snd.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b) h) (Sigma.snd.{u4, u1} ι (fun (i : ι) => β i) b))))
Case conversion may be inaccurate. Consider using '#align finset.sigma_lift_nonempty Finset.sigmaLift_nonemptyₓ'. -/
theorem sigmaLift_nonempty :
    (sigmaLift f a b).Nonempty ↔ ∃ h : a.1 = b.1, (f (h.rec a.2) b.2).Nonempty :=
  by
  simp_rw [nonempty_iff_ne_empty]
  convert dite_ne_right_iff
  ext h
  simp_rw [← nonempty_iff_ne_empty]
  exact map_nonempty.symm
#align finset.sigma_lift_nonempty Finset.sigmaLift_nonempty

/- warning: finset.sigma_lift_eq_empty -> Finset.sigmaLift_eq_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] {f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))} {a : Sigma.{u1, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u1, u3} ι (fun (i : ι) => β i)}, Iff (Eq.{succ (max u1 u4)} (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b) (EmptyCollection.emptyCollection.{max u1 u4} (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.hasEmptyc.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))))) (forall (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)), Eq.{succ u4} (Finset.{u4} (γ (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b))) (f (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b) h) (Sigma.snd.{u1, u3} ι (fun (i : ι) => β i) b)) (EmptyCollection.emptyCollection.{u4} (Finset.{u4} (γ (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b))) (Finset.hasEmptyc.{u4} (γ (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)))))
but is expected to have type
  forall {ι : Type.{u4}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u3}} [_inst_1 : DecidableEq.{succ u4} ι] {f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u3} (γ i))} {a : Sigma.{u4, u2} ι (fun (i : ι) => α i)} {b : Sigma.{u4, u1} ι (fun (i : ι) => β i)}, Iff (Eq.{max (succ u4) (succ u3)} (Finset.{max u3 u4} (Sigma.{u4, u3} ι (fun (i : ι) => γ i))) (Finset.sigmaLift.{u4, u2, u1, u3} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b) (EmptyCollection.emptyCollection.{max u4 u3} (Finset.{max u3 u4} (Sigma.{u4, u3} ι (fun (i : ι) => γ i))) (Finset.instEmptyCollectionFinset.{max u4 u3} (Sigma.{u4, u3} ι (fun (i : ι) => γ i))))) (forall (h : Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)), Eq.{succ u3} (Finset.{u3} (γ (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b))) (f (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b) (Eq.rec.{succ u2, succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Finset.Sigma._hyg.2041 : ι) (h._@.Mathlib.Data.Finset.Sigma._hyg.2042 : Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Finset.Sigma._hyg.2041) => α x._@.Mathlib.Data.Finset.Sigma._hyg.2041) (Sigma.snd.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b) h) (Sigma.snd.{u4, u1} ι (fun (i : ι) => β i) b)) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} (γ (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b))) (Finset.instEmptyCollectionFinset.{u3} (γ (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)))))
Case conversion may be inaccurate. Consider using '#align finset.sigma_lift_eq_empty Finset.sigmaLift_eq_emptyₓ'. -/
theorem sigmaLift_eq_empty : sigmaLift f a b = ∅ ↔ ∀ h : a.1 = b.1, f (h.rec a.2) b.2 = ∅ :=
  by
  convert dite_eq_right_iff
  exact forall_congr fun h => propext map_eq_empty.symm
#align finset.sigma_lift_eq_empty Finset.sigmaLift_eq_empty

/- warning: finset.sigma_lift_mono -> Finset.sigmaLift_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] {f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))} {g : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))}, (forall {{i : ι}} {{a : α i}} {{b : β i}}, HasSubset.Subset.{u4} (Finset.{u4} (γ i)) (Finset.hasSubset.{u4} (γ i)) (f i a b) (g i a b)) -> (forall (a : Sigma.{u1, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u1, u3} ι (fun (i : ι) => β i)), HasSubset.Subset.{max u1 u4} (Finset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.hasSubset.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i))) (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b) (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) g a b))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u3} ι] {f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))} {g : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))}, (forall {{i : ι}} {{a : α i}} {{b : β i}}, HasSubset.Subset.{u4} (Finset.{u4} (γ i)) (Finset.instHasSubsetFinset.{u4} (γ i)) (f i a b) (g i a b)) -> (forall (a : Sigma.{u3, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u3, u1} ι (fun (i : ι) => β i)), HasSubset.Subset.{max u4 u3} (Finset.{max u4 u3} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Finset.instHasSubsetFinset.{max u3 u4} (Sigma.{u3, u4} ι (fun (i : ι) => γ i))) (Finset.sigmaLift.{u3, u2, u1, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b) (Finset.sigmaLift.{u3, u2, u1, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) g a b))
Case conversion may be inaccurate. Consider using '#align finset.sigma_lift_mono Finset.sigmaLift_monoₓ'. -/
theorem sigmaLift_mono (h : ∀ ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b ⊆ g a b) (a : Σi, α i) (b : Σi, β i) :
    sigmaLift f a b ⊆ sigmaLift g a b := by
  rintro x hx
  rw [mem_sigma_lift] at hx⊢
  obtain ⟨ha, hb, hx⟩ := hx
  exact ⟨ha, hb, h hx⟩
#align finset.sigma_lift_mono Finset.sigmaLift_mono

variable (f a b)

/- warning: finset.card_sigma_lift -> Finset.card_sigmaLift is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {γ : ι -> Type.{u4}} [_inst_1 : DecidableEq.{succ u1} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u4} (γ i))) (a : Sigma.{u1, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u1, u3} ι (fun (i : ι) => β i)), Eq.{1} Nat (Finset.card.{max u1 u4} (Sigma.{u1, u4} ι (fun (i : ι) => γ i)) (Finset.sigmaLift.{u1, u2, u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)) (dite.{1} Nat (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) (_inst_1 (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) (fun (h : Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) => Finset.card.{u4} (γ (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b)) (f (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b) (Eq.ndrec.{succ u2, succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) α (Sigma.snd.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b) h) (Sigma.snd.{u1, u3} ι (fun (i : ι) => β i) b))) (fun (_x : Not (Eq.{succ u1} ι (Sigma.fst.{u1, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u1, u3} ι (fun (i : ι) => β i) b))) => OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))
but is expected to have type
  forall {ι : Type.{u4}} {α : ι -> Type.{u2}} {β : ι -> Type.{u1}} {γ : ι -> Type.{u3}} [_inst_1 : DecidableEq.{succ u4} ι] (f : forall {{i : ι}}, (α i) -> (β i) -> (Finset.{u3} (γ i))) (a : Sigma.{u4, u2} ι (fun (i : ι) => α i)) (b : Sigma.{u4, u1} ι (fun (i : ι) => β i)), Eq.{1} Nat (Finset.card.{max u4 u3} (Sigma.{u4, u3} ι (fun (i : ι) => γ i)) (Finset.sigmaLift.{u4, u2, u1, u3} ι (fun (i : ι) => α i) (fun (i : ι) => β i) (fun (i : ι) => γ i) (fun (a : ι) (b : ι) => _inst_1 a b) f a b)) (dite.{1} Nat (Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) (_inst_1 (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) (fun (h : Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) => Finset.card.{u3} (γ (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b)) (f (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b) (Eq.rec.{succ u2, succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (fun (x._@.Mathlib.Data.Finset.Sigma._hyg.2375 : ι) (h._@.Mathlib.Data.Finset.Sigma._hyg.2376 : Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) x._@.Mathlib.Data.Finset.Sigma._hyg.2375) => α x._@.Mathlib.Data.Finset.Sigma._hyg.2375) (Sigma.snd.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b) h) (Sigma.snd.{u4, u1} ι (fun (i : ι) => β i) b))) (fun (_x : Not (Eq.{succ u4} ι (Sigma.fst.{u4, u2} ι (fun (i : ι) => α i) a) (Sigma.fst.{u4, u1} ι (fun (i : ι) => β i) b))) => OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))
Case conversion may be inaccurate. Consider using '#align finset.card_sigma_lift Finset.card_sigmaLiftₓ'. -/
theorem card_sigmaLift :
    (sigmaLift f a b).card = dite (a.1 = b.1) (fun h => (f (h.rec a.2) b.2).card) fun _ => 0 :=
  by
  convert apply_dite _ _ _ _
  ext h
  exact (card_map _).symm
#align finset.card_sigma_lift Finset.card_sigmaLift

end SigmaLift

end Finset

