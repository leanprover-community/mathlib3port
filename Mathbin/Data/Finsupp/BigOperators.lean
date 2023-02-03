/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module data.finsupp.big_operators
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Defs
import Mathbin.Data.Finset.Pairwise

/-!

# Sums of collections of finsupp, and their support

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This file provides results about the `finsupp.support` of sums of collections of `finsupp`,
including sums of `list`, `multiset`, and `finset`.

The support of the sum is a subset of the union of the supports:
* `list.support_sum_subset`
* `multiset.support_sum_subset`
* `finset.support_sum_subset`

The support of the sum of pairwise disjoint finsupps is equal to the union of the supports
* `list.support_sum_eq`
* `multiset.support_sum_eq`
* `finset.support_sum_eq`

Member in the support of the indexed union over a collection iff
it is a member of the support of a member of the collection:
* `list.mem_foldr_sup_support_iff`
* `multiset.mem_sup_map_support_iff`
* `finset.mem_sup_support_iff`

-/


variable {ι M : Type _} [DecidableEq ι]

/- warning: list.support_sum_subset -> List.support_sum_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddMonoid.{u2} M] (l : List.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)))), HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)) (List.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finsupp.hasAdd.{u1, u2} ι M (AddMonoid.toAddZeroClass.{u2} M _inst_2)) (Finsupp.hasZero.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) l)) (List.foldr.{max u1 u2, u1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finset.{u1} ι) (Function.comp.{max (succ u1) (succ u2), succ u1, succ u1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finset.{u1} ι) ((Finset.{u1} ι) -> (Finset.{u1} ι)) (HasSup.sup.{u1} (Finset.{u1} ι) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))))) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.hasEmptyc.{u1} ι)) l)
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddMonoid.{u2} M] (l : List.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2))), HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.instHasSubsetFinset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2) (List.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finsupp.instAddFinsuppToZero.{u1, u2} ι M (AddMonoid.toAddZeroClass.{u2} M _inst_2)) (Finsupp.hasZero.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) l)) (List.foldr.{max u2 u1, u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finset.{u1} ι) (Function.comp.{succ (max u2 u1), succ u1, succ u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finset.{u1} ι) ((Finset.{u1} ι) -> (Finset.{u1} ι)) (fun (x._@.Mathlib.Data.Finsupp.BigOperators._hyg.45 : Finset.{u1} ι) (x._@.Mathlib.Data.Finsupp.BigOperators._hyg.47 : Finset.{u1} ι) => HasSup.sup.{u1} (Finset.{u1} ι) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b)))) x._@.Mathlib.Data.Finsupp.BigOperators._hyg.45 x._@.Mathlib.Data.Finsupp.BigOperators._hyg.47) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.instEmptyCollectionFinset.{u1} ι)) l)
Case conversion may be inaccurate. Consider using '#align list.support_sum_subset List.support_sum_subsetₓ'. -/
theorem List.support_sum_subset [AddMonoid M] (l : List (ι →₀ M)) :
    l.Sum.support ⊆ l.foldr ((· ⊔ ·) ∘ Finsupp.support) ∅ :=
  by
  induction' l with hd tl IH
  · simp
  · simp only [List.sum_cons, Finset.union_comm]
    refine' finsupp.support_add.trans (Finset.union_subset_union _ IH)
    rfl
#align list.support_sum_subset List.support_sum_subset

/- warning: multiset.support_sum_subset -> Multiset.support_sum_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Multiset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))), HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Multiset.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s)) (Multiset.sup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.orderBot.{u1} ι) (Multiset.map.{max u1 u2, u1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) s))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Multiset.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))), HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.instHasSubsetFinset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Multiset.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s)) (Multiset.sup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) (Multiset.map.{max u2 u1, u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) s))
Case conversion may be inaccurate. Consider using '#align multiset.support_sum_subset Multiset.support_sum_subsetₓ'. -/
theorem Multiset.support_sum_subset [AddCommMonoid M] (s : Multiset (ι →₀ M)) :
    s.Sum.support ⊆ (s.map Finsupp.support).sup :=
  by
  induction s using Quot.inductionOn
  simpa using List.support_sum_subset _
#align multiset.support_sum_subset Multiset.support_sum_subset

/- warning: finset.support_sum_subset -> Finset.support_sum_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Finset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))), HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.hasSubset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finset.sum.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s (id.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))) (Finset.sup.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.orderBot.{u1} ι) s (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Finset.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))), HasSubset.Subset.{u1} (Finset.{u1} ι) (Finset.instHasSubsetFinset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Finset.sum.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s (id.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))))) (Finset.sup.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) s (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))
Case conversion may be inaccurate. Consider using '#align finset.support_sum_subset Finset.support_sum_subsetₓ'. -/
theorem Finset.support_sum_subset [AddCommMonoid M] (s : Finset (ι →₀ M)) :
    (s.Sum id).support ⊆ Finset.sup s Finsupp.support := by
  classical convert Multiset.support_sum_subset s.1 <;> simp
#align finset.support_sum_subset Finset.support_sum_subset

/- warning: list.mem_foldr_sup_support_iff -> List.mem_foldr_sup_support_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Zero.{u2} M] {l : List.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)} {x : ι}, Iff (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x (List.foldr.{max u1 u2, u1} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{u1} ι) (Function.comp.{max (succ u1) (succ u2), succ u1, succ u1} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{u1} ι) ((Finset.{u1} ι) -> (Finset.{u1} ι)) (HasSup.sup.{u1} (Finset.{u1} ι) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))))) (Finsupp.support.{u1, u2} ι M _inst_2)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.hasEmptyc.{u1} ι)) l)) (Exists.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M _inst_2) (fun (f : Finsupp.{u1, u2} ι M _inst_2) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (List.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) (List.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f l) (fun (hf : Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (List.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) (List.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f l) => Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x (Finsupp.support.{u1, u2} ι M _inst_2 f))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Zero.{u2} M] {l : List.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)} {x : ι}, Iff (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x (List.foldr.{max u2 u1, u1} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{u1} ι) (Function.comp.{succ (max u2 u1), succ u1, succ u1} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{u1} ι) ((Finset.{u1} ι) -> (Finset.{u1} ι)) (fun (x._@.Mathlib.Data.Finsupp.BigOperators._hyg.215 : Finset.{u1} ι) (x._@.Mathlib.Data.Finsupp.BigOperators._hyg.217 : Finset.{u1} ι) => HasSup.sup.{u1} (Finset.{u1} ι) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b)))) x._@.Mathlib.Data.Finsupp.BigOperators._hyg.215 x._@.Mathlib.Data.Finsupp.BigOperators._hyg.217) (Finsupp.support.{u1, u2} ι M _inst_2)) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.instEmptyCollectionFinset.{u1} ι)) l)) (Exists.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M _inst_2) (fun (f : Finsupp.{u1, u2} ι M _inst_2) => Exists.{0} (Membership.mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (List.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)) (List.instMembershipList.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f l) (fun (hf : Membership.mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (List.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)) (List.instMembershipList.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f l) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x (Finsupp.support.{u1, u2} ι M _inst_2 f))))
Case conversion may be inaccurate. Consider using '#align list.mem_foldr_sup_support_iff List.mem_foldr_sup_support_iffₓ'. -/
theorem List.mem_foldr_sup_support_iff [Zero M] {l : List (ι →₀ M)} {x : ι} :
    x ∈ l.foldr ((· ⊔ ·) ∘ Finsupp.support) ∅ ↔ ∃ (f : ι →₀ M)(hf : f ∈ l), x ∈ f.support :=
  by
  simp only [Finset.sup_eq_union, List.foldr_map, Finsupp.mem_support_iff, exists_prop]
  induction' l with hd tl IH
  · simp
  · simp only [IH, List.foldr_cons, Finset.mem_union, Finsupp.mem_support_iff, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact ⟨hd, Or.inl rfl, h⟩
      · exact h.imp fun f hf => hf.imp_left Or.inr
    · rintro ⟨f, rfl | hf, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨f, hf, h⟩
#align list.mem_foldr_sup_support_iff List.mem_foldr_sup_support_iff

/- warning: multiset.mem_sup_map_support_iff -> Multiset.mem_sup_map_support_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Zero.{u2} M] {s : Multiset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)} {x : ι}, Iff (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x (Multiset.sup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.orderBot.{u1} ι) (Multiset.map.{max u1 u2, u1} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M _inst_2) s))) (Exists.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M _inst_2) (fun (f : Finsupp.{u1, u2} ι M _inst_2) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Multiset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) (Multiset.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) (fun (hf : Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Multiset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) (Multiset.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) => Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x (Finsupp.support.{u1, u2} ι M _inst_2 f))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Zero.{u2} M] {s : Multiset.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)} {x : ι}, Iff (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x (Multiset.sup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) (Multiset.map.{max u2 u1, u1} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M _inst_2) s))) (Exists.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M _inst_2) (fun (f : Finsupp.{u1, u2} ι M _inst_2) => Exists.{0} (Membership.mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Multiset.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)) (Multiset.instMembershipMultiset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) (fun (hf : Membership.mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Multiset.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)) (Multiset.instMembershipMultiset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x (Finsupp.support.{u1, u2} ι M _inst_2 f))))
Case conversion may be inaccurate. Consider using '#align multiset.mem_sup_map_support_iff Multiset.mem_sup_map_support_iffₓ'. -/
theorem Multiset.mem_sup_map_support_iff [Zero M] {s : Multiset (ι →₀ M)} {x : ι} :
    x ∈ (s.map Finsupp.support).sup ↔ ∃ (f : ι →₀ M)(hf : f ∈ s), x ∈ f.support :=
  Quot.inductionOn s fun _ => by simpa using List.mem_foldr_sup_support_iff
#align multiset.mem_sup_map_support_iff Multiset.mem_sup_map_support_iff

/- warning: finset.mem_sup_support_iff -> Finset.mem_sup_support_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Zero.{u2} M] {s : Finset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)} {x : ι}, Iff (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x (Finset.sup.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M _inst_2) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.orderBot.{u1} ι) s (Finsupp.support.{u1, u2} ι M _inst_2))) (Exists.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M _inst_2) (fun (f : Finsupp.{u1, u2} ι M _inst_2) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) (Finset.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) (fun (hf : Membership.Mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) (Finset.hasMem.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) => Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) x (Finsupp.support.{u1, u2} ι M _inst_2 f))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Zero.{u2} M] {s : Finset.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)} {x : ι}, Iff (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x (Finset.sup.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M _inst_2) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) s (Finsupp.support.{u1, u2} ι M _inst_2))) (Exists.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M _inst_2) (fun (f : Finsupp.{u1, u2} ι M _inst_2) => Exists.{0} (Membership.mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)) (Finset.instMembershipFinset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) (fun (hf : Membership.mem.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M _inst_2) (Finset.{max u2 u1} (Finsupp.{u1, u2} ι M _inst_2)) (Finset.instMembershipFinset.{max u1 u2} (Finsupp.{u1, u2} ι M _inst_2)) f s) => Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x (Finsupp.support.{u1, u2} ι M _inst_2 f))))
Case conversion may be inaccurate. Consider using '#align finset.mem_sup_support_iff Finset.mem_sup_support_iffₓ'. -/
theorem Finset.mem_sup_support_iff [Zero M] {s : Finset (ι →₀ M)} {x : ι} :
    x ∈ s.sup Finsupp.support ↔ ∃ (f : ι →₀ M)(hf : f ∈ s), x ∈ f.support :=
  Multiset.mem_sup_map_support_iff
#align finset.mem_sup_support_iff Finset.mem_sup_support_iff

/- warning: list.support_sum_eq -> List.support_sum_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddMonoid.{u2} M] (l : List.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)))), (List.Pairwise.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Function.onFun.{succ (max u1 u2), succ u1, 1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finset.{u1} ι) Prop (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.orderBot.{u1} ι)) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)))) l) -> (Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)) (List.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finsupp.hasAdd.{u1, u2} ι M (AddMonoid.toAddZeroClass.{u2} M _inst_2)) (Finsupp.hasZero.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) l)) (List.foldr.{max u1 u2, u1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finset.{u1} ι) (Function.comp.{max (succ u1) (succ u2), succ u1, succ u1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2))) (Finset.{u1} ι) ((Finset.{u1} ι) -> (Finset.{u1} ι)) (HasSup.sup.{u1} (Finset.{u1} ι) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))))) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M _inst_2)))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.hasEmptyc.{u1} ι)) l))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddMonoid.{u2} M] (l : List.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2))), (List.Pairwise.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Function.onFun.{succ (max u2 u1), succ u1, 1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finset.{u1} ι) Prop (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι)) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2))) l) -> (Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2) (List.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finsupp.instAddFinsuppToZero.{u1, u2} ι M (AddMonoid.toAddZeroClass.{u2} M _inst_2)) (Finsupp.hasZero.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) l)) (List.foldr.{max u2 u1, u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finset.{u1} ι) (Function.comp.{succ (max u2 u1), succ u1, succ u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2)) (Finset.{u1} ι) ((Finset.{u1} ι) -> (Finset.{u1} ι)) (fun (x._@.Mathlib.Data.Finsupp.BigOperators._hyg.464 : Finset.{u1} ι) (x._@.Mathlib.Data.Finsupp.BigOperators._hyg.466 : Finset.{u1} ι) => HasSup.sup.{u1} (Finset.{u1} ι) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b)))) x._@.Mathlib.Data.Finsupp.BigOperators._hyg.464 x._@.Mathlib.Data.Finsupp.BigOperators._hyg.466) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M _inst_2))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.instEmptyCollectionFinset.{u1} ι)) l))
Case conversion may be inaccurate. Consider using '#align list.support_sum_eq List.support_sum_eqₓ'. -/
theorem List.support_sum_eq [AddMonoid M] (l : List (ι →₀ M))
    (hl : l.Pairwise (Disjoint on Finsupp.support)) :
    l.Sum.support = l.foldr ((· ⊔ ·) ∘ Finsupp.support) ∅ :=
  by
  induction' l with hd tl IH
  · simp
  · simp only [List.pairwise_cons] at hl
    simp only [List.sum_cons, List.foldr_cons, Function.comp_apply]
    rw [Finsupp.support_add_eq, IH hl.right, Finset.sup_eq_union]
    suffices Disjoint hd.support (tl.foldr ((· ⊔ ·) ∘ Finsupp.support) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    · rw [← List.foldr_map, ← Finset.bot_eq_empty, List.foldr_sup_eq_sup_toFinset]
      rw [Finset.disjoint_sup_right]
      intro f hf
      simp only [List.mem_toFinset, List.mem_map'] at hf
      obtain ⟨f, hf, rfl⟩ := hf
      exact hl.left _ hf
#align list.support_sum_eq List.support_sum_eq

/- warning: multiset.support_sum_eq -> Multiset.support_sum_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Multiset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))), (Multiset.Pairwise.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Function.onFun.{succ (max u1 u2), succ u1, 1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finset.{u1} ι) Prop (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.orderBot.{u1} ι)) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) s) -> (Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Multiset.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s)) (Multiset.sup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.orderBot.{u1} ι) (Multiset.map.{max u1 u2, u1} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) s)))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Multiset.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))), (Multiset.Pairwise.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Function.onFun.{succ (max u2 u1), succ u1, 1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finset.{u1} ι) Prop (Disjoint.{u1} (Finset.{u1} ι) (Finset.partialOrder.{u1} ι) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι)) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) s) -> (Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Multiset.sum.{max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s)) (Multiset.sup.{u1} (Finset.{u1} ι) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) (Multiset.map.{max u2 u1, u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) s)))
Case conversion may be inaccurate. Consider using '#align multiset.support_sum_eq Multiset.support_sum_eqₓ'. -/
theorem Multiset.support_sum_eq [AddCommMonoid M] (s : Multiset (ι →₀ M))
    (hs : s.Pairwise (Disjoint on Finsupp.support)) : s.Sum.support = (s.map Finsupp.support).sup :=
  by
  induction s using Quot.inductionOn
  obtain ⟨l, hl, hd⟩ := hs
  convert List.support_sum_eq _ _
  · simp
  · simp
  · simp only [Multiset.quot_mk_to_coe'', Multiset.coe_map, Multiset.coe_eq_coe] at hl
    exact hl.symm.pairwise hd fun _ _ h => Disjoint.symm h
#align multiset.support_sum_eq Multiset.support_sum_eq

/- warning: finset.support_sum_eq -> Finset.support_sum_eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Finset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))), (Set.PairwiseDisjoint.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finset.partialOrder.{u1} ι) (Finset.orderBot.{u1} ι) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Finset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (Set.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (Set.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (Set.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) (Finset.Set.hasCoeT.{max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))) s) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))) -> (Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finset.sum.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s (id.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))) (Finset.sup.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.lattice.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.orderBot.{u1} ι) s (Finsupp.support.{u1, u2} ι M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))))))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u2} M] (s : Finset.{max u2 u1} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))), (Set.PairwiseDisjoint.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finset.partialOrder.{u1} ι) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) (Finset.toSet.{max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) s) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))) -> (Eq.{succ u1} (Finset.{u1} ι) (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)) (Finset.sum.{max u1 u2, max u1 u2} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Finsupp.addCommMonoid.{u1, u2} ι M _inst_2) s (id.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))))) (Finset.sup.{u1, max u1 u2} (Finset.{u1} ι) (Finsupp.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2))) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} ι) (Finset.instLatticeFinset.{u1} ι (fun (a : ι) (b : ι) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} ι) s (Finsupp.support.{u1, u2} ι M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_2)))))
Case conversion may be inaccurate. Consider using '#align finset.support_sum_eq Finset.support_sum_eqₓ'. -/
theorem Finset.support_sum_eq [AddCommMonoid M] (s : Finset (ι →₀ M))
    (hs : (s : Set (ι →₀ M)).PairwiseDisjoint Finsupp.support) :
    (s.Sum id).support = Finset.sup s Finsupp.support := by
  classical
    convert Multiset.support_sum_eq s.1 _
    · exact (Finset.sum_val _).symm
    · obtain ⟨l, hl, hn⟩ : ∃ l : List (ι →₀ M), l.toFinset = s ∧ l.Nodup :=
        by
        refine' ⟨s.to_list, _, Finset.nodup_toList _⟩
        simp
      subst hl
      rwa [List.toFinset_val, list.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise, ←
        List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hn]
      intro x y hxy
      exact symmetric_disjoint hxy
#align finset.support_sum_eq Finset.support_sum_eq

