/-
Copyright (c) 2022 Violeta Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández

! This file was ported from Lean 3 source module data.finsupp.alist
! leanprover-community/mathlib commit d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Basic
import Mathbin.Data.List.Alist

/-!
# Connections between `finsupp` and `alist`

## Main definitions

* `finsupp.to_alist`
* `alist.lookup_finsupp`: converts an association list into a finitely supported function
  via `alist.lookup`, sending absent keys to zero.

-/


namespace Finsupp

variable {α M : Type _} [Zero M]

#print Finsupp.toAList /-
/-- Produce an association list for the finsupp over its support using choice. -/
@[simps]
noncomputable def toAList (f : α →₀ M) : AList fun x : α => M :=
  ⟨f.graph.toList.map Prod.toSigma,
    by
    rw [List.NodupKeys, List.keys, List.map_map, Prod.fst_comp_toSigma, List.nodup_map_iff_inj_on]
    · rintro ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c)
      rw [Finset.mem_toList, Finsupp.mem_graph_iff] at hb hc
      dsimp at hb hc
      rw [← hc.1, hb.1]
    · apply Finset.nodup_toList⟩
#align finsupp.to_alist Finsupp.toAList
-/

/- warning: finsupp.to_alist_keys_to_finset -> Finsupp.toAList_keys_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] (f : Finsupp.{u1, u2} α M _inst_1), Eq.{succ u1} (Finset.{u1} α) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (AList.keys.{u1, u2} α (fun (x : α) => M) (Finsupp.toAList.{u1, u2} α M _inst_1 f))) (Finsupp.support.{u1, u2} α M _inst_1 f)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] (f : Finsupp.{u2, u1} α M _inst_1), Eq.{succ u2} (Finset.{u2} α) (List.toFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (AList.keys.{u2, u1} α (fun (x : α) => M) (Finsupp.toAList.{u2, u1} α M _inst_1 f))) (Finsupp.support.{u2, u1} α M _inst_1 f)
Case conversion may be inaccurate. Consider using '#align finsupp.to_alist_keys_to_finset Finsupp.toAList_keys_toFinsetₓ'. -/
@[simp]
theorem toAList_keys_toFinset [DecidableEq α] (f : α →₀ M) : f.toAList.keys.toFinset = f.support :=
  by
  ext
  simp [to_alist, AList.mem_keys, AList.keys, List.keys]
#align finsupp.to_alist_keys_to_finset Finsupp.toAList_keys_toFinset

/- warning: finsupp.mem_to_alist -> Finsupp.mem_toAlist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] {f : Finsupp.{u1, u2} α M _inst_1} {x : α}, Iff (Membership.Mem.{u1, max u1 u2} α (AList.{u1, u2} α (fun (x : α) => M)) (AList.hasMem.{u1, u2} α (fun (x : α) => M)) x (Finsupp.toAList.{u1, u2} α M _inst_1 f)) (Ne.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) f x) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] {f : Finsupp.{u2, u1} α M _inst_1} {x : α}, Iff (Membership.mem.{u2, max u2 u1} α (AList.{u2, u1} α (fun (x : α) => M)) (AList.instMembershipAList.{u2, u1} α (fun (x : α) => M)) x (Finsupp.toAList.{u2, u1} α M _inst_1 f)) (Ne.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) f x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) x) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) x) _inst_1)))
Case conversion may be inaccurate. Consider using '#align finsupp.mem_to_alist Finsupp.mem_toAlistₓ'. -/
@[simp]
theorem mem_toAlist {f : α →₀ M} {x : α} : x ∈ f.toAList ↔ f x ≠ 0 := by
  classical rw [AList.mem_keys, ← List.mem_toFinset, to_alist_keys_to_finset, mem_support_iff]
#align finsupp.mem_to_alist Finsupp.mem_toAlist

end Finsupp

namespace AList

variable {α M : Type _} [Zero M]

open List

#print AList.lookupFinsupp /-
/-- Converts an association list into a finitely supported function via `alist.lookup`, sending
absent keys to zero. -/
noncomputable def lookupFinsupp (l : AList fun x : α => M) : α →₀ M
    where
  support := by
    haveI := Classical.decEq α <;> haveI := Classical.decEq M <;>
      exact (l.1.filterₓ fun x => Sigma.snd x ≠ 0).keys.toFinset
  toFun a :=
    haveI := Classical.decEq α
    (l.lookup a).getD 0
  mem_support_toFun a := by
    classical
      simp_rw [mem_to_finset, List.mem_keys, List.mem_filter, ← mem_lookup_iff]
      cases lookup a l <;> simp
#align alist.lookup_finsupp AList.lookupFinsupp
-/

/- warning: alist.lookup_finsupp_apply -> AList.lookupFinsupp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] (l : AList.{u1, u2} α (fun (x : α) => M)) (a : α), Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 l) a) (Option.getD.{u2} M (AList.lookup.{u1, u2} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a l) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] (l : AList.{u2, u1} α (fun (x : α) => M)) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 l) a) (Option.getD.{u1} M (AList.lookup.{u2, u1} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a l) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align alist.lookup_finsupp_apply AList.lookupFinsupp_applyₓ'. -/
@[simp]
theorem lookupFinsupp_apply [DecidableEq α] (l : AList fun x : α => M) (a : α) :
    l.lookupFinsupp a = (l.dlookup a).getD 0 := by convert rfl
#align alist.lookup_finsupp_apply AList.lookupFinsupp_apply

/- warning: alist.lookup_finsupp_support -> AList.lookupFinsupp_support is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] [_inst_3 : DecidableEq.{succ u2} M] (l : AList.{u1, u2} α (fun (x : α) => M)), Eq.{succ u1} (Finset.{u1} α) (Finsupp.support.{u1, u2} α M _inst_1 (AList.lookupFinsupp.{u1, u2} α M _inst_1 l)) (List.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) (List.keys.{u1, u2} α (fun (x : α) => M) (List.filterₓ.{max u1 u2} (Sigma.{u1, u2} α (fun (x : α) => M)) (fun (x : Sigma.{u1, u2} α (fun (x : α) => M)) => Ne.{succ u2} M (Sigma.snd.{u1, u2} α (fun (x : α) => M) x) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (fun (a : Sigma.{u1, u2} α (fun (x : α) => M)) => Ne.decidable.{succ u2} ((fun (x : α) => M) (Sigma.fst.{u1, u2} α (fun (x : α) => M) a)) (fun (a : M) (b : M) => _inst_3 a b) (Sigma.snd.{u1, u2} α (fun (x : α) => M) a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (AList.entries.{u1, u2} α (fun (x : α) => M) l))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] [_inst_3 : DecidableEq.{succ u1} M] (l : AList.{u2, u1} α (fun (x : α) => M)), Eq.{succ u2} (Finset.{u2} α) (Finsupp.support.{u2, u1} α M _inst_1 (AList.lookupFinsupp.{u2, u1} α M _inst_1 l)) (List.toFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b) (List.keys.{u2, u1} α (fun (x : α) => M) (List.filter.{max u1 u2} (Sigma.{u2, u1} α (fun (_x : α) => M)) (fun (a : Sigma.{u2, u1} α (fun (x : α) => M)) => Decidable.decide (Ne.{succ u1} M (Sigma.snd.{u2, u1} α (fun (_x : α) => M) a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (instDecidableNot (Eq.{succ u1} M (Sigma.snd.{u2, u1} α (fun (_x : α) => M) a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) (_inst_3 (Sigma.snd.{u2, u1} α (fun (_x : α) => M) a) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))))) (AList.entries.{u2, u1} α (fun (x : α) => M) l))))
Case conversion may be inaccurate. Consider using '#align alist.lookup_finsupp_support AList.lookupFinsupp_supportₓ'. -/
@[simp]
theorem lookupFinsupp_support [DecidableEq α] [DecidableEq M] (l : AList fun x : α => M) :
    l.lookupFinsupp.support = (l.1.filterₓ fun x => Sigma.snd x ≠ 0).keys.toFinset := by convert rfl
#align alist.lookup_finsupp_support AList.lookupFinsupp_support

/- warning: alist.lookup_finsupp_eq_iff_of_ne_zero -> AList.lookupFinsupp_eq_iff_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] {l : AList.{u1, u2} α (fun (x : α) => M)} {a : α} {x : M}, (Ne.{succ u2} M x (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) -> (Iff (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 l) a) x) (Membership.Mem.{u2, u2} M (Option.{u2} M) (Option.hasMem.{u2} M) x (AList.lookup.{u1, u2} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a l)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] {l : AList.{u2, u1} α (fun (x : α) => M)} {a : α} {x : M}, (Ne.{succ u1} M x (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1))) -> (Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 l) a) x) (Membership.mem.{u1, u1} M (Option.{u1} M) (Option.instMembershipOption.{u1} M) x (AList.lookup.{u2, u1} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a l)))
Case conversion may be inaccurate. Consider using '#align alist.lookup_finsupp_eq_iff_of_ne_zero AList.lookupFinsupp_eq_iff_of_ne_zeroₓ'. -/
theorem lookupFinsupp_eq_iff_of_ne_zero [DecidableEq α] {l : AList fun x : α => M} {a : α} {x : M}
    (hx : x ≠ 0) : l.lookupFinsupp a = x ↔ x ∈ l.dlookup a :=
  by
  rw [lookup_finsupp_apply]
  cases' lookup a l with m <;> simp [hx.symm]
#align alist.lookup_finsupp_eq_iff_of_ne_zero AList.lookupFinsupp_eq_iff_of_ne_zero

/- warning: alist.lookup_finsupp_eq_zero_iff -> AList.lookupFinsupp_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] {l : AList.{u1, u2} α (fun (x : α) => M)} {a : α}, Iff (Eq.{succ u2} M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (fun (_x : Finsupp.{u1, u2} α M _inst_1) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 l) a) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1)))) (Or (Not (Membership.Mem.{u1, max u1 u2} α (AList.{u1, u2} α (fun (x : α) => M)) (AList.hasMem.{u1, u2} α (fun (x : α) => M)) a l)) (Membership.Mem.{u2, u2} M (Option.{u2} M) (Option.hasMem.{u2} M) (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M _inst_1))) (AList.lookup.{u1, u2} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a l)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] {l : AList.{u2, u1} α (fun (x : α) => M)} {a : α}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) _x) (Finsupp.funLike.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 l) a) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) _inst_1))) (Or (Not (Membership.mem.{u2, max u2 u1} α (AList.{u2, u1} α (fun (x : α) => M)) (AList.instMembershipAList.{u2, u1} α (fun (x : α) => M)) a l)) (Membership.mem.{u1, u1} M (Option.{u1} M) (Option.instMembershipOption.{u1} M) (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M _inst_1)) (AList.lookup.{u2, u1} α (fun (x : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a l)))
Case conversion may be inaccurate. Consider using '#align alist.lookup_finsupp_eq_zero_iff AList.lookupFinsupp_eq_zero_iffₓ'. -/
theorem lookupFinsupp_eq_zero_iff [DecidableEq α] {l : AList fun x : α => M} {a : α} :
    l.lookupFinsupp a = 0 ↔ a ∉ l ∨ (0 : M) ∈ l.dlookup a :=
  by
  rw [lookup_finsupp_apply, ← lookup_eq_none]
  cases' lookup a l with m <;> simp
#align alist.lookup_finsupp_eq_zero_iff AList.lookupFinsupp_eq_zero_iff

/- warning: alist.empty_lookup_finsupp -> AList.empty_lookupFinsupp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M], Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 (EmptyCollection.emptyCollection.{max u1 u2} (AList.{u1, u2} α (fun (x : α) => M)) (AList.hasEmptyc.{u1, u2} α (fun (x : α) => M)))) (OfNat.ofNat.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (OfNat.mk.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) 0 (Zero.zero.{max u1 u2} (Finsupp.{u1, u2} α M _inst_1) (Finsupp.hasZero.{u1, u2} α M _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M], Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 (EmptyCollection.emptyCollection.{max u2 u1} (AList.{u2, u1} α (fun (x : α) => M)) (AList.instEmptyCollectionAList.{u2, u1} α (fun (x : α) => M)))) (OfNat.ofNat.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) 0 (Zero.toOfNat0.{max u2 u1} (Finsupp.{u2, u1} α M _inst_1) (Finsupp.instZeroFinsupp.{u2, u1} α M _inst_1)))
Case conversion may be inaccurate. Consider using '#align alist.empty_lookup_finsupp AList.empty_lookupFinsuppₓ'. -/
@[simp]
theorem empty_lookupFinsupp : lookupFinsupp (∅ : AList fun x : α => M) = 0 := by
  classical
    ext
    simp
#align alist.empty_lookup_finsupp AList.empty_lookupFinsupp

/- warning: alist.insert_lookup_finsupp -> AList.insert_lookupFinsupp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] [_inst_2 : DecidableEq.{succ u1} α] (l : AList.{u1, u2} α (fun (x : α) => M)) (a : α) (m : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 (AList.insert.{u1, u2} α (fun (a : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a m l)) (Finsupp.update.{u1, u2} α M _inst_1 (AList.lookupFinsupp.{u1, u2} α M _inst_1 l) a m)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] [_inst_2 : DecidableEq.{succ u2} α] (l : AList.{u2, u1} α (fun (x : α) => M)) (a : α) (m : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 (AList.insert.{u2, u1} α (fun (a : α) => M) (fun (a : α) (b : α) => _inst_2 a b) a m l)) (Finsupp.update.{u2, u1} α M _inst_1 (AList.lookupFinsupp.{u2, u1} α M _inst_1 l) a m)
Case conversion may be inaccurate. Consider using '#align alist.insert_lookup_finsupp AList.insert_lookupFinsuppₓ'. -/
@[simp]
theorem insert_lookupFinsupp [DecidableEq α] (l : AList fun x : α => M) (a : α) (m : M) :
    (l.insert a m).lookupFinsupp = l.lookupFinsupp.update a m :=
  by
  ext b
  by_cases h : b = a <;> simp [h]
#align alist.insert_lookup_finsupp AList.insert_lookupFinsupp

/- warning: alist.singleton_lookup_finsupp -> AList.singleton_lookupFinsupp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (a : α) (m : M), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 (AList.singleton.{u1, u2} α (fun (a : α) => M) a m)) (Finsupp.single.{u1, u2} α M _inst_1 a m)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (a : α) (m : M), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 (AList.singleton.{u2, u1} α (fun (a : α) => M) a m)) (Finsupp.single.{u2, u1} α M _inst_1 a m)
Case conversion may be inaccurate. Consider using '#align alist.singleton_lookup_finsupp AList.singleton_lookupFinsuppₓ'. -/
@[simp]
theorem singleton_lookupFinsupp (a : α) (m : M) :
    (singleton a m).lookupFinsupp = Finsupp.single a m := by classical simp [← AList.insert_empty]
#align alist.singleton_lookup_finsupp AList.singleton_lookupFinsupp

/- warning: finsupp.to_alist_lookup_finsupp -> Finsupp.toAList_lookupFinsupp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M] (f : Finsupp.{u1, u2} α M _inst_1), Eq.{max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1 (Finsupp.toAList.{u1, u2} α M _inst_1 f)) f
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M] (f : Finsupp.{u2, u1} α M _inst_1), Eq.{max (succ u2) (succ u1)} (Finsupp.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1 (Finsupp.toAList.{u2, u1} α M _inst_1 f)) f
Case conversion may be inaccurate. Consider using '#align finsupp.to_alist_lookup_finsupp Finsupp.toAList_lookupFinsuppₓ'. -/
@[simp]
theorem Finsupp.toAList_lookupFinsupp (f : α →₀ M) : f.toAList.lookupFinsupp = f :=
  by
  ext
  classical
    by_cases h : f a = 0
    · suffices f.to_alist.lookup a = none by simp [h, this]
      · simp [lookup_eq_none, h]
    · suffices f.to_alist.lookup a = some (f a) by simp [h, this]
      · apply mem_lookup_iff.2
        simpa using h
#align finsupp.to_alist_lookup_finsupp Finsupp.toAList_lookupFinsupp

/- warning: alist.lookup_finsupp_surjective -> AList.lookupFinsupp_surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : Zero.{u2} M], Function.Surjective.{succ (max u1 u2), max (succ u1) (succ u2)} (AList.{u1, u2} α (fun (x : α) => M)) (Finsupp.{u1, u2} α M _inst_1) (AList.lookupFinsupp.{u1, u2} α M _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : Zero.{u1} M], Function.Surjective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (AList.{u2, u1} α (fun (x : α) => M)) (Finsupp.{u2, u1} α M _inst_1) (AList.lookupFinsupp.{u2, u1} α M _inst_1)
Case conversion may be inaccurate. Consider using '#align alist.lookup_finsupp_surjective AList.lookupFinsupp_surjectiveₓ'. -/
theorem lookupFinsupp_surjective : Function.Surjective (@lookupFinsupp α M _) := fun f =>
  ⟨_, Finsupp.toAList_lookupFinsupp f⟩
#align alist.lookup_finsupp_surjective AList.lookupFinsupp_surjective

end AList

