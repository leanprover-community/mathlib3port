/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module order.well_founded_set
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Antichain
import Mathbin.Order.OrderIsoNat
import Mathbin.Order.WellFounded
import Mathbin.Tactic.Tfae

/-!
# Well-founded sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.
 * `set.partially_well_ordered_on s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
 * `set.is_pwo s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results
 * Higman's Lemma, `set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂`,
  shows that if `r` is partially well-ordered on `s`, then `list.sublist_forall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
 * `set.well_founded_on_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `set.is_wf.mono` shows that a subset of a well-founded subset is well-founded.
 * `set.is_wf.union` shows that the union of two well-founded subsets is well-founded.
 * `finset.is_wf` shows that all `finset`s are well-founded.

## TODO

Prove that `s` is partial well ordered iff it has no infinite descending chain or antichain.

## References
 * [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
 * [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/


variable {ι α β : Type _}

namespace Set

/-! ### Relations well-founded on sets -/


#print Set.WellFoundedOn /-
/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def WellFoundedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded fun a b : s => r a b
#align set.well_founded_on Set.WellFoundedOn
-/

#print Set.wellFoundedOn_empty /-
@[simp]
theorem wellFoundedOn_empty (r : α → α → Prop) : WellFoundedOn ∅ r :=
  wellFounded_of_isEmpty _
#align set.well_founded_on_empty Set.wellFoundedOn_empty
-/

section WellFoundedOn

variable {r r' : α → α → Prop}

section AnyRel

variable {s t : Set α} {x y : α}

#print Set.wellFoundedOn_iff /-
theorem wellFoundedOn_iff : s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
  by
  have f : RelEmbedding (fun (a : s) (b : s) => r a b) fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
    ⟨⟨coe, Subtype.coe_injective⟩, fun a b => by simp⟩
  refine' ⟨fun h => _, f.well_founded⟩
  rw [WellFounded.wellFounded_iff_has_min]
  intro t ht
  by_cases hst : (s ∩ t).Nonempty
  · rw [← Subtype.preimage_coe_nonempty] at hst
    rcases h.has_min (coe ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, ms⟩ => hm ⟨x, xs⟩ xt xm⟩
  · rcases ht with ⟨m, mt⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩
#align set.well_founded_on_iff Set.wellFoundedOn_iff
-/

namespace WellFoundedOn

#print Set.WellFoundedOn.induction /-
protected theorem induction (hs : s.WellFoundedOn r) (hx : x ∈ s) {P : α → Prop}
    (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x :=
  by
  let Q : s → Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine' WellFounded.induction hs ⟨x, hx⟩ _
  simpa only [Subtype.forall]
#align set.well_founded_on.induction Set.WellFoundedOn.induction
-/

#print Set.WellFoundedOn.mono /-
protected theorem mono (h : t.WellFoundedOn r') (hle : r ≤ r') (hst : s ⊆ t) : s.WellFoundedOn r :=
  by
  rw [well_founded_on_iff] at *
  refine' Subrelation.wf (fun x y xy => _) h
  exact ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩
#align set.well_founded_on.mono Set.WellFoundedOn.mono
-/

#print Set.WellFoundedOn.subset /-
theorem subset (h : t.WellFoundedOn r) (hst : s ⊆ t) : s.WellFoundedOn r :=
  h.mono le_rfl hst
#align set.well_founded_on.subset Set.WellFoundedOn.subset
-/

open Relation

#print Set.WellFoundedOn.acc_iff_wellFoundedOn /-
/-- `a` is accessible under the relation `r` iff `r` is well-founded on the downward transitive
  closure of `a` under `r` (including `a` or not). -/
theorem acc_iff_wellFoundedOn {α} {r : α → α → Prop} {a : α} :
    [Acc r a, { b | ReflTransGen r b a }.WellFoundedOn r,
        { b | TransGen r b a }.WellFoundedOn r].TFAE :=
  by
  tfae_have 1 → 2
  · refine' fun h => ⟨fun b => _⟩
    apply InvImage.accessible
    rw [← acc_transGen_iff] at h⊢
    obtain h' | h' := refl_trans_gen_iff_eq_or_trans_gen.1 b.2
    · rwa [h'] at h
    · exact h.inv h'
  tfae_have 2 → 3
  · exact fun h => h.Subset fun _ => trans_gen.to_refl
  tfae_have 3 → 1
  · refine' fun h =>
      Acc.intro _ fun b hb => (h.apply ⟨b, trans_gen.single hb⟩).of_fibration Subtype.val _
    exact fun ⟨c, hc⟩ d h => ⟨⟨d, trans_gen.head h hc⟩, h, rfl⟩
  tfae_finish
#align set.well_founded_on.acc_iff_well_founded_on Set.WellFoundedOn.acc_iff_wellFoundedOn
-/

end WellFoundedOn

end AnyRel

section IsStrictOrder

variable [IsStrictOrder α r] {s t : Set α}

#print Set.IsStrictOrder.subset /-
instance IsStrictOrder.subset : IsStrictOrder α fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s
    where
  to_isIrrefl := ⟨fun a con => irrefl_of r a Con.1⟩
  to_isTrans := ⟨fun a b c ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩
#align set.is_strict_order.subset Set.IsStrictOrder.subset
-/

/- warning: set.well_founded_on_iff_no_descending_seq -> Set.wellFoundedOn_iff_no_descending_seq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {s : Set.{u1} α}, Iff (Set.WellFoundedOn.{u1} α s r) (forall (f : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r), Not (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (coeFn.{succ u1, succ u1} (RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) (fun (_x : RelEmbedding.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) => Nat -> α) (RelEmbedding.hasCoeToFun.{0, u1} Nat α (GT.gt.{0} Nat Nat.hasLt) r) f n) s))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {s : Set.{u1} α}, Iff (Set.WellFoundedOn.{u1} α s r) (forall (f : RelEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.WellFoundedSet._hyg.1156 : Nat) (x._@.Mathlib.Order.WellFoundedSet._hyg.1158 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.WellFoundedSet._hyg.1156 x._@.Mathlib.Order.WellFoundedSet._hyg.1158) r), Not (forall (n : Nat), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => α) n) (Set.{u1} α) (Set.instMembershipSet.{u1} α) (FunLike.coe.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} Nat α) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => α) _x) (EmbeddingLike.toFunLike.{succ u1, 1, succ u1} (Function.Embedding.{1, succ u1} Nat α) Nat α (Function.instEmbeddingLikeEmbedding.{1, succ u1} Nat α)) (RelEmbedding.toEmbedding.{0, u1} Nat α (fun (x._@.Mathlib.Order.WellFoundedSet._hyg.1156 : Nat) (x._@.Mathlib.Order.WellFoundedSet._hyg.1158 : Nat) => GT.gt.{0} Nat instLTNat x._@.Mathlib.Order.WellFoundedSet._hyg.1156 x._@.Mathlib.Order.WellFoundedSet._hyg.1158) r f) n) s))
Case conversion may be inaccurate. Consider using '#align set.well_founded_on_iff_no_descending_seq Set.wellFoundedOn_iff_no_descending_seqₓ'. -/
theorem wellFoundedOn_iff_no_descending_seq :
    s.WellFoundedOn r ↔ ∀ f : ((· > ·) : ℕ → ℕ → Prop) ↪r r, ¬∀ n, f n ∈ s :=
  by
  simp only [well_founded_on_iff, RelEmbedding.wellFounded_iff_no_descending_seq, ← not_exists, ←
    not_nonempty_iff, not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : ∀ n, f n ∈ s := fun n => (hf.2 n.lt_succ_self).2.2
    refine' ⟨⟨f, _⟩, H⟩
    simpa only [H, and_true_iff] using @hf
  · rintro ⟨⟨f, hf⟩, hfs : ∀ n, f n ∈ s⟩
    refine' ⟨⟨f, _⟩⟩
    simpa only [hfs, and_true_iff] using @hf
#align set.well_founded_on_iff_no_descending_seq Set.wellFoundedOn_iff_no_descending_seq

/- warning: set.well_founded_on.union -> Set.WellFoundedOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.WellFoundedOn.{u1} α s r) -> (Set.WellFoundedOn.{u1} α t r) -> (Set.WellFoundedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.WellFoundedOn.{u1} α s r) -> (Set.WellFoundedOn.{u1} α t r) -> (Set.WellFoundedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r)
Case conversion may be inaccurate. Consider using '#align set.well_founded_on.union Set.WellFoundedOn.unionₓ'. -/
theorem WellFoundedOn.union (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r) :
    (s ∪ t).WellFoundedOn r :=
  by
  rw [well_founded_on_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts[hs (g.dual.lt_embedding.trans f) hg, ht (g.dual.lt_embedding.trans f) hg]
#align set.well_founded_on.union Set.WellFoundedOn.union

/- warning: set.well_founded_on_union -> Set.wellFoundedOn_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.WellFoundedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r) (And (Set.WellFoundedOn.{u1} α s r) (Set.WellFoundedOn.{u1} α t r))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u1} α r] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.WellFoundedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r) (And (Set.WellFoundedOn.{u1} α s r) (Set.WellFoundedOn.{u1} α t r))
Case conversion may be inaccurate. Consider using '#align set.well_founded_on_union Set.wellFoundedOn_unionₓ'. -/
@[simp]
theorem wellFoundedOn_union : (s ∪ t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r :=
  ⟨fun h => ⟨h.Subset <| subset_union_left _ _, h.Subset <| subset_union_right _ _⟩, fun h =>
    h.1.union h.2⟩
#align set.well_founded_on_union Set.wellFoundedOn_union

end IsStrictOrder

end WellFoundedOn

/-! ### Sets well-founded w.r.t. the strict inequality -/


section LT

variable [LT α] {s t : Set α}

#print Set.IsWf /-
/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def IsWf (s : Set α) : Prop :=
  WellFoundedOn s (· < ·)
#align set.is_wf Set.IsWf
-/

#print Set.isWf_empty /-
@[simp]
theorem isWf_empty : IsWf (∅ : Set α) :=
  wellFounded_of_isEmpty _
#align set.is_wf_empty Set.isWf_empty
-/

#print Set.isWf_univ_iff /-
theorem isWf_univ_iff : IsWf (univ : Set α) ↔ WellFounded ((· < ·) : α → α → Prop) := by
  simp [is_wf, well_founded_on_iff]
#align set.is_wf_univ_iff Set.isWf_univ_iff
-/

#print Set.IsWf.mono /-
theorem IsWf.mono (h : IsWf t) (st : s ⊆ t) : IsWf s :=
  h.Subset st
#align set.is_wf.mono Set.IsWf.mono
-/

end LT

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

/- warning: set.is_wf.union -> Set.IsWf.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) s) -> (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) t) -> (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) s) -> (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) t) -> (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.is_wf.union Set.IsWf.unionₓ'. -/
protected theorem IsWf.union (hs : IsWf s) (ht : IsWf t) : IsWf (s ∪ t) :=
  hs.union ht
#align set.is_wf.union Set.IsWf.union

/- warning: set.is_wf_union -> Set.isWf_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (And (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) s) (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (And (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) s) (Set.IsWf.{u1} α (Preorder.toLT.{u1} α _inst_1) t))
Case conversion may be inaccurate. Consider using '#align set.is_wf_union Set.isWf_unionₓ'. -/
@[simp]
theorem isWf_union : IsWf (s ∪ t) ↔ IsWf s ∧ IsWf t :=
  wellFoundedOn_union
#align set.is_wf_union Set.isWf_union

end Preorder

section Preorder

variable [Preorder α] {s t : Set α} {a : α}

#print Set.isWf_iff_no_descending_seq /-
theorem isWf_iff_no_descending_seq :
    IsWf s ↔ ∀ f : ℕ → α, StrictAnti f → ¬∀ n, f (OrderDual.toDual n) ∈ s :=
  wellFoundedOn_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.Injective⟩, fun a b => hf.lt_iff_lt⟩, fun H f =>
      H f fun _ _ => f.map_rel_iff.2⟩
#align set.is_wf_iff_no_descending_seq Set.isWf_iff_no_descending_seq
-/

end Preorder

/-!
### Partially well-ordered sets

A set is partially well-ordered by a relation `r` when any infinite sequence contains two elements
where the first is related to the second by `r`. Equivalently, any antichain (see `is_antichain`) is
finite, see `set.partially_well_ordered_on_iff_finite_antichains`.
-/


#print Set.PartiallyWellOrderedOn /-
/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def PartiallyWellOrderedOn (s : Set α) (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ m n : ℕ, m < n ∧ r (f m) (f n)
#align set.partially_well_ordered_on Set.PartiallyWellOrderedOn
-/

section PartiallyWellOrderedOn

variable {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α} {t : Set α} {a : α}

#print Set.PartiallyWellOrderedOn.mono /-
theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s ⊆ t) :
    s.PartiallyWellOrderedOn r := fun f hf => ht f fun n => h <| hf n
#align set.partially_well_ordered_on.mono Set.PartiallyWellOrderedOn.mono
-/

#print Set.partiallyWellOrderedOn_empty /-
@[simp]
theorem partiallyWellOrderedOn_empty (r : α → α → Prop) : PartiallyWellOrderedOn ∅ r := fun f hf =>
  (hf 0).elim
#align set.partially_well_ordered_on_empty Set.partiallyWellOrderedOn_empty
-/

/- warning: set.partially_well_ordered_on.union -> Set.PartiallyWellOrderedOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.PartiallyWellOrderedOn.{u1} α s r) -> (Set.PartiallyWellOrderedOn.{u1} α t r) -> (Set.PartiallyWellOrderedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.PartiallyWellOrderedOn.{u1} α s r) -> (Set.PartiallyWellOrderedOn.{u1} α t r) -> (Set.PartiallyWellOrderedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r)
Case conversion may be inaccurate. Consider using '#align set.partially_well_ordered_on.union Set.PartiallyWellOrderedOn.unionₓ'. -/
theorem PartiallyWellOrderedOn.union (hs : s.PartiallyWellOrderedOn r)
    (ht : t.PartiallyWellOrderedOn r) : (s ∪ t).PartiallyWellOrderedOn r :=
  by
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hgs | hgt⟩
  · rcases hs _ hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strict_mono hlt, hr⟩
  · rcases ht _ hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strict_mono hlt, hr⟩
#align set.partially_well_ordered_on.union Set.PartiallyWellOrderedOn.union

/- warning: set.partially_well_ordered_on_union -> Set.partiallyWellOrderedOn_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.PartiallyWellOrderedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r) (And (Set.PartiallyWellOrderedOn.{u1} α s r) (Set.PartiallyWellOrderedOn.{u1} α t r))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.PartiallyWellOrderedOn.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r) (And (Set.PartiallyWellOrderedOn.{u1} α s r) (Set.PartiallyWellOrderedOn.{u1} α t r))
Case conversion may be inaccurate. Consider using '#align set.partially_well_ordered_on_union Set.partiallyWellOrderedOn_unionₓ'. -/
@[simp]
theorem partiallyWellOrderedOn_union :
    (s ∪ t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r :=
  ⟨fun h => ⟨h.mono <| subset_union_left _ _, h.mono <| subset_union_right _ _⟩, fun h =>
    h.1.union h.2⟩
#align set.partially_well_ordered_on_union Set.partiallyWellOrderedOn_union

/- warning: set.partially_well_ordered_on.image_of_monotone_on -> Set.PartiallyWellOrderedOn.image_of_monotone_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {f : α -> β} {s : Set.{u1} α}, (Set.PartiallyWellOrderedOn.{u1} α s r) -> (forall (a₁ : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a₁ s) -> (forall (a₂ : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a₂ s) -> (r a₁ a₂) -> (r' (f a₁) (f a₂)))) -> (Set.PartiallyWellOrderedOn.{u2} β (Set.image.{u1, u2} α β f s) r')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {f : α -> β} {s : Set.{u2} α}, (Set.PartiallyWellOrderedOn.{u2} α s r) -> (forall (a₁ : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a₁ s) -> (forall (a₂ : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a₂ s) -> (r a₁ a₂) -> (r' (f a₁) (f a₂)))) -> (Set.PartiallyWellOrderedOn.{u1} β (Set.image.{u2, u1} α β f s) r')
Case conversion may be inaccurate. Consider using '#align set.partially_well_ordered_on.image_of_monotone_on Set.PartiallyWellOrderedOn.image_of_monotone_onₓ'. -/
theorem PartiallyWellOrderedOn.image_of_monotone_on (hs : s.PartiallyWellOrderedOn r)
    (hf : ∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a₂ → r' (f a₁) (f a₂)) : (f '' s).PartiallyWellOrderedOn r' :=
  by
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g'; exact funext HEq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩
#align set.partially_well_ordered_on.image_of_monotone_on Set.PartiallyWellOrderedOn.image_of_monotone_on

#print IsAntichain.finite_of_partiallyWellOrderedOn /-
theorem IsAntichain.finite_of_partiallyWellOrderedOn (ha : IsAntichain r s)
    (hp : s.PartiallyWellOrderedOn r) : s.Finite :=
  by
  refine' not_infinite.1 fun hi => _
  obtain ⟨m, n, hmn, h⟩ := hp (fun n => hi.nat_embedding _ n) fun n => (hi.nat_embedding _ n).2
  exact
    hmn.ne
      ((hi.nat_embedding _).Injective <|
        Subtype.val_injective <| ha.eq (hi.nat_embedding _ m).2 (hi.nat_embedding _ n).2 h)
#align is_antichain.finite_of_partially_well_ordered_on IsAntichain.finite_of_partiallyWellOrderedOn
-/

section IsRefl

variable [IsRefl α r]

#print Set.Finite.partiallyWellOrderedOn /-
protected theorem Finite.partiallyWellOrderedOn (hs : s.Finite) : s.PartiallyWellOrderedOn r :=
  by
  intro f hf
  obtain ⟨m, n, hmn, h⟩ := hs.exists_lt_map_eq_of_forall_mem hf
  exact ⟨m, n, hmn, h.subst <| refl (f m)⟩
#align set.finite.partially_well_ordered_on Set.Finite.partiallyWellOrderedOn
-/

#print IsAntichain.partiallyWellOrderedOn_iff /-
theorem IsAntichain.partiallyWellOrderedOn_iff (hs : IsAntichain r s) :
    s.PartiallyWellOrderedOn r ↔ s.Finite :=
  ⟨hs.finite_of_partiallyWellOrderedOn, Finite.partiallyWellOrderedOn⟩
#align is_antichain.partially_well_ordered_on_iff IsAntichain.partiallyWellOrderedOn_iff
-/

#print Set.partiallyWellOrderedOn_singleton /-
@[simp]
theorem partiallyWellOrderedOn_singleton (a : α) : PartiallyWellOrderedOn {a} r :=
  (finite_singleton a).PartiallyWellOrderedOn
#align set.partially_well_ordered_on_singleton Set.partiallyWellOrderedOn_singleton
-/

#print Set.partiallyWellOrderedOn_insert /-
@[simp]
theorem partiallyWellOrderedOn_insert :
    PartiallyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r := by
  simp only [← singleton_union, partially_well_ordered_on_union,
    partially_well_ordered_on_singleton, true_and_iff]
#align set.partially_well_ordered_on_insert Set.partiallyWellOrderedOn_insert
-/

#print Set.PartiallyWellOrderedOn.insert /-
protected theorem PartiallyWellOrderedOn.insert (h : PartiallyWellOrderedOn s r) (a : α) :
    PartiallyWellOrderedOn (insert a s) r :=
  partiallyWellOrderedOn_insert.2 h
#align set.partially_well_ordered_on.insert Set.PartiallyWellOrderedOn.insert
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print Set.partiallyWellOrderedOn_iff_finite_antichains /-
theorem partiallyWellOrderedOn_iff_finite_antichains [IsSymm α r] :
    s.PartiallyWellOrderedOn r ↔ ∀ (t) (_ : t ⊆ s), IsAntichain r t → t.Finite :=
  by
  refine' ⟨fun h t ht hrt => hrt.finite_of_partiallyWellOrderedOn (h.mono ht), _⟩
  rintro hs f hf
  by_contra' H
  refine' infinite_range_of_injective (fun m n hmn => _) (hs _ (range_subset_iff.2 hf) _)
  · obtain h | h | h := lt_trichotomy m n
    · refine' (H _ _ h _).elim
      rw [hmn]
      exact refl _
    · exact h
    · refine' (H _ _ h _).elim
      rw [hmn]
      exact refl _
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn
  obtain h | h := (ne_of_apply_ne _ hmn).lt_or_lt
  · exact H _ _ h
  · exact mt symm (H _ _ h)
#align set.partially_well_ordered_on_iff_finite_antichains Set.partiallyWellOrderedOn_iff_finite_antichains
-/

variable [IsTrans α r]

/- warning: set.partially_well_ordered_on.exists_monotone_subseq -> Set.PartiallyWellOrderedOn.exists_monotone_subseq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} [_inst_1 : IsRefl.{u1} α r] [_inst_2 : IsTrans.{u1} α r], (Set.PartiallyWellOrderedOn.{u1} α s r) -> (forall (f : Nat -> α), (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => forall (m : Nat) (n : Nat), (LE.le.{0} Nat Nat.hasLe m n) -> (r (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g m)) (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} [_inst_1 : IsRefl.{u1} α r] [_inst_2 : IsTrans.{u1} α r], (Set.PartiallyWellOrderedOn.{u1} α s r) -> (forall (f : Nat -> α), (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => forall (m : Nat) (n : Nat), (LE.le.{0} Nat instLENat m n) -> (r (f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) g) m)) (f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) g) n))))))
Case conversion may be inaccurate. Consider using '#align set.partially_well_ordered_on.exists_monotone_subseq Set.PartiallyWellOrderedOn.exists_monotone_subseqₓ'. -/
theorem PartiallyWellOrderedOn.exists_monotone_subseq (h : s.PartiallyWellOrderedOn r) (f : ℕ → α)
    (hf : ∀ n, f n ∈ s) : ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
  by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine' ⟨g, fun m n hle => _⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts[h1 m n hlt, refl_of r _]
  · exfalso
    obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) fun n => hf _
    exact h2 m n hlt hle
#align set.partially_well_ordered_on.exists_monotone_subseq Set.PartiallyWellOrderedOn.exists_monotone_subseq

/- warning: set.partially_well_ordered_on_iff_exists_monotone_subseq -> Set.partiallyWellOrderedOn_iff_exists_monotone_subseq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} [_inst_1 : IsRefl.{u1} α r] [_inst_2 : IsTrans.{u1} α r], Iff (Set.PartiallyWellOrderedOn.{u1} α s r) (forall (f : Nat -> α), (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => forall (m : Nat) (n : Nat), (LE.le.{0} Nat Nat.hasLe m n) -> (r (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g m)) (f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g n))))))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} {s : Set.{u1} α} [_inst_1 : IsRefl.{u1} α r] [_inst_2 : IsTrans.{u1} α r], Iff (Set.PartiallyWellOrderedOn.{u1} α s r) (forall (f : Nat -> α), (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => forall (m : Nat) (n : Nat), (LE.le.{0} Nat instLENat m n) -> (r (f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) g) m)) (f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) g) n))))))
Case conversion may be inaccurate. Consider using '#align set.partially_well_ordered_on_iff_exists_monotone_subseq Set.partiallyWellOrderedOn_iff_exists_monotone_subseqₓ'. -/
theorem partiallyWellOrderedOn_iff_exists_monotone_subseq :
    s.PartiallyWellOrderedOn r ↔
      ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
  by
  classical
    constructor <;> intro h f hf
    · exact h.exists_monotone_subseq f hf
    · obtain ⟨g, gmon⟩ := h f hf
      exact ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩
#align set.partially_well_ordered_on_iff_exists_monotone_subseq Set.partiallyWellOrderedOn_iff_exists_monotone_subseq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.PartiallyWellOrderedOn.prod /-
protected theorem PartiallyWellOrderedOn.prod {t : Set β} (hs : PartiallyWellOrderedOn s r)
    (ht : PartiallyWellOrderedOn t r') :
    PartiallyWellOrderedOn (s ×ˢ t) fun x y : α × β => r x.1 y.1 ∧ r' x.2 y.2 :=
  by
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq (Prod.fst ∘ f) fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht (Prod.snd ∘ f ∘ g₁) fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strict_mono hlt, h₁ _ _ hlt.le, hle⟩
#align set.partially_well_ordered_on.prod Set.PartiallyWellOrderedOn.prod
-/

end IsRefl

#print Set.PartiallyWellOrderedOn.wellFoundedOn /-
theorem PartiallyWellOrderedOn.wellFoundedOn [IsPreorder α r] (h : s.PartiallyWellOrderedOn r) :
    s.WellFoundedOn fun a b => r a b ∧ ¬r b a :=
  by
  letI : Preorder α :=
    { le := r
      le_refl := refl_of r
      le_trans := fun _ _ _ => trans_of r }
  change s.well_founded_on (· < ·); change s.partially_well_ordered_on (· ≤ ·) at h
  rw [well_founded_on_iff_no_descending_seq]
  intro f hf
  obtain ⟨m, n, hlt, hle⟩ := h f hf
  exact (f.map_rel_iff.2 hlt).not_le hle
#align set.partially_well_ordered_on.well_founded_on Set.PartiallyWellOrderedOn.wellFoundedOn
-/

end PartiallyWellOrderedOn

section IsPwo

variable [Preorder α] [Preorder β] {s t : Set α}

#print Set.IsPwo /-
/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def IsPwo (s : Set α) : Prop :=
  PartiallyWellOrderedOn s (· ≤ ·)
#align set.is_pwo Set.IsPwo
-/

#print Set.IsPwo.mono /-
theorem IsPwo.mono (ht : t.IsPwo) : s ⊆ t → s.IsPwo :=
  ht.mono
#align set.is_pwo.mono Set.IsPwo.mono
-/

/- warning: set.is_pwo.exists_monotone_subseq -> Set.IsPwo.exists_monotone_subseq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, (Set.IsPwo.{u1} α _inst_1 s) -> (forall (f : Nat -> α), (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) _inst_1 (Function.comp.{1, 1, succ u1} Nat Nat α f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, (Set.IsPwo.{u1} α _inst_1 s) -> (forall (f : Nat -> α), (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) _inst_1 (Function.comp.{1, 1, succ u1} Nat Nat α f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) g))))))
Case conversion may be inaccurate. Consider using '#align set.is_pwo.exists_monotone_subseq Set.IsPwo.exists_monotone_subseqₓ'. -/
theorem IsPwo.exists_monotone_subseq (h : s.IsPwo) (f : ℕ → α) (hf : ∀ n, f n ∈ s) :
    ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq f hf
#align set.is_pwo.exists_monotone_subseq Set.IsPwo.exists_monotone_subseq

/- warning: set.is_pwo_iff_exists_monotone_subseq -> Set.isPwo_iff_exists_monotone_subseq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, Iff (Set.IsPwo.{u1} α _inst_1 s) (forall (f : Nat -> α), (forall (n : Nat), Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (g : OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) => Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) _inst_1 (Function.comp.{1, 1, succ u1} Nat Nat α f (coeFn.{1, 1} (OrderEmbedding.{0, 0} Nat Nat Nat.hasLe Nat.hasLe) (fun (_x : RelEmbedding.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) => Nat -> Nat) (RelEmbedding.hasCoeToFun.{0, 0} Nat Nat (LE.le.{0} Nat Nat.hasLe) (LE.le.{0} Nat Nat.hasLe)) g)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α}, Iff (Set.IsPwo.{u1} α _inst_1 s) (forall (f : Nat -> α), (forall (n : Nat), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (f n) s) -> (Exists.{1} (OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) (fun (g : OrderEmbedding.{0, 0} Nat Nat instLENat instLENat) => Monotone.{0, u1} Nat α (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) _inst_1 (Function.comp.{1, 1, succ u1} Nat Nat α f (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat (fun (_x : Nat) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Nat) => Nat) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} Nat Nat) Nat Nat (Function.instEmbeddingLikeEmbedding.{1, 1} Nat Nat)) (RelEmbedding.toEmbedding.{0, 0} Nat Nat (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Nat) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Nat) => LE.le.{0} Nat instLENat x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) g))))))
Case conversion may be inaccurate. Consider using '#align set.is_pwo_iff_exists_monotone_subseq Set.isPwo_iff_exists_monotone_subseqₓ'. -/
theorem isPwo_iff_exists_monotone_subseq :
    s.IsPwo ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partiallyWellOrderedOn_iff_exists_monotone_subseq
#align set.is_pwo_iff_exists_monotone_subseq Set.isPwo_iff_exists_monotone_subseq

#print Set.IsPwo.isWf /-
protected theorem IsPwo.isWf (h : s.IsPwo) : s.IsWf := by
  simpa only [← lt_iff_le_not_le] using h.well_founded_on
#align set.is_pwo.is_wf Set.IsPwo.isWf
-/

/- warning: set.is_pwo.prod -> Set.IsPwo.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.IsPwo.{u1} α _inst_1 s) -> (Set.IsPwo.{u2} β _inst_2 t) -> (Set.IsPwo.{max u1 u2} (Prod.{u1, u2} α β) (Prod.preorder.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.IsPwo.{u1} α _inst_1 s) -> (Set.IsPwo.{u2} β _inst_2 t) -> (Set.IsPwo.{max u2 u1} (Prod.{u1, u2} α β) (Prod.instPreorderProd.{u1, u2} α β _inst_1 _inst_2) (Set.prod.{u1, u2} α β s t))
Case conversion may be inaccurate. Consider using '#align set.is_pwo.prod Set.IsPwo.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsPwo.prod {t : Set β} (hs : s.IsPwo) (ht : t.IsPwo) : IsPwo (s ×ˢ t) :=
  hs.Prod ht
#align set.is_pwo.prod Set.IsPwo.prod

/- warning: set.is_pwo.image_of_monotone_on -> Set.IsPwo.image_of_monotoneOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α}, (Set.IsPwo.{u1} α _inst_1 s) -> (forall {f : α -> β}, (MonotoneOn.{u1, u2} α β _inst_1 _inst_2 f s) -> (Set.IsPwo.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α}, (Set.IsPwo.{u2} α _inst_1 s) -> (forall {f : α -> β}, (MonotoneOn.{u2, u1} α β _inst_1 _inst_2 f s) -> (Set.IsPwo.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.is_pwo.image_of_monotone_on Set.IsPwo.image_of_monotoneOnₓ'. -/
theorem IsPwo.image_of_monotoneOn (hs : s.IsPwo) {f : α → β} (hf : MonotoneOn f s) :
    IsPwo (f '' s) :=
  hs.image_of_monotone_on hf
#align set.is_pwo.image_of_monotone_on Set.IsPwo.image_of_monotoneOn

/- warning: set.is_pwo.image_of_monotone -> Set.IsPwo.image_of_monotone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α}, (Set.IsPwo.{u1} α _inst_1 s) -> (forall {f : α -> β}, (Monotone.{u1, u2} α β _inst_1 _inst_2 f) -> (Set.IsPwo.{u2} β _inst_2 (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α}, (Set.IsPwo.{u2} α _inst_1 s) -> (forall {f : α -> β}, (Monotone.{u2, u1} α β _inst_1 _inst_2 f) -> (Set.IsPwo.{u1} β _inst_2 (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align set.is_pwo.image_of_monotone Set.IsPwo.image_of_monotoneₓ'. -/
theorem IsPwo.image_of_monotone (hs : s.IsPwo) {f : α → β} (hf : Monotone f) : IsPwo (f '' s) :=
  hs.image_of_monotone_on (hf.MonotoneOn _)
#align set.is_pwo.image_of_monotone Set.IsPwo.image_of_monotone

/- warning: set.is_pwo.union -> Set.IsPwo.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsPwo.{u1} α _inst_1 s) -> (Set.IsPwo.{u1} α _inst_1 t) -> (Set.IsPwo.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Set.IsPwo.{u1} α _inst_1 s) -> (Set.IsPwo.{u1} α _inst_1 t) -> (Set.IsPwo.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.is_pwo.union Set.IsPwo.unionₓ'. -/
protected theorem IsPwo.union (hs : IsPwo s) (ht : IsPwo t) : IsPwo (s ∪ t) :=
  hs.union ht
#align set.is_pwo.union Set.IsPwo.union

/- warning: set.is_pwo_union -> Set.isPwo_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.IsPwo.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (And (Set.IsPwo.{u1} α _inst_1 s) (Set.IsPwo.{u1} α _inst_1 t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.IsPwo.{u1} α _inst_1 (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (And (Set.IsPwo.{u1} α _inst_1 s) (Set.IsPwo.{u1} α _inst_1 t))
Case conversion may be inaccurate. Consider using '#align set.is_pwo_union Set.isPwo_unionₓ'. -/
@[simp]
theorem isPwo_union : IsPwo (s ∪ t) ↔ IsPwo s ∧ IsPwo t :=
  partiallyWellOrderedOn_union
#align set.is_pwo_union Set.isPwo_union

#print Set.Finite.isPwo /-
protected theorem Finite.isPwo (hs : s.Finite) : IsPwo s :=
  hs.PartiallyWellOrderedOn
#align set.finite.is_pwo Set.Finite.isPwo
-/

#print Set.isPwo_of_finite /-
@[simp]
theorem isPwo_of_finite [Finite α] : s.IsPwo :=
  s.toFinite.IsPwo
#align set.is_pwo_of_finite Set.isPwo_of_finite
-/

#print Set.isPwo_singleton /-
@[simp]
theorem isPwo_singleton (a : α) : IsPwo ({a} : Set α) :=
  (finite_singleton a).IsPwo
#align set.is_pwo_singleton Set.isPwo_singleton
-/

#print Set.isPwo_empty /-
@[simp]
theorem isPwo_empty : IsPwo (∅ : Set α) :=
  finite_empty.IsPwo
#align set.is_pwo_empty Set.isPwo_empty
-/

#print Set.Subsingleton.isPwo /-
protected theorem Subsingleton.isPwo (hs : s.Subsingleton) : IsPwo s :=
  hs.Finite.IsPwo
#align set.subsingleton.is_pwo Set.Subsingleton.isPwo
-/

#print Set.isPwo_insert /-
@[simp]
theorem isPwo_insert {a} : IsPwo (insert a s) ↔ IsPwo s := by
  simp only [← singleton_union, is_pwo_union, is_pwo_singleton, true_and_iff]
#align set.is_pwo_insert Set.isPwo_insert
-/

#print Set.IsPwo.insert /-
protected theorem IsPwo.insert (h : IsPwo s) (a : α) : IsPwo (insert a s) :=
  isPwo_insert.2 h
#align set.is_pwo.insert Set.IsPwo.insert
-/

#print Set.Finite.isWf /-
protected theorem Finite.isWf (hs : s.Finite) : IsWf s :=
  hs.IsPwo.IsWf
#align set.finite.is_wf Set.Finite.isWf
-/

#print Set.isWf_singleton /-
@[simp]
theorem isWf_singleton {a : α} : IsWf ({a} : Set α) :=
  (finite_singleton a).IsWf
#align set.is_wf_singleton Set.isWf_singleton
-/

#print Set.Subsingleton.isWf /-
protected theorem Subsingleton.isWf (hs : s.Subsingleton) : IsWf s :=
  hs.IsPwo.IsWf
#align set.subsingleton.is_wf Set.Subsingleton.isWf
-/

#print Set.isWf_insert /-
@[simp]
theorem isWf_insert {a} : IsWf (insert a s) ↔ IsWf s := by
  simp only [← singleton_union, is_wf_union, is_wf_singleton, true_and_iff]
#align set.is_wf_insert Set.isWf_insert
-/

#print Set.IsWf.insert /-
theorem IsWf.insert (h : IsWf s) (a : α) : IsWf (insert a s) :=
  isWf_insert.2 h
#align set.is_wf.insert Set.IsWf.insert
-/

end IsPwo

section WellFoundedOn

variable {r : α → α → Prop} [IsStrictOrder α r] {s : Set α} {a : α}

#print Set.Finite.wellFoundedOn /-
protected theorem Finite.wellFoundedOn (hs : s.Finite) : s.WellFoundedOn r :=
  letI := partialOrderOfSO r
  hs.is_wf
#align set.finite.well_founded_on Set.Finite.wellFoundedOn
-/

#print Set.wellFoundedOn_singleton /-
@[simp]
theorem wellFoundedOn_singleton : WellFoundedOn ({a} : Set α) r :=
  (finite_singleton a).WellFoundedOn
#align set.well_founded_on_singleton Set.wellFoundedOn_singleton
-/

#print Set.Subsingleton.wellFoundedOn /-
protected theorem Subsingleton.wellFoundedOn (hs : s.Subsingleton) : s.WellFoundedOn r :=
  hs.Finite.WellFoundedOn
#align set.subsingleton.well_founded_on Set.Subsingleton.wellFoundedOn
-/

#print Set.wellFoundedOn_insert /-
@[simp]
theorem wellFoundedOn_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r := by
  simp only [← singleton_union, well_founded_on_union, well_founded_on_singleton, true_and_iff]
#align set.well_founded_on_insert Set.wellFoundedOn_insert
-/

#print Set.WellFoundedOn.insert /-
theorem WellFoundedOn.insert (h : WellFoundedOn s r) (a : α) : WellFoundedOn (insert a s) r :=
  wellFoundedOn_insert.2 h
#align set.well_founded_on.insert Set.WellFoundedOn.insert
-/

end WellFoundedOn

section LinearOrder

variable [LinearOrder α] {s : Set α}

#print Set.IsWf.isPwo /-
protected theorem IsWf.isPwo (hs : s.IsWf) : s.IsPwo :=
  by
  intro f hf
  lift f to ℕ → s using hf
  have hrange : (range f).Nonempty := range_nonempty _
  rcases hs.has_min (range f) (range_nonempty _) with ⟨_, ⟨m, rfl⟩, hm⟩
  simp only [forall_range_iff, not_lt] at hm
  exact ⟨m, m + 1, lt_add_one m, hm _⟩
#align set.is_wf.is_pwo Set.IsWf.isPwo
-/

#print Set.isWf_iff_isPwo /-
/-- In a linear order, the predicates `set.is_wf` and `set.is_pwo` are equivalent. -/
theorem isWf_iff_isPwo : s.IsWf ↔ s.IsPwo :=
  ⟨IsWf.isPwo, IsPwo.isWf⟩
#align set.is_wf_iff_is_pwo Set.isWf_iff_isPwo
-/

end LinearOrder

end Set

namespace Finset

variable {r : α → α → Prop}

#print Finset.partiallyWellOrderedOn /-
@[simp]
protected theorem partiallyWellOrderedOn [IsRefl α r] (s : Finset α) :
    (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_toSet.PartiallyWellOrderedOn
#align finset.partially_well_ordered_on Finset.partiallyWellOrderedOn
-/

#print Finset.isPwo /-
@[simp]
protected theorem isPwo [Preorder α] (s : Finset α) : Set.IsPwo (↑s : Set α) :=
  s.PartiallyWellOrderedOn
#align finset.is_pwo Finset.isPwo
-/

#print Finset.isWf /-
@[simp]
protected theorem isWf [Preorder α] (s : Finset α) : Set.IsWf (↑s : Set α) :=
  s.finite_toSet.IsWf
#align finset.is_wf Finset.isWf
-/

#print Finset.wellFoundedOn /-
@[simp]
protected theorem wellFoundedOn [IsStrictOrder α r] (s : Finset α) :
    Set.WellFoundedOn (↑s : Set α) r :=
  letI := partialOrderOfSO r
  s.is_wf
#align finset.well_founded_on Finset.wellFoundedOn
-/

/- warning: finset.well_founded_on_sup -> Finset.wellFoundedOn_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u2} α r] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.WellFoundedOn.{u2} α (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s f) r) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Set.WellFoundedOn.{u2} α (f i) r))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} {r : α -> α -> Prop} [_inst_1 : IsStrictOrder.{u2} α r] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.WellFoundedOn.{u2} α (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeSup.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s f) r) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Set.WellFoundedOn.{u2} α (f i) r))
Case conversion may be inaccurate. Consider using '#align finset.well_founded_on_sup Finset.wellFoundedOn_supₓ'. -/
theorem wellFoundedOn_sup [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_bUnion, hs]
#align finset.well_founded_on_sup Finset.wellFoundedOn_sup

/- warning: finset.partially_well_ordered_on_sup -> Finset.partiallyWellOrderedOn_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {r : α -> α -> Prop} (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.PartiallyWellOrderedOn.{u2} α (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s f) r) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Set.PartiallyWellOrderedOn.{u2} α (f i) r))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {r : α -> α -> Prop} (s : Finset.{u2} ι) {f : ι -> (Set.{u1} α)}, Iff (Set.PartiallyWellOrderedOn.{u1} α (Finset.sup.{u1, u2} (Set.{u1} α) ι (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeSup.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (ConditionallyCompleteLattice.toLattice.{u1} (Set.{u1} α) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s f) r) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Set.PartiallyWellOrderedOn.{u1} α (f i) r))
Case conversion may be inaccurate. Consider using '#align finset.partially_well_ordered_on_sup Finset.partiallyWellOrderedOn_supₓ'. -/
theorem partiallyWellOrderedOn_sup (s : Finset ι) {f : ι → Set α} :
    (s.sup f).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r :=
  Finset.cons_induction_on s (by simp) fun a s ha hs => by simp [-sup_set_eq_bUnion, hs]
#align finset.partially_well_ordered_on_sup Finset.partiallyWellOrderedOn_sup

/- warning: finset.is_wf_sup -> Finset.isWf_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.IsWf.{u2} α (Preorder.toLT.{u2} α _inst_1) (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s f)) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Set.IsWf.{u2} α (Preorder.toLT.{u2} α _inst_1) (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.IsWf.{u2} α (Preorder.toLT.{u2} α _inst_1) (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeSup.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s f)) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Set.IsWf.{u2} α (Preorder.toLT.{u2} α _inst_1) (f i)))
Case conversion may be inaccurate. Consider using '#align finset.is_wf_sup Finset.isWf_supₓ'. -/
theorem isWf_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsWf ↔ ∀ i ∈ s, (f i).IsWf :=
  s.wellFoundedOn_sup
#align finset.is_wf_sup Finset.isWf_sup

/- warning: finset.is_pwo_sup -> Finset.isPwo_sup is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.IsPwo.{u2} α _inst_1 (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.completeBooleanAlgebra.{u2} α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} α) (Set.booleanAlgebra.{u2} α))) s f)) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Set.IsPwo.{u2} α _inst_1 (f i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : Preorder.{u2} α] (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.IsPwo.{u2} α _inst_1 (Finset.sup.{u2, u1} (Set.{u2} α) ι (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} α) (Preorder.toLE.{u2} (Set.{u2} α) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (SemilatticeSup.toPartialOrder.{u2} (Set.{u2} α) (Lattice.toSemilatticeSup.{u2} (Set.{u2} α) (ConditionallyCompleteLattice.toLattice.{u2} (Set.{u2} α) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))))))) (CompleteLattice.toBoundedOrder.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))))) s f)) (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Set.IsPwo.{u2} α _inst_1 (f i)))
Case conversion may be inaccurate. Consider using '#align finset.is_pwo_sup Finset.isPwo_supₓ'. -/
theorem isPwo_sup [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).IsPwo ↔ ∀ i ∈ s, (f i).IsPwo :=
  s.partiallyWellOrderedOn_sup
#align finset.is_pwo_sup Finset.isPwo_sup

#print Finset.wellFoundedOn_bUnion /-
@[simp]
theorem wellFoundedOn_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r := by
  simpa only [Finset.sup_eq_supᵢ] using s.well_founded_on_sup
#align finset.well_founded_on_bUnion Finset.wellFoundedOn_bUnion
-/

/- warning: finset.partially_well_ordered_on_bUnion -> Finset.partiallyWellOrderedOn_bUnion is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {r : α -> α -> Prop} (s : Finset.{u1} ι) {f : ι -> (Set.{u2} α)}, Iff (Set.PartiallyWellOrderedOn.{u2} α (Set.unionᵢ.{u2, succ u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, 0} α (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) => f i))) r) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Set.PartiallyWellOrderedOn.{u2} α (f i) r))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} {r : α -> α -> Prop} (s : Finset.{u2} ι) {f : ι -> (Set.{u1} α)}, Iff (Set.PartiallyWellOrderedOn.{u1} α (Set.unionᵢ.{u1, succ u2} α ι (fun (i : ι) => Set.unionᵢ.{u1, 0} α (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) => f i))) r) (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Set.PartiallyWellOrderedOn.{u1} α (f i) r))
Case conversion may be inaccurate. Consider using '#align finset.partially_well_ordered_on_bUnion Finset.partiallyWellOrderedOn_bUnionₓ'. -/
@[simp]
theorem partiallyWellOrderedOn_bUnion (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r := by
  simpa only [Finset.sup_eq_supᵢ] using s.partially_well_ordered_on_sup
#align finset.partially_well_ordered_on_bUnion Finset.partiallyWellOrderedOn_bUnion

#print Finset.isWf_bUnion /-
@[simp]
theorem isWf_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsWf ↔ ∀ i ∈ s, (f i).IsWf :=
  s.wellFoundedOn_bUnion
#align finset.is_wf_bUnion Finset.isWf_bUnion
-/

#print Finset.isPwo_bUnion /-
@[simp]
theorem isPwo_bUnion [Preorder α] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).IsPwo ↔ ∀ i ∈ s, (f i).IsPwo :=
  s.partiallyWellOrderedOn_bUnion
#align finset.is_pwo_bUnion Finset.isPwo_bUnion
-/

end Finset

namespace Set

section Preorder

variable [Preorder α] {s : Set α} {a : α}

#print Set.IsWf.min /-
/-- `is_wf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable def IsWf.min (hs : IsWf s) (hn : s.Nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)
#align set.is_wf.min Set.IsWf.min
-/

#print Set.IsWf.min_mem /-
theorem IsWf.min_mem (hs : IsWf s) (hn : s.Nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2
#align set.is_wf.min_mem Set.IsWf.min_mem
-/

#print Set.IsWf.not_lt_min /-
theorem IsWf.not_lt_min (hs : IsWf s) (hn : s.Nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))
#align set.is_wf.not_lt_min Set.IsWf.not_lt_min
-/

#print Set.isWf_min_singleton /-
@[simp]
theorem isWf_min_singleton (a) {hs : IsWf ({a} : Set α)} {hn : ({a} : Set α).Nonempty} :
    hs.min hn = a :=
  eq_of_mem_singleton (IsWf.min_mem hs hn)
#align set.is_wf_min_singleton Set.isWf_min_singleton
-/

end Preorder

section LinearOrder

variable [LinearOrder α] {s t : Set α} {a : α}

#print Set.IsWf.min_le /-
theorem IsWf.min_le (hs : s.IsWf) (hn : s.Nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_lt (hs.not_lt_min hn ha)
#align set.is_wf.min_le Set.IsWf.min_le
-/

#print Set.IsWf.le_min_iff /-
theorem IsWf.le_min_iff (hs : s.IsWf) (hn : s.Nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha b hb => le_trans ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩
#align set.is_wf.le_min_iff Set.IsWf.le_min_iff
-/

#print Set.IsWf.min_le_min_of_subset /-
theorem IsWf.min_le_min_of_subset {hs : s.IsWf} {hsn : s.Nonempty} {ht : t.IsWf} {htn : t.Nonempty}
    (hst : s ⊆ t) : ht.min htn ≤ hs.min hsn :=
  (IsWf.le_min_iff _ _).2 fun b hb => ht.min_le htn (hst hb)
#align set.is_wf.min_le_min_of_subset Set.IsWf.min_le_min_of_subset
-/

/- warning: set.is_wf.min_union -> Set.IsWf.min_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} (hs : Set.IsWf.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) s) (hsn : Set.Nonempty.{u1} α s) (ht : Set.IsWf.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) t) (htn : Set.Nonempty.{u1} α t), Eq.{succ u1} α (Set.IsWf.min.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Set.IsWf.union.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) s t hs ht) (Iff.mpr (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Or (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t)) (Set.union_nonempty.{u1} α s t) (Or.intro_left (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t) hsn))) (LinearOrder.min.{u1} α _inst_1 (Set.IsWf.min.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) s hs hsn) (Set.IsWf.min.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) t ht htn))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} (hs : Set.IsWf.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) s) (hsn : Set.Nonempty.{u1} α s) (ht : Set.IsWf.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) t) (htn : Set.Nonempty.{u1} α t), Eq.{succ u1} α (Set.IsWf.min.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Set.IsWf.union.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) s t hs ht) (Iff.mpr (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Or (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t)) (Set.union_nonempty.{u1} α s t) (Or.intro_left (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t) hsn))) (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1) (Set.IsWf.min.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) s hs hsn) (Set.IsWf.min.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) t ht htn))
Case conversion may be inaccurate. Consider using '#align set.is_wf.min_union Set.IsWf.min_unionₓ'. -/
theorem IsWf.min_union (hs : s.IsWf) (hsn : s.Nonempty) (ht : t.IsWf) (htn : t.Nonempty) :
    (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) = min (hs.min hsn) (ht.min htn) :=
  by
  refine'
    le_antisymm
      (le_min (is_wf.min_le_min_of_subset (subset_union_left _ _))
        (is_wf.min_le_min_of_subset (subset_union_right _ _)))
      _
  rw [min_le_iff]
  exact
    ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (Or.intro_left _ hsn)))).imp
      (hs.min_le _) (ht.min_le _)
#align set.is_wf.min_union Set.IsWf.min_union

end LinearOrder

end Set

open Set

namespace Set.PartiallyWellOrderedOn

variable {r : α → α → Prop}

#print Set.PartiallyWellOrderedOn.IsBadSeq /-
/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def IsBadSeq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  (∀ n, f n ∈ s) ∧ ∀ m n : ℕ, m < n → ¬r (f m) (f n)
#align set.partially_well_ordered_on.is_bad_seq Set.PartiallyWellOrderedOn.IsBadSeq
-/

#print Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq /-
theorem iff_forall_not_isBadSeq (r : α → α → Prop) (s : Set α) :
    s.PartiallyWellOrderedOn r ↔ ∀ f, ¬IsBadSeq r s f :=
  forall_congr' fun f => by simp [is_bad_seq]
#align set.partially_well_ordered_on.iff_forall_not_is_bad_seq Set.PartiallyWellOrderedOn.iff_forall_not_isBadSeq
-/

#print Set.PartiallyWellOrderedOn.IsMinBadSeq /-
/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def IsMinBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ g : ℕ → α, (∀ m : ℕ, m < n → f m = g m) → rk (g n) < rk (f n) → ¬IsBadSeq r s g
#align set.partially_well_ordered_on.is_min_bad_seq Set.PartiallyWellOrderedOn.IsMinBadSeq
-/

#print Set.PartiallyWellOrderedOn.minBadSeqOfBadSeq /-
/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
noncomputable def minBadSeqOfBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α)
    (hf : IsBadSeq r s f) :
    { g : ℕ → α // (∀ m : ℕ, m < n → f m = g m) ∧ IsBadSeq r s g ∧ IsMinBadSeq r rk s n g } := by
  classical
    have h : ∃ (k : ℕ)(g : ℕ → α), (∀ m, m < n → f m = g m) ∧ is_bad_seq r s g ∧ rk (g n) = k :=
      ⟨_, f, fun _ _ => rfl, hf, rfl⟩
    obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (Nat.find_spec h)
    refine' ⟨Classical.choose (Nat.find_spec h), h1, by convert h2, fun g hg1 hg2 con => _⟩
    refine' Nat.find_min h _ ⟨g, fun m mn => (h1 m mn).trans (hg1 m mn), by convert Con, rfl⟩
    rwa [← h3]
#align set.partially_well_ordered_on.min_bad_seq_of_bad_seq Set.PartiallyWellOrderedOn.minBadSeqOfBadSeq
-/

#print Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad /-
theorem exists_min_bad_of_exists_bad (r : α → α → Prop) (rk : α → ℕ) (s : Set α) :
    (∃ f, IsBadSeq r s f) → ∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f :=
  by
  rintro ⟨f0, hf0 : is_bad_seq r s f0⟩
  let fs : ∀ n : ℕ, { f : ℕ → α // is_bad_seq r s f ∧ is_min_bad_seq r rk s n f } :=
    by
    refine' Nat.rec _ _
    ·
      exact
        ⟨(min_bad_seq_of_bad_seq r rk s 0 f0 hf0).1, (min_bad_seq_of_bad_seq r rk s 0 f0 hf0).2.2⟩
    ·
      exact fun n fn =>
        ⟨(min_bad_seq_of_bad_seq r rk s (n + 1) fn.1 fn.2.1).1,
          (min_bad_seq_of_bad_seq r rk s (n + 1) fn.1 fn.2.1).2.2⟩
  have h : ∀ m n, m ≤ n → (fs m).1 m = (fs n).1 m :=
    by
    intro m n mn
    obtain ⟨k, rfl⟩ := exists_add_of_le mn
    clear mn
    induction' k with k ih
    · rfl
    rw [ih,
      (min_bad_seq_of_bad_seq r rk s (m + k).succ (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (Nat.lt_succ_iff.2 (Nat.add_le_add_left k.zero_le m))]
    rfl
  refine' ⟨fun n => (fs n).1 n, ⟨fun n => (fs n).2.1.1 n, fun m n mn => _⟩, fun n g hg1 hg2 => _⟩
  · dsimp
    rw [← Subtype.val_eq_coe, h m n (le_of_lt mn)]
    convert (fs n).2.1.2 m n mn
  · convert (fs n).2.2 g (fun m mn => Eq.trans _ (hg1 m mn)) (lt_of_lt_of_le hg2 le_rfl)
    rw [← h m n (le_of_lt mn)]
#align set.partially_well_ordered_on.exists_min_bad_of_exists_bad Set.PartiallyWellOrderedOn.exists_min_bad_of_exists_bad
-/

#print Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq /-
theorem iff_not_exists_isMinBadSeq (rk : α → ℕ) {s : Set α} :
    s.PartiallyWellOrderedOn r ↔ ¬∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f :=
  by
  rw [iff_forall_not_is_bad_seq, ← not_exists, not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
  rintro ⟨f, hf1, hf2⟩
  exact ⟨f, hf1⟩
#align set.partially_well_ordered_on.iff_not_exists_is_min_bad_seq Set.PartiallyWellOrderedOn.iff_not_exists_isMinBadSeq
-/

#print Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ /-
/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `list.sublist_forall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `list.sublist_forall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`.  -/
theorem partiallyWellOrderedOn_sublistForall₂ (r : α → α → Prop) [IsRefl α r] [IsTrans α r]
    {s : Set α} (h : s.PartiallyWellOrderedOn r) :
    { l : List α | ∀ x, x ∈ l → x ∈ s }.PartiallyWellOrderedOn (List.SublistForall₂ r) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨as, has⟩)
  · apply partially_well_ordered_on.mono (Finset.partiallyWellOrderedOn {List.nil})
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_singleton, List.eq_nil_iff_forall_not_mem]
      exact hl
    infer_instance
  haveI : Inhabited α := ⟨as⟩
  rw [iff_not_exists_is_min_bad_seq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : ∀ n, f n ≠ List.nil := fun n con =>
    hf1.2 n n.succ n.lt_succ_self (Con.symm ▸ List.SublistForall₂.nil)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq (List.headI ∘ f) _
  swap;
  · simp only [Set.range_subset_iff, Function.comp_apply]
    exact fun n => hf1.1 n _ (List.head!_mem_self (hnil n))
  have hf' :=
    hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0))))
      (fun m hm => (if_pos hm).symm) _
  swap;
  · simp only [if_neg (lt_irrefl (g 0)), tsub_self]
    rw [List.length_tail, ← Nat.pred_eq_sub_one]
    exact Nat.pred_lt fun con => hnil _ (List.length_eq_zero.1 Con)
  rw [is_bad_seq] at hf'
  push_neg  at hf'
  obtain ⟨m, n, mn, hmn⟩ := hf' _
  swap
  · rintro n x hx
    split_ifs  at hx with hn hn
    · exact hf1.1 _ _ hx
    · refine' hf1.1 _ _ (List.tail_subset _ hx)
  by_cases hn : n < g 0
  · apply hf1.2 m n mn
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
  · obtain ⟨n', rfl⟩ := exists_add_of_le (not_lt.1 hn)
    rw [if_neg hn, add_comm (g 0) n', add_tsub_cancel_right] at hmn
    split_ifs  at hmn with hm hm
    · apply hf1.2 m (g n') (lt_of_lt_of_le hm (g.monotone n'.zero_le))
      exact trans hmn (List.tail_sublistForall₂_self _)
    · rw [← tsub_lt_iff_left (le_of_not_lt hm)] at mn
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      rw [← List.cons_head!_tail (hnil (g (m - g 0))), ← List.cons_head!_tail (hnil (g n'))]
      exact List.SublistForall₂.cons (hg _ _ (le_of_lt mn)) hmn
#align set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂ Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂
-/

end Set.PartiallyWellOrderedOn

#print WellFounded.isWf /-
theorem WellFounded.isWf [LT α] (h : WellFounded ((· < ·) : α → α → Prop)) (s : Set α) : s.IsWf :=
  (Set.isWf_univ_iff.2 h).mono s.subset_univ
#align well_founded.is_wf WellFounded.isWf
-/

#print Pi.isPwo /-
/-- A version of **Dickson's lemma** any subset of functions `Π s : σ, α s` is partially well
ordered, when `σ` is a `fintype` and each `α s` is a linear well order.
This includes the classical case of Dickson's lemma that `ℕ ^ n` is a well partial order.
Some generalizations would be possible based on this proof, to include cases where the target is
partially well ordered, and also to consider the case of `set.partially_well_ordered_on` instead of
`set.is_pwo`. -/
theorem Pi.isPwo {α : ι → Type _} [∀ i, LinearOrder (α i)] [∀ i, IsWellOrder (α i) (· < ·)]
    [Finite ι] (s : Set (∀ i, α i)) : s.IsPwo :=
  by
  cases nonempty_fintype ι
  suffices
    ∀ s : Finset ι,
      ∀ f : ℕ → ∀ s, α s,
        ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x : ι) (hs : x ∈ s), (f ∘ g) a x ≤ (f ∘ g) b x
    by
    refine' is_pwo_iff_exists_monotone_subseq.2 fun f hf => _
    simpa only [Finset.mem_univ, true_imp_iff] using this Finset.univ f
  refine' Finset.cons_induction _ _
  · intro f
    exists RelEmbedding.refl (· ≤ ·)
    simp only [IsEmpty.forall_iff, imp_true_iff, forall_const, Finset.not_mem_empty]
  · intro x s hx ih f
    obtain ⟨g, hg⟩ :=
      (is_well_founded.wf.is_wf univ).IsPwo.exists_monotone_subseq (fun n => f n x) mem_univ
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    refine' ⟨g'.trans g, fun a b hab => (Finset.forall_mem_cons _ _).2 _⟩
    exact ⟨hg (OrderHomClass.mono g' hab), hg' hab⟩
#align pi.is_pwo Pi.isPwo
-/

