/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.sum
! leanprover-community/mathlib commit 98e83c3d541c77cdb7da20d79611a780ff8e7d90
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Sum
import Mathbin.Logic.Embedding.Set

/-!
## Instances

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide the `fintype` instance for the sum of two fintypes.
-/


universe u v

variable {α β : Type _}

open Finset

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (Sum α β)
    where
  elems := univ.disjSum univ
  complete := by rintro (_ | _) <;> simp

/- warning: finset.univ_disj_sum_univ -> Finset.univ_disjSum_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Sum.{u1, u2} α β)) (Finset.disjSum.{u1, u2} α β (Finset.univ.{u1} α _inst_1) (Finset.univ.{u2} β _inst_2)) (Finset.univ.{max u1 u2} (Sum.{u1, u2} α β) (Sum.fintype.{u1, u2} α β _inst_1 _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Sum.{u2, u1} α β)) (Finset.disjSum.{u2, u1} α β (Finset.univ.{u2} α _inst_1) (Finset.univ.{u1} β _inst_2)) (Finset.univ.{max u2 u1} (Sum.{u2, u1} α β) (instFintypeSum.{u2, u1} α β _inst_1 _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.univ_disj_sum_univ Finset.univ_disjSum_univₓ'. -/
@[simp]
theorem Finset.univ_disjSum_univ {α β : Type _} [Fintype α] [Fintype β] :
    univ.disjSum univ = (univ : Finset (Sum α β)) :=
  rfl
#align finset.univ_disj_sum_univ Finset.univ_disjSum_univ

/- warning: fintype.card_sum -> Fintype.card_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β], Eq.{1} Nat (Fintype.card.{max u1 u2} (Sum.{u1, u2} α β) (Sum.fintype.{u1, u2} α β _inst_1 _inst_2)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β], Eq.{1} Nat (Fintype.card.{max u1 u2} (Sum.{u2, u1} α β) (instFintypeSum.{u2, u1} α β _inst_1 _inst_2)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_sum Fintype.card_sumₓ'. -/
@[simp]
theorem Fintype.card_sum [Fintype α] [Fintype β] :
    Fintype.card (Sum α β) = Fintype.card α + Fintype.card β :=
  card_disjSum _ _
#align fintype.card_sum Fintype.card_sum

#print fintypeOfFintypeNe /-
/-- If the subtype of all-but-one elements is a `fintype` then the type itself is a `fintype`. -/
def fintypeOfFintypeNe (a : α) (h : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofBijective (Sum.elim (coe : { b // b = a } → α) (coe : { b // b ≠ a } → α)) <| by
    classical exact (Equiv.sumCompl (· = a)).Bijective
#align fintype_of_fintype_ne fintypeOfFintypeNe
-/

/- warning: image_subtype_ne_univ_eq_image_erase -> image_subtype_ne_univ_eq_image_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (k : β) (b : α -> β), Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) β (fun (a : β) (b : β) => _inst_2 a b) (fun (i : Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) => b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) α (coeSubtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k))))) i)) (Finset.univ.{u1} (Subtype.{succ u1} α (fun (a : α) => Ne.{succ u2} β (b a) k)) (Subtype.fintype.{u1} α (fun (a : α) => Ne.{succ u2} β (b a) k) (fun (a : α) => Ne.decidable.{succ u2} β (fun (a : β) (b : β) => _inst_2 a b) (b a) k) _inst_1))) (Finset.erase.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) b (Finset.univ.{u1} α _inst_1)) k)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] (_inst_2 : β) (k : α -> β), Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} (Subtype.{succ u2} α (fun (a : α) => Ne.{succ u1} β (k a) _inst_2)) β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) (fun (i : Subtype.{succ u2} α (fun (a : α) => Ne.{succ u1} β (k a) _inst_2)) => k (Subtype.val.{succ u2} α (fun (a : α) => Ne.{succ u1} β (k a) _inst_2) i)) (Finset.univ.{u2} (Subtype.{succ u2} α (fun (a : α) => Ne.{succ u1} β (k a) _inst_2)) (Subtype.fintype.{u2} α (fun (a : α) => Ne.{succ u1} β (k a) _inst_2) (fun (a : α) => instDecidableNot (Eq.{succ u1} β (k a) _inst_2) (Classical.propDecidable (Eq.{succ u1} β (k a) _inst_2))) _inst_1))) (Finset.erase.{u1} β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) k (Finset.univ.{u2} α _inst_1)) _inst_2)
Case conversion may be inaccurate. Consider using '#align image_subtype_ne_univ_eq_image_erase image_subtype_ne_univ_eq_image_eraseₓ'. -/
theorem image_subtype_ne_univ_eq_image_erase [Fintype α] [DecidableEq β] (k : β) (b : α → β) :
    image (fun i : { a // b a ≠ k } => b ↑i) univ = (image b univ).eraseₓ k :=
  by
  apply subset_antisymm
  · rw [image_subset_iff]
    intro i _
    apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _))
  · intro i hi
    rw [mem_image]
    rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩
    subst ha
    exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩
#align image_subtype_ne_univ_eq_image_erase image_subtype_ne_univ_eq_image_erase

/- warning: image_subtype_univ_ssubset_image_univ -> image_subtype_univ_ssubset_image_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (k : β) (b : α -> β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) k (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) b (Finset.univ.{u1} α _inst_1))) -> (forall (p : β -> Prop) [_inst_3 : DecidablePred.{succ u2} β p], (Not (p k)) -> (HasSSubset.SSubset.{u2} (Finset.{u2} β) (Finset.hasSsubset.{u2} β) (Finset.image.{u1, u2} (Subtype.{succ u1} α (fun (a : α) => p (b a))) β (fun (a : β) (b : β) => _inst_2 a b) (fun (i : Subtype.{succ u1} α (fun (a : α) => p (b a))) => b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} α (fun (a : α) => p (b a))) α (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => p (b a))) α (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => p (b a))) α (coeBase.{succ u1, succ u1} (Subtype.{succ u1} α (fun (a : α) => p (b a))) α (coeSubtype.{succ u1} α (fun (a : α) => p (b a)))))) i)) (Finset.univ.{u1} (Subtype.{succ u1} α (fun (a : α) => p (b a))) (Subtype.fintype.{u1} α (fun (a : α) => p (b a)) (fun (a : α) => _inst_3 (b a)) _inst_1))) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) b (Finset.univ.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] (_inst_2 : β) (k : α -> β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) _inst_2 (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) k (Finset.univ.{u2} α _inst_1))) -> (forall (hk : β -> Prop) [p : DecidablePred.{succ u1} β hk], (Not (hk _inst_2)) -> (HasSSubset.SSubset.{u1} (Finset.{u1} β) (Finset.instHasSSubsetFinset.{u1} β) (Finset.image.{u2, u1} (Subtype.{succ u2} α (fun (a : α) => hk (k a))) β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) (fun (i : Subtype.{succ u2} α (fun (a : α) => hk (k a))) => k (Subtype.val.{succ u2} α (fun (a : α) => hk (k a)) i)) (Finset.univ.{u2} (Subtype.{succ u2} α (fun (a : α) => hk (k a))) (Subtype.fintype.{u2} α (fun (a : α) => hk (k a)) (fun (a : α) => p (k a)) _inst_1))) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) k (Finset.univ.{u2} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align image_subtype_univ_ssubset_image_univ image_subtype_univ_ssubset_image_univₓ'. -/
theorem image_subtype_univ_ssubset_image_univ [Fintype α] [DecidableEq β] (k : β) (b : α → β)
    (hk : k ∈ image b univ) (p : β → Prop) [DecidablePred p] (hp : ¬p k) :
    image (fun i : { a // p (b a) } => b ↑i) univ ⊂ image b univ :=
  by
  constructor
  · intro x hx
    rcases mem_image.1 hx with ⟨y, _, hy⟩
    exact hy ▸ mem_image_of_mem b (mem_univ y)
  · intro h
    rw [mem_image] at hk
    rcases hk with ⟨k', _, hk'⟩
    subst hk'
    have := h (mem_image_of_mem b (mem_univ k'))
    rw [mem_image] at this
    rcases this with ⟨j, hj, hj'⟩
    exact hp (hj' ▸ j.2)
#align image_subtype_univ_ssubset_image_univ image_subtype_univ_ssubset_image_univ

/- warning: finset.exists_equiv_extend_of_card_eq -> Finset.exists_equiv_extend_of_card_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] {t : Finset.{u2} β}, (Eq.{1} Nat (Fintype.card.{u1} α _inst_1) (Finset.card.{u2} β t)) -> (forall {s : Finset.{u1} α} {f : α -> β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) f s) t) -> (Set.InjOn.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) -> (Exists.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) (fun (g : Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) => forall (i : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) i s) -> (Eq.{succ u2} β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x t))))) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) (fun (_x : Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) => α -> (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) (Equiv.hasCoeToFun.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) g i)) (f i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] {_inst_2 : Finset.{u1} β}, (Eq.{1} Nat (Fintype.card.{u2} α _inst_1) (Finset.card.{u1} β _inst_2)) -> (forall {hαt : Finset.{u2} α} {s : α -> β}, (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => Classical.propDecidable (Eq.{succ u1} β a b)) s hαt) _inst_2) -> (Set.InjOn.{u2, u1} α β s (Finset.toSet.{u2} α hαt)) -> (Exists.{max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x _inst_2))) (fun (g : Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x _inst_2))) => forall (i : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) i hαt) -> (Eq.{succ u1} β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x _inst_2))) α (fun (a : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x _inst_2)) a) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x _inst_2))) g i)) (s i)))))
Case conversion may be inaccurate. Consider using '#align finset.exists_equiv_extend_of_card_eq Finset.exists_equiv_extend_of_card_eqₓ'. -/
/-- Any injection from a finset `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
theorem Finset.exists_equiv_extend_of_card_eq [Fintype α] [DecidableEq β] {t : Finset β}
    (hαt : Fintype.card α = t.card) {s : Finset α} {f : α → β} (hfst : s.image f ⊆ t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    induction' s using Finset.induction with a s has H generalizing f
    · obtain ⟨e⟩ : Nonempty (α ≃ ↥t) := by rwa [← Fintype.card_eq, Fintype.card_coe]
      use e
      simp
    have hfst' : Finset.image f s ⊆ t := (Finset.image_mono _ (s.subset_insert a)).trans hfst
    have hfs' : Set.InjOn f s := hfs.mono (s.subset_insert a)
    obtain ⟨g', hg'⟩ := H hfst' hfs'
    have hfat : f a ∈ t := hfst (mem_image_of_mem _ (s.mem_insert_self a))
    use g'.trans (Equiv.swap (⟨f a, hfat⟩ : t) (g' a))
    simp_rw [mem_insert]
    rintro i (rfl | hi)
    · simp
    rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne, hg' _ hi]
    ·
      exact
        ne_of_apply_ne Subtype.val
          (ne_of_eq_of_ne (hg' _ hi) <|
            hfs.ne (subset_insert _ _ hi) (mem_insert_self _ _) <| ne_of_mem_of_not_mem hi has)
    · exact g'.injective.ne (ne_of_mem_of_not_mem hi has)
#align finset.exists_equiv_extend_of_card_eq Finset.exists_equiv_extend_of_card_eq

/- warning: set.maps_to.exists_equiv_extend_of_card_eq -> Set.MapsTo.exists_equiv_extend_of_card_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] {t : Finset.{u2} β}, (Eq.{1} Nat (Fintype.card.{u1} α _inst_1) (Finset.card.{u2} β t)) -> (forall {s : Set.{u1} α} {f : α -> β}, (Set.MapsTo.{u1, u2} α β f s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t)) -> (Set.InjOn.{u1, u2} α β f s) -> (Exists.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) (fun (g : Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) => forall (i : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) i s) -> (Eq.{succ u2} β ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t) β (coeSubtype.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) x t))))) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) (fun (_x : Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) => α -> (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) (Equiv.hasCoeToFun.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} β) Type.{u2} (Finset.hasCoeToSort.{u2} β) t)) g i)) (f i)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] {t : Finset.{u1} β}, (Eq.{1} Nat (Fintype.card.{u2} α _inst_1) (Finset.card.{u1} β t)) -> (forall {s : Set.{u2} α} {f : α -> β}, (Set.MapsTo.{u2, u1} α β f s (Finset.toSet.{u1} β t)) -> (Set.InjOn.{u2, u1} α β f s) -> (Exists.{max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x t))) (fun (g : Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x t))) => forall (i : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) i s) -> (Eq.{succ u1} β (Subtype.val.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x t) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x t))) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x t)) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α (Subtype.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x t))) g i)) (f i)))))
Case conversion may be inaccurate. Consider using '#align set.maps_to.exists_equiv_extend_of_card_eq Set.MapsTo.exists_equiv_extend_of_card_eqₓ'. -/
/-- Any injection from a set `s` in a fintype `α` to a finset `t` of the same cardinality as `α`
can be extended to a bijection between `α` and `t`. -/
theorem Set.MapsTo.exists_equiv_extend_of_card_eq [Fintype α] {t : Finset β}
    (hαt : Fintype.card α = t.card) {s : Set α} {f : α → β} (hfst : s.MapsTo f t)
    (hfs : Set.InjOn f s) : ∃ g : α ≃ t, ∀ i ∈ s, (g i : β) = f i := by
  classical
    let s' : Finset α := s.to_finset
    have hfst' : s'.image f ⊆ t := by simpa [← Finset.coe_subset] using hfst
    have hfs' : Set.InjOn f s' := by simpa using hfs
    obtain ⟨g, hg⟩ := Finset.exists_equiv_extend_of_card_eq hαt hfst' hfs'
    refine' ⟨g, fun i hi => _⟩
    apply hg
    simpa using hi
#align set.maps_to.exists_equiv_extend_of_card_eq Set.MapsTo.exists_equiv_extend_of_card_eq

#print Fintype.card_subtype_or /-
theorem Fintype.card_subtype_or (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // q x }]
    [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } ≤ Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]
#align fintype.card_subtype_or Fintype.card_subtype_or
-/

#print Fintype.card_subtype_or_disjoint /-
theorem Fintype.card_subtype_or_disjoint (p q : α → Prop) (h : Disjoint p q) [Fintype { x // p x }]
    [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
    convert Fintype.card_congr (subtypeOrEquiv p q h)
    simp
#align fintype.card_subtype_or_disjoint Fintype.card_subtype_or_disjoint
-/

section

open Classical

#print infinite_sum /-
@[simp]
theorem infinite_sum : Infinite (Sum α β) ↔ Infinite α ∨ Infinite β :=
  by
  refine' ⟨fun H => _, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H; haveI := fintypeOfNotInfinite H.1; haveI := fintypeOfNotInfinite H.2
  exact Infinite.false
#align infinite_sum infinite_sum
-/

end

