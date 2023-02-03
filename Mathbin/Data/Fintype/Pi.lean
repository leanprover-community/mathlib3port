/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.pi
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Finset.Pi

/-!
# fintype instances for pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Finset

namespace Fintype

variable [DecidableEq α] [Fintype α] {δ : α → Type _}

#print Fintype.piFinset /-
/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map ⟨fun f a => f a (mem_univ a), fun _ _ => by simp [Function.funext_iff]⟩
#align fintype.pi_finset Fintype.piFinset
-/

#print Fintype.mem_piFinset /-
@[simp]
theorem mem_piFinset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a :=
  by
  constructor
  · simp only [pi_finset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ, exists_imp,
      mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
  · simp only [pi_finset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi]
    exact fun hf => ⟨fun a ha => f a, hf, rfl⟩
#align fintype.mem_pi_finset Fintype.mem_piFinset
-/

#print Fintype.coe_piFinset /-
@[simp]
theorem coe_piFinset (t : ∀ a, Finset (δ a)) :
    (piFinset t : Set (∀ a, δ a)) = Set.pi Set.univ fun a => t a :=
  Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_piFinset
#align fintype.coe_pi_finset Fintype.coe_piFinset
-/

#print Fintype.piFinset_subset /-
theorem piFinset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
    piFinset t₁ ⊆ piFinset t₂ := fun g hg => mem_piFinset.2 fun a => h a <| mem_piFinset.1 hg a
#align fintype.pi_finset_subset Fintype.piFinset_subset
-/

/- warning: fintype.pi_finset_empty -> Fintype.piFinset_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {δ : α -> Type.{u2}} [_inst_3 : Nonempty.{succ u1} α], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), δ a)) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (_x : α) => δ _x) (fun (_x : α) => EmptyCollection.emptyCollection.{u2} (Finset.{u2} (δ _x)) (Finset.hasEmptyc.{u2} (δ _x)))) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), δ a)) (Finset.hasEmptyc.{max u1 u2} (forall (a : α), δ a)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] {δ : α -> Type.{u1}} [_inst_3 : Nonempty.{succ u2} α], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (a : α), δ a)) (Fintype.piFinset.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (_x : α) => δ _x) (fun (_x : α) => EmptyCollection.emptyCollection.{u1} (Finset.{u1} (δ _x)) (Finset.instEmptyCollectionFinset.{u1} (δ _x)))) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u2 u1} (forall (a : α), δ a)) (Finset.instEmptyCollectionFinset.{max u2 u1} (forall (a : α), δ a)))
Case conversion may be inaccurate. Consider using '#align fintype.pi_finset_empty Fintype.piFinset_emptyₓ'. -/
@[simp]
theorem piFinset_empty [Nonempty α] : piFinset (fun _ => ∅ : ∀ i, Finset (δ i)) = ∅ :=
  eq_empty_of_forall_not_mem fun _ => by simp
#align fintype.pi_finset_empty Fintype.piFinset_empty

/- warning: fintype.pi_finset_singleton -> Fintype.piFinset_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {δ : α -> Type.{u2}} (f : forall (i : α), δ i), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), δ a)) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (i : α) => δ i) (fun (i : α) => Singleton.singleton.{u2, u2} (δ i) (Finset.{u2} (δ i)) (Finset.hasSingleton.{u2} (δ i)) (f i))) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (a : α), δ a) (Finset.{max u1 u2} (forall (a : α), δ a)) (Finset.hasSingleton.{max u1 u2} (forall (a : α), δ a)) f)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] {δ : α -> Type.{u1}} (f : forall (i : α), δ i), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (a : α), δ a)) (Fintype.piFinset.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (i : α) => δ i) (fun (i : α) => Singleton.singleton.{u1, u1} (δ i) (Finset.{u1} (δ i)) (Finset.instSingletonFinset.{u1} (δ i)) (f i))) (Singleton.singleton.{max u2 u1, max u2 u1} (forall (a : α), δ a) (Finset.{max u2 u1} (forall (a : α), δ a)) (Finset.instSingletonFinset.{max u2 u1} (forall (a : α), δ a)) f)
Case conversion may be inaccurate. Consider using '#align fintype.pi_finset_singleton Fintype.piFinset_singletonₓ'. -/
@[simp]
theorem piFinset_singleton (f : ∀ i, δ i) : piFinset (fun i => {f i} : ∀ i, Finset (δ i)) = {f} :=
  ext fun _ => by simp only [Function.funext_iff, Fintype.mem_piFinset, mem_singleton]
#align fintype.pi_finset_singleton Fintype.piFinset_singleton

#print Fintype.piFinset_subsingleton /-
theorem piFinset_subsingleton {f : ∀ i, Finset (δ i)} (hf : ∀ i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (∀ i, δ i)).Subsingleton := fun a ha b hb =>
  funext fun i => hf _ (mem_piFinset.1 ha _) (mem_piFinset.1 hb _)
#align fintype.pi_finset_subsingleton Fintype.piFinset_subsingleton
-/

/- warning: fintype.pi_finset_disjoint_of_disjoint -> Fintype.piFinset_disjoint_of_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {δ : α -> Type.{u2}} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)) {a : α}, (Disjoint.{u2} (Finset.{u2} (δ a)) (Finset.partialOrder.{u2} (δ a)) (Finset.orderBot.{u2} (δ a)) (t₁ a) (t₂ a)) -> (Disjoint.{max u1 u2} (Finset.{max u1 u2} (forall (a : α), δ a)) (Finset.partialOrder.{max u1 u2} (forall (a : α), δ a)) (Finset.orderBot.{max u1 u2} (forall (a : α), δ a)) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t₁) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] {δ : α -> Type.{u2}} (t₁ : forall (a : α), Finset.{u2} (δ a)) (t₂ : forall (a : α), Finset.{u2} (δ a)) {a : α}, (Disjoint.{u2} (Finset.{u2} (δ a)) (Finset.partialOrder.{u2} (δ a)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} (δ a)) (t₁ a) (t₂ a)) -> (Disjoint.{max u2 u1} (Finset.{max u1 u2} (forall (a : α), δ a)) (Finset.partialOrder.{max u1 u2} (forall (a : α), δ a)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u1 u2} (forall (a : α), δ a)) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t₁) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => δ a) t₂))
Case conversion may be inaccurate. Consider using '#align fintype.pi_finset_disjoint_of_disjoint Fintype.piFinset_disjoint_of_disjointₓ'. -/
theorem piFinset_disjoint_of_disjoint (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_piFinset.1 hf₁ a) (f₂ a) (mem_piFinset.1 hf₂ a)
      (congr_fun eq₁₂ a)
#align fintype.pi_finset_disjoint_of_disjoint Fintype.piFinset_disjoint_of_disjoint

end Fintype

/-! ### pi -/


#print Pi.fintype /-
/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.fintype {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by simp⟩
#align pi.fintype Pi.fintype
-/

/- warning: fintype.pi_finset_univ -> Fintype.piFinset_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : forall (a : α), Fintype.{u2} (β a)], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), β a)) (Fintype.piFinset.{u1, u2} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => β a) (fun (a : α) => Finset.univ.{u2} (β a) (_inst_3 a))) (Finset.univ.{max u1 u2} (forall (a : α), β a) (Pi.fintype.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => _inst_3 a)))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] [_inst_3 : forall (a : α), Fintype.{u1} (β a)], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (a : α), β a)) (Fintype.piFinset.{u2, u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => β a) (fun (a : α) => Finset.univ.{u1} (β a) (_inst_3 a))) (Finset.univ.{max u2 u1} (forall (a : α), β a) (Pi.fintype.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => _inst_3 a)))
Case conversion may be inaccurate. Consider using '#align fintype.pi_finset_univ Fintype.piFinset_univₓ'. -/
@[simp]
theorem Fintype.piFinset_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) =
      (Finset.univ : Finset (∀ a, β a)) :=
  rfl
#align fintype.pi_finset_univ Fintype.piFinset_univ

#print Function.Embedding.fintype /-
instance Function.Embedding.fintype {α β} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Fintype (α ↪ β) :=
  Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding α β)
#align function.embedding.fintype Function.Embedding.fintype
-/

/- warning: finset.univ_pi_univ -> Finset.univ_pi_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Fintype.{u1} α] [_inst_3 : forall (a : α), Fintype.{u2} (β a)], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) -> (β a))) (Finset.pi.{u1, u2} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) (Finset.univ.{u1} α _inst_2) (fun (a : α) => Finset.univ.{u2} (β a) (_inst_3 a))) (Finset.univ.{max u1 u2} (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) -> (β a)) (Pi.fintype.{u1, u2} α (fun (a : α) => (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) -> (β a)) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => pfunFintype.{u2} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a (Finset.univ.{u1} α _inst_2)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) => β a) (fun (hp : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.univ.{u1} α _inst_2)) => _inst_3 a))))
but is expected to have type
  forall {α : Type.{u2}} {β : α -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : Fintype.{u2} α] [_inst_3 : forall (a : α), Fintype.{u1} (β a)], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_2)) -> (β a))) (Finset.pi.{u2, u1} α (fun (a : α) => β a) (fun (a : α) (b : α) => _inst_1 a b) (Finset.univ.{u2} α _inst_2) (fun (a : α) => Finset.univ.{u1} (β a) (_inst_3 a))) (Finset.univ.{max u2 u1} (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_2)) -> (β a)) (Pi.fintype.{u2, u1} α (fun (a : α) => (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_2)) -> (β a)) (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (fun (a : α) => pfunFintype.{u1} (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_2)) (Finset.decidableMem.{u2} α (fun (a : α) (b : α) => _inst_1 a b) a (Finset.univ.{u2} α _inst_2)) (fun (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_2)) => β a) (fun (hp : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.univ.{u2} α _inst_2)) => (fun (a : α) => _inst_3 a) a))))
Case conversion may be inaccurate. Consider using '#align finset.univ_pi_univ Finset.univ_pi_univₓ'. -/
@[simp]
theorem Finset.univ_pi_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α]
    [∀ a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ :=
  by
  ext
  simp
#align finset.univ_pi_univ Finset.univ_pi_univ

