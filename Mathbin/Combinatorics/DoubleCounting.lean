/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.double_counting
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Order

/-!
# Double countings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : finset α` and `t : finset β` by the minimum/maximum of edges over all `a ∈ s` times the
the size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartite_below`: `s.bipartite_below r b` are the elements of `s` below `b` wrt to `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartite_above`: `t.bipartite_above r a` are the elements of `t` above `a` wrt to `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.
-/


open Finset Function Relator

open BigOperators

variable {α β : Type _}

/-! ### Bipartite graph -/


namespace Finset

section Bipartite

variable (r : α → β → Prop) (s : Finset α) (t : Finset β) (a a' : α) (b b' : β)
  [DecidablePred (r a)] [∀ a, Decidable (r a b)] {m n : ℕ}

#print Finset.bipartiteBelow /-
/-- Elements of `s` which are "below" `b` according to relation `r`. -/
def bipartiteBelow : Finset α :=
  s.filter fun a => r a b
#align finset.bipartite_below Finset.bipartiteBelow
-/

#print Finset.bipartiteAbove /-
/-- Elements of `t` which are "above" `a` according to relation `r`. -/
def bipartiteAbove : Finset β :=
  t.filter (r a)
#align finset.bipartite_above Finset.bipartiteAbove
-/

#print Finset.bipartiteBelow_swap /-
theorem bipartiteBelow_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a :=
  rfl
#align finset.bipartite_below_swap Finset.bipartiteBelow_swap
-/

/- warning: finset.bipartite_above_swap -> Finset.bipartiteAbove_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (s : Finset.{u1} α) (b : β) [_inst_2 : forall (a : α), Decidable (r a b)], Eq.{succ u1} (Finset.{u1} α) (Finset.bipartiteAbove.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r) s b (fun (a : α) => _inst_2 a)) (Finset.bipartiteBelow.{u1, u2} α β r s b (fun (a : α) => _inst_2 a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) (s : Finset.{u2} α) (b : β) [_inst_2 : forall (a : α), Decidable (r a b)], Eq.{succ u2} (Finset.{u2} α) (Finset.bipartiteAbove.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r) s b (fun (a : α) => _inst_2 a)) (Finset.bipartiteBelow.{u2, u1} α β r s b (fun (a : α) => _inst_2 a))
Case conversion may be inaccurate. Consider using '#align finset.bipartite_above_swap Finset.bipartiteAbove_swapₓ'. -/
theorem bipartiteAbove_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b :=
  rfl
#align finset.bipartite_above_swap Finset.bipartiteAbove_swap

/- warning: finset.coe_bipartite_below -> Finset.coe_bipartiteBelow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (s : Finset.{u1} α) (b : β) [_inst_2 : forall (a : α), Decidable (r a b)], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) (Finset.bipartiteBelow.{u1, u2} α β r s b (fun (a : α) => _inst_2 a))) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (a : α) => r a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) (s : Finset.{u2} α) (b : β) [_inst_2 : forall (a : α), Decidable (r a b)], Eq.{succ u2} (Set.{u2} α) (Finset.toSet.{u2} α (Finset.bipartiteBelow.{u2, u1} α β r s b (fun (a : α) => _inst_2 a))) (setOf.{u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (r a b)))
Case conversion may be inaccurate. Consider using '#align finset.coe_bipartite_below Finset.coe_bipartiteBelowₓ'. -/
@[simp, norm_cast]
theorem coe_bipartiteBelow : (s.bipartiteBelow r b : Set α) = { a ∈ s | r a b } :=
  coe_filter _ _
#align finset.coe_bipartite_below Finset.coe_bipartiteBelow

#print Finset.coe_bipartiteAbove /-
@[simp, norm_cast]
theorem coe_bipartiteAbove : (t.bipartiteAbove r a : Set β) = { b ∈ t | r a b } :=
  coe_filter _ _
#align finset.coe_bipartite_above Finset.coe_bipartiteAbove
-/

variable {s t a a' b b'}

/- warning: finset.mem_bipartite_below -> Finset.mem_bipartiteBelow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) {s : Finset.{u1} α} {b : β} [_inst_2 : forall (a : α), Decidable (r a b)] {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finset.bipartiteBelow.{u1, u2} α β r s b (fun (a : α) => _inst_2 a))) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (r a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) {s : Finset.{u2} α} {b : β} [_inst_2 : forall (a : α), Decidable (r a b)] {a : α}, Iff (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finset.bipartiteBelow.{u2, u1} α β r s b (fun (a : α) => _inst_2 a))) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (r a b))
Case conversion may be inaccurate. Consider using '#align finset.mem_bipartite_below Finset.mem_bipartiteBelowₓ'. -/
@[simp]
theorem mem_bipartiteBelow {a : α} : a ∈ s.bipartiteBelow r b ↔ a ∈ s ∧ r a b :=
  mem_filter
#align finset.mem_bipartite_below Finset.mem_bipartiteBelow

#print Finset.mem_bipartiteAbove /-
@[simp]
theorem mem_bipartiteAbove {b : β} : b ∈ t.bipartiteAbove r a ↔ b ∈ t ∧ r a b :=
  mem_filter
#align finset.mem_bipartite_above Finset.mem_bipartiteAbove
-/

/- warning: finset.sum_card_bipartite_above_eq_sum_card_bipartite_below -> Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) {s : Finset.{u1} α} {t : Finset.{u2} β} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)], Eq.{1} Nat (Finset.sum.{0, u1} Nat α Nat.addCommMonoid s (fun (a : α) => Finset.card.{u2} β (Finset.bipartiteAbove.{u1, u2} α β r t a (fun (a_1 : β) => _inst_3 a a_1)))) (Finset.sum.{0, u2} Nat β Nat.addCommMonoid t (fun (b : β) => Finset.card.{u1} α (Finset.bipartiteBelow.{u1, u2} α β r s b (fun (a : α) => _inst_3 a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) {s : Finset.{u2} α} {t : Finset.{u1} β} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)], Eq.{1} Nat (Finset.sum.{0, u2} Nat α Nat.addCommMonoid s (fun (a : α) => Finset.card.{u1} β (Finset.bipartiteAbove.{u2, u1} α β r t a (fun (a_1 : β) => _inst_3 a a_1)))) (Finset.sum.{0, u1} Nat β Nat.addCommMonoid t (fun (b : β) => Finset.card.{u2} α (Finset.bipartiteBelow.{u2, u1} α β r s b (fun (a : α) => _inst_3 a b))))
Case conversion may be inaccurate. Consider using '#align finset.sum_card_bipartite_above_eq_sum_card_bipartite_below Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelowₓ'. -/
theorem sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow [∀ a b, Decidable (r a b)] :
    (∑ a in s, (t.bipartiteAbove r a).card) = ∑ b in t, (s.bipartiteBelow r b).card :=
  by
  simp_rw [card_eq_sum_ones, bipartite_above, bipartite_below, sum_filter]
  exact sum_comm
#align finset.sum_card_bipartite_above_eq_sum_card_bipartite_below Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow

/- warning: finset.card_mul_le_card_mul -> Finset.card_mul_le_card_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) {s : Finset.{u1} α} {t : Finset.{u2} β} {m : Nat} {n : Nat} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)], (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{0} Nat Nat.hasLe m (Finset.card.{u2} β (Finset.bipartiteAbove.{u1, u2} α β r t a (fun (a_1 : β) => _inst_3 a a_1))))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α (Finset.bipartiteBelow.{u1, u2} α β r s b (fun (a : α) => _inst_3 a b))) n)) -> (LE.le.{0} Nat Nat.hasLe (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) m) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u2} β t) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) {s : Finset.{u2} α} {t : Finset.{u1} β} {m : Nat} {n : Nat} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)], (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (LE.le.{0} Nat instLENat m (Finset.card.{u1} β (Finset.bipartiteAbove.{u2, u1} α β r t a (fun (a_1 : β) => _inst_3 a a_1))))) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α (Finset.bipartiteBelow.{u2, u1} α β r s b (fun (a : α) => _inst_3 a b))) n)) -> (LE.le.{0} Nat instLENat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α s) m) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} β t) n))
Case conversion may be inaccurate. Consider using '#align finset.card_mul_le_card_mul Finset.card_mul_le_card_mulₓ'. -/
/-- Double counting argument. Considering `r` as a bipartite graph, the LHS is a lower bound on the
number of edges while the RHS is an upper bound. -/
theorem card_mul_le_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, m ≤ (t.bipartiteAbove r a).card)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card ≤ n) : s.card * m ≤ t.card * n :=
  calc
    _ ≤ ∑ a in s, (t.bipartiteAbove r a).card := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (s.bipartiteBelow r b).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn
    
#align finset.card_mul_le_card_mul Finset.card_mul_le_card_mul

#print Finset.card_mul_le_card_mul' /-
theorem card_mul_le_card_mul' [∀ a b, Decidable (r a b)]
    (hn : ∀ b ∈ t, n ≤ (s.bipartiteBelow r b).card)
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card ≤ m) : t.card * n ≤ s.card * m :=
  card_mul_le_card_mul (swap r) hn hm
#align finset.card_mul_le_card_mul' Finset.card_mul_le_card_mul'
-/

/- warning: finset.card_mul_eq_card_mul -> Finset.card_mul_eq_card_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) {s : Finset.{u1} α} {t : Finset.{u2} β} {m : Nat} {n : Nat} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)], (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Eq.{1} Nat (Finset.card.{u2} β (Finset.bipartiteAbove.{u1, u2} α β r t a (fun (a_1 : β) => _inst_3 a a_1))) m)) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (Eq.{1} Nat (Finset.card.{u1} α (Finset.bipartiteBelow.{u1, u2} α β r s b (fun (a : α) => _inst_3 a b))) n)) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) m) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u2} β t) n))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) {s : Finset.{u2} α} {t : Finset.{u1} β} {m : Nat} {n : Nat} [_inst_3 : forall (a : α) (b : β), Decidable (r a b)], (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Eq.{1} Nat (Finset.card.{u1} β (Finset.bipartiteAbove.{u2, u1} α β r t a (fun (a_1 : β) => _inst_3 a a_1))) m)) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) -> (Eq.{1} Nat (Finset.card.{u2} α (Finset.bipartiteBelow.{u2, u1} α β r s b (fun (a : α) => _inst_3 a b))) n)) -> (Eq.{1} Nat (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α s) m) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u1} β t) n))
Case conversion may be inaccurate. Consider using '#align finset.card_mul_eq_card_mul Finset.card_mul_eq_card_mulₓ'. -/
theorem card_mul_eq_card_mul [∀ a b, Decidable (r a b)]
    (hm : ∀ a ∈ s, (t.bipartiteAbove r a).card = m)
    (hn : ∀ b ∈ t, (s.bipartiteBelow r b).card = n) : s.card * m = t.card * n :=
  (card_mul_le_card_mul _ (fun a ha => (hm a ha).ge) fun b hb => (hn b hb).le).antisymm <|
    card_mul_le_card_mul' _ (fun a ha => (hn a ha).ge) fun b hb => (hm b hb).le
#align finset.card_mul_eq_card_mul Finset.card_mul_eq_card_mul

/- warning: finset.card_le_card_of_forall_subsingleton -> Finset.card_le_card_of_forall_subsingleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) {s : Finset.{u1} α} {t : Finset.{u2} β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Exists.{succ u2} β (fun (b : β) => And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) (r a b)))) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (Set.Subsingleton.{u1} α (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (a : α) => r a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) {s : Finset.{u2} α} {t : Finset.{u1} β}, (forall (a : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Exists.{succ u1} β (fun (b : β) => And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) (r a b)))) -> (forall (b : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) -> (Set.Subsingleton.{u2} α (setOf.{u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (r a b))))) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α s) (Finset.card.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_of_forall_subsingleton Finset.card_le_card_of_forall_subsingletonₓ'. -/
theorem card_le_card_of_forall_subsingleton (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : s.card ≤ t.card := by
  classical simpa using
      card_mul_le_card_mul _
        (fun a h =>
          card_pos.2 <|
            (by
              rw [← coe_nonempty, coe_bipartite_above]
              exact hs _ h : (t.bipartite_above r a).Nonempty))
        fun b h =>
        card_le_one.2 <| by
          simp_rw [mem_bipartite_below]
          exact ht _ h
#align finset.card_le_card_of_forall_subsingleton Finset.card_le_card_of_forall_subsingleton

#print Finset.card_le_card_of_forall_subsingleton' /-
theorem card_le_card_of_forall_subsingleton' (ht : ∀ b ∈ t, ∃ a, a ∈ s ∧ r a b)
    (hs : ∀ a ∈ s, ({ b ∈ t | r a b } : Set β).Subsingleton) : t.card ≤ s.card :=
  card_le_card_of_forall_subsingleton (swap r) ht hs
#align finset.card_le_card_of_forall_subsingleton' Finset.card_le_card_of_forall_subsingleton'
-/

end Bipartite

end Finset

open Finset

namespace Fintype

variable [Fintype α] [Fintype β] {r : α → β → Prop}

/- warning: fintype.card_le_card_of_left_total_unique -> Fintype.card_le_card_of_leftTotal_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] {r : α -> β -> Prop}, (Relator.LeftTotal.{u1, u2} α β r) -> (Relator.LeftUnique.{u1, u2} α β r) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} α _inst_1) (Fintype.card.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] {r : α -> β -> Prop}, (Relator.LeftTotal.{u2, u1} α β r) -> (Relator.LeftUnique.{u2, u1} α β r) -> (LE.le.{0} Nat instLENat (Fintype.card.{u2} α _inst_1) (Fintype.card.{u1} β _inst_2))
Case conversion may be inaccurate. Consider using '#align fintype.card_le_card_of_left_total_unique Fintype.card_le_card_of_leftTotal_uniqueₓ'. -/
theorem card_le_card_of_leftTotal_unique (h₁ : LeftTotal r) (h₂ : LeftUnique r) :
    Fintype.card α ≤ Fintype.card β :=
  card_le_card_of_forall_subsingleton r (by simpa using h₁) fun b _ a₁ ha₁ a₂ ha₂ => h₂ ha₁.2 ha₂.2
#align fintype.card_le_card_of_left_total_unique Fintype.card_le_card_of_leftTotal_unique

/- warning: fintype.card_le_card_of_right_total_unique -> Fintype.card_le_card_of_rightTotal_unique is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : Fintype.{u2} β] {r : α -> β -> Prop}, (Relator.RightTotal.{u1, u2} α β r) -> (Relator.RightUnique.{u1, u2} α β r) -> (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u2} β _inst_2) (Fintype.card.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : Fintype.{u1} β] {r : α -> β -> Prop}, (Relator.RightTotal.{u2, u1} α β r) -> (Relator.RightUnique.{u2, u1} α β r) -> (LE.le.{0} Nat instLENat (Fintype.card.{u1} β _inst_2) (Fintype.card.{u2} α _inst_1))
Case conversion may be inaccurate. Consider using '#align fintype.card_le_card_of_right_total_unique Fintype.card_le_card_of_rightTotal_uniqueₓ'. -/
theorem card_le_card_of_rightTotal_unique (h₁ : RightTotal r) (h₂ : RightUnique r) :
    Fintype.card β ≤ Fintype.card α :=
  card_le_card_of_forall_subsingleton' r (by simpa using h₁) fun b _ a₁ ha₁ a₂ ha₂ => h₂ ha₁.2 ha₂.2
#align fintype.card_le_card_of_right_total_unique Fintype.card_le_card_of_rightTotal_unique

end Fintype

