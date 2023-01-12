/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module order.zorn_atoms
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Zorn
import Mathbin.Order.Atoms

/-!
# Zorn lemma for (co)atoms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we use Zorn's lemma to prove that a partial order is atomic if every nonempty chain
`c`, `⊥ ∉ c`, has a lower bound not equal to `⊥`. We also prove the order dual version of this
statement.
-/


open Set

/- warning: is_coatomic.of_is_chain_bounded -> IsCoatomic.of_isChain_bounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], (forall (c : Set.{u1} α), (IsChain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) c) -> (Set.Nonempty.{u1} α c) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) c)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Ne.{succ u1} α x (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (fun (H : Ne.{succ u1} α x (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) c))))) -> (IsCoatomic.{u1} α _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], (forall (c : Set.{u1} α), (IsChain.{u1} α (fun (x._@.Mathlib.Order.ZornAtoms._hyg.26 : α) (x._@.Mathlib.Order.ZornAtoms._hyg.28 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Order.ZornAtoms._hyg.26 x._@.Mathlib.Order.ZornAtoms._hyg.28) c) -> (Set.Nonempty.{u1} α c) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) c)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Ne.{succ u1} α x (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (fun (H : Ne.{succ u1} α x (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (upperBounds.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) c))))) -> (IsCoatomic.{u1} α _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align is_coatomic.of_is_chain_bounded IsCoatomic.of_isChain_boundedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » «expr⊤»()) -/
/-- **Zorn's lemma**: A partial order is coatomic if every nonempty chain `c`, `⊤ ∉ c`, has an upper
bound not equal to `⊤`. -/
theorem IsCoatomic.of_isChain_bounded {α : Type _} [PartialOrder α] [OrderTop α]
    (h :
      ∀ c : Set α,
        IsChain (· ≤ ·) c → c.Nonempty → ⊤ ∉ c → ∃ (x : _)(_ : x ≠ ⊤), x ∈ upperBounds c) :
    IsCoatomic α := by
  refine' ⟨fun x => le_top.eq_or_lt.imp_right fun hx => _⟩
  rcases zorn_nonempty_partialOrder₀ (Ico x ⊤) (fun c hxc hc y hy => _) x (left_mem_Ico.2 hx) with
    ⟨y, ⟨hxy, hy⟩, -, hy'⟩
  · refine' ⟨y, ⟨hy.ne, fun z hyz => le_top.eq_or_lt.resolve_right fun hz => _⟩, hxy⟩
    exact hyz.ne' (hy' z ⟨hxy.trans hyz.le, hz⟩ hyz.le)
  · rcases h c hc ⟨y, hy⟩ fun h => (hxc h).2.Ne rfl with ⟨z, hz, hcz⟩
    exact ⟨z, ⟨le_trans (hxc hy).1 (hcz hy), hz.lt_top⟩, hcz⟩
#align is_coatomic.of_is_chain_bounded IsCoatomic.of_isChain_bounded

/- warning: is_atomic.of_is_chain_bounded -> IsAtomic.of_isChain_bounded is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], (forall (c : Set.{u1} α), (IsChain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) c) -> (Set.Nonempty.{u1} α c) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) c)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Ne.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (fun (H : Ne.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) c))))) -> (IsAtomic.{u1} α _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], (forall (c : Set.{u1} α), (IsChain.{u1} α (fun (x._@.Mathlib.Order.ZornAtoms._hyg.303 : α) (x._@.Mathlib.Order.ZornAtoms._hyg.305 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x._@.Mathlib.Order.ZornAtoms._hyg.303 x._@.Mathlib.Order.ZornAtoms._hyg.305) c) -> (Set.Nonempty.{u1} α c) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2)) c)) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Ne.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) (fun (H : Ne.{succ u1} α x (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) _inst_2))) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (lowerBounds.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) c))))) -> (IsAtomic.{u1} α _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align is_atomic.of_is_chain_bounded IsAtomic.of_isChain_boundedₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x «expr ≠ » «expr⊥»()) -/
/-- **Zorn's lemma**: A partial order is atomic if every nonempty chain `c`, `⊥ ∉ c`, has an lower
bound not equal to `⊥`. -/
theorem IsAtomic.of_isChain_bounded {α : Type _} [PartialOrder α] [OrderBot α]
    (h :
      ∀ c : Set α,
        IsChain (· ≤ ·) c → c.Nonempty → ⊥ ∉ c → ∃ (x : _)(_ : x ≠ ⊥), x ∈ lowerBounds c) :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp <| IsCoatomic.of_isChain_bounded fun c hc => h c hc.symm
#align is_atomic.of_is_chain_bounded IsAtomic.of_isChain_bounded

