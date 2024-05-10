/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Data.Rbtree.Init
import Logic.IsEmpty
import Tactic.Interactive

#align_import data.rbtree.basic from "leanprover-community/mathlib"@"5cb17dd1617d2dc55eb17777c3dcded3306fadb5"

universe u

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
unsafe def tactic.interactive.blast_disjs : tactic Unit :=
  sorry
#align tactic.interactive.blast_disjs tactic.interactive.blast_disjs

namespace Batteries.RBNode

variable {α : Type u}

open Color Nat

inductive Batteries.RBNode.IsNodeOf :
    Batteries.RBNode α → Batteries.RBNode α → α → Batteries.RBNode α → Prop
  | of_red (l v r) : is_node_of (Batteries.RBNode.node l v r) l v r
  | of_black (l v r) : is_node_of (black_node l v r) l v r
#align rbnode.is_node_of Batteries.RBNode.IsNodeOf

def Batteries.RBNode.Lift (lt : α → α → Prop) : Option α → Option α → Prop
  | some a, some b => lt a b
  | _, _ => True
#align rbnode.lift Batteries.RBNode.Lift

inductive Batteries.RBNode.IsSearchable (lt : α → α → Prop) :
    Batteries.RBNode α → Option α → Option α → Prop
  | leaf_s {lo hi} (hlt : Batteries.RBNode.Lift lt lo hi) : is_searchable Batteries.RBNode.nil lo hi
  |
  red_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) :
    is_searchable (Batteries.RBNode.node l v r) lo hi
  |
  black_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) :
    is_searchable (black_node l v r) lo hi
#align rbnode.is_searchable Batteries.RBNode.IsSearchable

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
unsafe def is_searchable_tactic : tactic Unit :=
  sorry
#align rbnode.is_searchable_tactic rbnode.is_searchable_tactic

open Batteries.RBNode (Mem)

open IsSearchable

section IsSearchableLemmas

variable {lt : α → α → Prop}

theorem Batteries.RBNode.lo_lt_hi {t : Batteries.RBNode α} {lt} [IsTrans α lt] :
    ∀ {lo hi}, Batteries.RBNode.IsSearchable lt t lo hi → Batteries.RBNode.Lift lt lo hi :=
  by
  induction t <;> intro lo hi hs
  case leaf => cases hs; assumption
  all_goals
    cases hs
    have h₁ := t_ih_lchild hs_hs₁
    have h₂ := t_ih_rchild hs_hs₂
    cases lo <;> cases hi <;> simp [lift] at *
    apply trans_of lt h₁ h₂
#align rbnode.lo_lt_hi Batteries.RBNode.lo_lt_hi

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableOfIsSearchableOfIncomp [IsStrictWeakOrder α lt] {t} :
    ∀ {lo hi hi'} (hc : ¬lt hi' hi ∧ ¬lt hi hi')
      (hs : Batteries.RBNode.IsSearchable lt t lo (some hi)),
      Batteries.RBNode.IsSearchable lt t lo (some hi') :=
  by
  classical
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo <;> simp_all [lift]; apply lt_of_lt_of_incomp; assumption; exact ⟨hc.2, hc.1⟩
  all_goals apply t_ih_rchild hc hs_hs₂
#align rbnode.is_searchable_of_is_searchable_of_incomp Batteries.RBNode.isSearchableOfIsSearchableOfIncomp

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableOfIncompOfIsSearchable [IsStrictWeakOrder α lt] {t} :
    ∀ {lo lo' hi} (hc : ¬lt lo' lo ∧ ¬lt lo lo')
      (hs : Batteries.RBNode.IsSearchable lt t (some lo) hi),
      Batteries.RBNode.IsSearchable lt t (some lo') hi :=
  by
  classical
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases hi <;> simp_all [lift]; apply lt_of_incomp_of_lt; assumption; assumption
  all_goals apply t_ih_lchild hc hs_hs₁
#align rbnode.is_searchable_of_incomp_of_is_searchable Batteries.RBNode.isSearchableOfIncompOfIsSearchable

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableSomeLowOfIsSearchableOfLt {t} [IsTrans α lt] :
    ∀ {lo hi lo'} (hlt : lt lo' lo) (hs : Batteries.RBNode.IsSearchable lt t (some lo) hi),
      Batteries.RBNode.IsSearchable lt t (some lo') hi :=
  by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases hi <;> simp_all [lift]; apply trans_of lt hlt; assumption
  all_goals apply t_ih_lchild hlt hs_hs₁
#align rbnode.is_searchable_some_low_of_is_searchable_of_lt Batteries.RBNode.isSearchableSomeLowOfIsSearchableOfLt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableNoneLowOfIsSearchableSomeLow {t} :
    ∀ {y hi} (hlt : Batteries.RBNode.IsSearchable lt t (some y) hi),
      Batteries.RBNode.IsSearchable lt t none hi :=
  by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · simp [lift]
  all_goals apply t_ih_lchild hlt_hs₁
#align rbnode.is_searchable_none_low_of_is_searchable_some_low Batteries.RBNode.isSearchableNoneLowOfIsSearchableSomeLow

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableSomeHighOfIsSearchableOfLt {t} [IsTrans α lt] :
    ∀ {lo hi hi'} (hlt : lt hi hi') (hs : Batteries.RBNode.IsSearchable lt t lo (some hi)),
      Batteries.RBNode.IsSearchable lt t lo (some hi') :=
  by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo <;> simp_all [lift]; apply trans_of lt; assumption; assumption
  all_goals apply t_ih_rchild hlt hs_hs₂
#align rbnode.is_searchable_some_high_of_is_searchable_of_lt Batteries.RBNode.isSearchableSomeHighOfIsSearchableOfLt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableNoneHighOfIsSearchableSomeHigh {t} :
    ∀ {lo y} (hlt : Batteries.RBNode.IsSearchable lt t lo (some y)),
      Batteries.RBNode.IsSearchable lt t lo none :=
  by
  induction t <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo <;> simp [lift]
  all_goals apply t_ih_rchild hlt_hs₂
#align rbnode.is_searchable_none_high_of_is_searchable_some_high Batteries.RBNode.isSearchableNoneHighOfIsSearchableSomeHigh

theorem Batteries.RBNode.range [IsStrictWeakOrder α lt] {t : Batteries.RBNode α} {x} :
    ∀ {lo hi},
      Batteries.RBNode.IsSearchable lt t lo hi →
        Batteries.RBNode.Mem lt x t →
          Batteries.RBNode.Lift lt lo (some x) ∧ Batteries.RBNode.Lift lt (some x) hi :=
  by
  classical
  induction t
  case leaf => simp [mem]
  all_goals
    -- red_node and black_node are identical
    intro lo hi h₁ h₂;
    cases h₁
    simp only [mem] at h₂
    have val_hi : lift lt (some t_val) hi := by apply lo_lt_hi; assumption
    have lo_val : lift lt lo (some t_val) := by apply lo_lt_hi; assumption
    cases_type* or.1
    · have h₃ : lift lt lo (some x) ∧ lift lt (some x) (some t_val) := by apply t_ih_lchild;
        assumption; assumption
      cases' h₃ with lo_x x_val
      constructor
      show lift lt lo (some x); · assumption
      show lift lt (some x) hi
      · cases' hi with hi <;> simp [lift] at *
        apply trans_of lt x_val val_hi
    · cases h₂
      cases' lo with lo <;> cases' hi with hi <;> simp [lift] at *
      · apply lt_of_incomp_of_lt _ val_hi; simp [*]
      · apply lt_of_lt_of_incomp lo_val; simp [*]
      constructor
      · apply lt_of_lt_of_incomp lo_val; simp [*]
      · apply lt_of_incomp_of_lt _ val_hi; simp [*]
    · have h₃ : lift lt (some t_val) (some x) ∧ lift lt (some x) hi := by apply t_ih_rchild;
        assumption; assumption
      cases' h₃ with val_x x_hi
      cases' lo with lo <;> cases' hi with hi <;> simp [lift] at *
      · assumption
      · apply trans_of lt lo_val val_x
      constructor
      · apply trans_of lt lo_val val_x
      · assumption
#align rbnode.range Batteries.RBNode.range

theorem Batteries.RBNode.ltOfMemLeft [IsStrictWeakOrder α lt] {y : α} {t l r : Batteries.RBNode α} :
    ∀ {lo hi},
      Batteries.RBNode.IsSearchable lt t lo hi →
        Batteries.RBNode.IsNodeOf t l y r → ∀ {x}, Batteries.RBNode.Mem lt x l → lt x y :=
  by
  intro _ _ hs hn x hm; cases hn <;> cases hs
  all_goals exact (range hs_hs₁ hm).2
#align rbnode.lt_of_mem_left Batteries.RBNode.ltOfMemLeft

theorem Batteries.RBNode.ltOfMemRight [IsStrictWeakOrder α lt] {y : α}
    {t l r : Batteries.RBNode α} :
    ∀ {lo hi},
      Batteries.RBNode.IsSearchable lt t lo hi →
        Batteries.RBNode.IsNodeOf t l y r → ∀ {z}, Batteries.RBNode.Mem lt z r → lt y z :=
  by
  intro _ _ hs hn z hm; cases hn <;> cases hs
  all_goals exact (range hs_hs₂ hm).1
#align rbnode.lt_of_mem_right Batteries.RBNode.ltOfMemRight

theorem Batteries.RBNode.ltOfMemLeftRight [IsStrictWeakOrder α lt] {y : α}
    {t l r : Batteries.RBNode α} :
    ∀ {lo hi},
      Batteries.RBNode.IsSearchable lt t lo hi →
        Batteries.RBNode.IsNodeOf t l y r →
          ∀ {x z}, Batteries.RBNode.Mem lt x l → Batteries.RBNode.Mem lt z r → lt x z :=
  by
  intro _ _ hs hn x z hm₁ hm₂; cases hn <;> cases hs
  all_goals
    have h₁ := range hs_hs₁ hm₁
    have h₂ := range hs_hs₂ hm₂
    exact trans_of lt h₁.2 h₂.1
#align rbnode.lt_of_mem_left_right Batteries.RBNode.ltOfMemLeftRight

end IsSearchableLemmas

inductive Batteries.RBNode.IsRedBlack : Batteries.RBNode α → RBColor → Nat → Prop
  | leaf_rb : is_red_black Batteries.RBNode.nil black 0
  |
  red_rb {v l r n} (rb_l : is_red_black l black n) (rb_r : is_red_black r black n) :
    is_red_black (Batteries.RBNode.node l v r) red n
  |
  black_rb {v l r n c₁ c₂} (rb_l : is_red_black l c₁ n) (rb_r : is_red_black r c₂ n) :
    is_red_black (black_node l v r) black (succ n)
#align rbnode.is_red_black Batteries.RBNode.IsRedBlack

open IsRedBlack

theorem Batteries.RBNode.depth_min :
    ∀ {c n} {t : Batteries.RBNode α},
      Batteries.RBNode.IsRedBlack t c n → n ≤ Batteries.RBNode.depth min t :=
  by
  intro c n' t h
  induction h
  case leaf_rb => exact le_refl _
  case red_rb =>
    simp [depth]
    have : min (depth min h_l) (depth min h_r) ≥ h_n := by apply le_min <;> assumption
    apply le_succ_of_le; assumption
  case black_rb =>
    simp [depth]
    apply succ_le_succ
    apply le_min <;> assumption
#align rbnode.depth_min Batteries.RBNode.depth_min

private def upper : RBColor → Nat → Nat
  | red, n => 2 * n + 1
  | black, n => 2 * n

private theorem upper_le : ∀ c n, upper c n ≤ 2 * n + 1
  | red, n => le_refl _
  | black, n => by apply le_succ

theorem Batteries.RBNode.depth_max' :
    ∀ {c n} {t : Batteries.RBNode α},
      Batteries.RBNode.IsRedBlack t c n → Batteries.RBNode.depth max t ≤ upper c n :=
  by
  intro c n' t h
  induction h
  case leaf_rb => simp [max, depth, upper, Nat.mul_zero]
  case
    red_rb =>
    suffices succ (max (depth max h_l) (depth max h_r)) ≤ 2 * h_n + 1 by simp_all [depth, upper]
    apply succ_le_succ
    apply max_le <;> assumption
  case
    black_rb =>
    have : depth max h_l ≤ 2 * h_n + 1 := le_trans h_ih_rb_l (upper_le _ _)
    have : depth max h_r ≤ 2 * h_n + 1 := le_trans h_ih_rb_r (upper_le _ _)
    suffices new : max (depth max h_l) (depth max h_r) + 1 ≤ 2 * h_n + 2 * 1
    · simp_all [depth, upper, succ_eq_add_one, Nat.left_distrib]
    apply succ_le_succ; apply max_le <;> assumption
#align rbnode.depth_max' Batteries.RBNode.depth_max'

theorem Batteries.RBNode.depth_max {c n} {t : Batteries.RBNode α}
    (h : Batteries.RBNode.IsRedBlack t c n) : Batteries.RBNode.depth max t ≤ 2 * n + 1 :=
  le_trans (Batteries.RBNode.depth_max' h) (upper_le _ _)
#align rbnode.depth_max Batteries.RBNode.depth_max

theorem Batteries.RBNode.balanced {c n} {t : Batteries.RBNode α}
    (h : Batteries.RBNode.IsRedBlack t c n) :
    Batteries.RBNode.depth max t ≤ 2 * Batteries.RBNode.depth min t + 1 :=
  by
  have : 2 * depth min t + 1 ≥ 2 * n + 1 := by apply succ_le_succ; apply Nat.mul_le_mul_left;
    apply depth_min h
  apply le_trans; apply depth_max h; apply this
#align rbnode.balanced Batteries.RBNode.balanced

end Batteries.RBNode

