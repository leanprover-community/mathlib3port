/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Data.Rbtree.Find

#align_import data.rbtree.insert from "leanprover-community/mathlib"@"4d4167104581a21259f7f448e1972a63a4546be7"

universe u v

attribute [local simp] Batteries.RBNode.Lift

namespace Batteries.RBNode

variable {α : Type u}

open Color

@[simp]
theorem Batteries.RBNode.balance1_eq₁ (l : Batteries.RBNode α) (x r₁ y r₂ v t) :
    Batteries.RBNode.balance1 (Batteries.RBNode.node l x r₁) y r₂ v t =
      Batteries.RBNode.node (black_node l x r₁) y (black_node r₂ v t) :=
  by cases r₂ <;> rfl
#align rbnode.balance1_eq₁ Batteries.RBNode.balance1_eq₁

@[simp]
theorem Batteries.RBNode.balance1_eq₂ (l₁ : Batteries.RBNode α) (y l₂ x r v t) :
    Batteries.RBNode.getColor l₁ ≠ red →
      Batteries.RBNode.balance1 l₁ y (Batteries.RBNode.node l₂ x r) v t =
        Batteries.RBNode.node (black_node l₁ y l₂) x (black_node r v t) :=
  by cases l₁ <;> simp [get_color, balance1, false_imp_iff]
#align rbnode.balance1_eq₂ Batteries.RBNode.balance1_eq₂

@[simp]
theorem Batteries.RBNode.balance1_eq₃ (l : Batteries.RBNode α) (y r v t) :
    Batteries.RBNode.getColor l ≠ red →
      Batteries.RBNode.getColor r ≠ red →
        Batteries.RBNode.balance1 l y r v t = black_node (Batteries.RBNode.node l y r) v t :=
  by cases l <;> cases r <;> simp [get_color, balance1, false_imp_iff]
#align rbnode.balance1_eq₃ Batteries.RBNode.balance1_eq₃

@[simp]
theorem Batteries.RBNode.balance2_eq₁ (l : Batteries.RBNode α) (x₁ r₁ y r₂ v t) :
    Batteries.RBNode.balance2 (Batteries.RBNode.node l x₁ r₁) y r₂ v t =
      Batteries.RBNode.node (black_node t v l) x₁ (black_node r₁ y r₂) :=
  by cases r₂ <;> rfl
#align rbnode.balance2_eq₁ Batteries.RBNode.balance2_eq₁

@[simp]
theorem Batteries.RBNode.balance2_eq₂ (l₁ : Batteries.RBNode α) (y l₂ x₂ r₂ v t) :
    Batteries.RBNode.getColor l₁ ≠ red →
      Batteries.RBNode.balance2 l₁ y (Batteries.RBNode.node l₂ x₂ r₂) v t =
        Batteries.RBNode.node (black_node t v l₁) y (black_node l₂ x₂ r₂) :=
  by cases l₁ <;> simp [get_color, balance2, false_imp_iff]
#align rbnode.balance2_eq₂ Batteries.RBNode.balance2_eq₂

@[simp]
theorem Batteries.RBNode.balance2_eq₃ (l : Batteries.RBNode α) (y r v t) :
    Batteries.RBNode.getColor l ≠ red →
      Batteries.RBNode.getColor r ≠ red →
        Batteries.RBNode.balance2 l y r v t = black_node t v (Batteries.RBNode.node l y r) :=
  by cases l <;> cases r <;> simp [get_color, balance2, false_imp_iff]
#align rbnode.balance2_eq₃ Batteries.RBNode.balance2_eq₃

-- We can use the same induction principle for balance1 and balance2
theorem Batteries.RBNode.Balance.cases {p : Batteries.RBNode α → α → Batteries.RBNode α → Prop}
    (l y r) (red_left : ∀ l x r₁ y r₂, p (Batteries.RBNode.node l x r₁) y r₂)
    (red_right :
      ∀ l₁ y l₂ x r, Batteries.RBNode.getColor l₁ ≠ red → p l₁ y (Batteries.RBNode.node l₂ x r))
    (other :
      ∀ l y r, Batteries.RBNode.getColor l ≠ red → Batteries.RBNode.getColor r ≠ red → p l y r) :
    p l y r := by
  cases l <;> cases r
  any_goals apply red_left
  any_goals apply red_right <;> simp [get_color] <;> contradiction <;> done
  any_goals apply other <;> simp [get_color] <;> contradiction <;> done
#align rbnode.balance.cases Batteries.RBNode.Balance.cases

theorem Batteries.RBNode.balance1_ne_nil (l : Batteries.RBNode α) (x r v t) :
    Batteries.RBNode.balance1 l x r v t ≠ Batteries.RBNode.nil := by
  apply balance.cases l x r <;> intros <;> simp [*] <;> contradiction
#align rbnode.balance1_ne_leaf Batteries.RBNode.balance1_ne_nil

theorem Batteries.RBNode.balance1Node_ne_nil {s : Batteries.RBNode α} (a : α)
    (t : Batteries.RBNode α) :
    s ≠ Batteries.RBNode.nil → Batteries.RBNode.balance1Node s a t ≠ Batteries.RBNode.nil :=
  by
  intro h; cases s
  · contradiction
  all_goals simp [balance1_node]; apply balance1_ne_leaf
#align rbnode.balance1_node_ne_leaf Batteries.RBNode.balance1Node_ne_nil

theorem Batteries.RBNode.balance2_ne_nil (l : Batteries.RBNode α) (x r v t) :
    Batteries.RBNode.balance2 l x r v t ≠ Batteries.RBNode.nil := by
  apply balance.cases l x r <;> intros <;> simp [*] <;> contradiction
#align rbnode.balance2_ne_leaf Batteries.RBNode.balance2_ne_nil

theorem Batteries.RBNode.balance2Node_ne_nil {s : Batteries.RBNode α} (a : α)
    (t : Batteries.RBNode α) :
    s ≠ Batteries.RBNode.nil → Batteries.RBNode.balance2Node s a t ≠ Batteries.RBNode.nil :=
  by
  intro h; cases s
  · contradiction
  all_goals simp [balance2_node]; apply balance2_ne_leaf
#align rbnode.balance2_node_ne_leaf Batteries.RBNode.balance2Node_ne_nil

variable (lt : α → α → Prop)

@[elab_as_elim]
theorem Batteries.RBNode.ins.induction [DecidableRel lt] {p : Batteries.RBNode α → Prop} (t x)
    (is_leaf : p Batteries.RBNode.nil)
    (is_red_lt :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.lt) (ih : p a), p (Batteries.RBNode.node a y b))
    (is_red_eq : ∀ (a y b) (hc : cmpUsing lt x y = Ordering.eq), p (Batteries.RBNode.node a y b))
    (is_red_gt :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.gt) (ih : p b), p (Batteries.RBNode.node a y b))
    (is_black_lt_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.lt) (hr : Batteries.RBNode.getColor a = red)
        (ih : p a), p (black_node a y b))
    (is_black_lt_not_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.lt) (hnr : Batteries.RBNode.getColor a ≠ red)
        (ih : p a), p (black_node a y b))
    (is_black_eq : ∀ (a y b) (hc : cmpUsing lt x y = Ordering.eq), p (black_node a y b))
    (is_black_gt_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.gt) (hr : Batteries.RBNode.getColor b = red)
        (ih : p b), p (black_node a y b))
    (is_black_gt_not_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.gt) (hnr : Batteries.RBNode.getColor b ≠ red)
        (ih : p b), p (black_node a y b)) :
    p t := by
  induction t
  case leaf => apply is_leaf
  case red_node a y b =>
    cases h : cmpUsing lt x y
    case lt => apply is_red_lt <;> assumption
    case eq => apply is_red_eq <;> assumption
    case gt => apply is_red_gt <;> assumption
  case black_node a y b =>
    cases h : cmpUsing lt x y
    case lt =>
      by_cases get_color a = red
      · apply is_black_lt_red <;> assumption
      · apply is_black_lt_not_red <;> assumption
    case eq => apply is_black_eq <;> assumption
    case gt =>
      by_cases get_color b = red
      · apply is_black_gt_red <;> assumption
      · apply is_black_gt_not_red <;> assumption
#align rbnode.ins.induction Batteries.RBNode.ins.induction

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableBalance1 {l y r v t lo hi} :
    Batteries.RBNode.IsSearchable lt l lo (some y) →
      Batteries.RBNode.IsSearchable lt r (some y) (some v) →
        Batteries.RBNode.IsSearchable lt t (some v) hi →
          Batteries.RBNode.IsSearchable lt (Batteries.RBNode.balance1 l y r v t) lo hi :=
  by
  apply balance.cases l y r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
#align rbnode.is_searchable_balance1 Batteries.RBNode.isSearchableBalance1

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableBalance1Node {t} [IsTrans α lt] :
    ∀ {y s lo hi},
      Batteries.RBNode.IsSearchable lt t lo (some y) →
        Batteries.RBNode.IsSearchable lt s (some y) hi →
          Batteries.RBNode.IsSearchable lt (Batteries.RBNode.balance1Node t y s) lo hi :=
  by
  cases t <;> simp! <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo
    · apply is_searchable_none_low_of_is_searchable_some_low; assumption
    · simp at *; apply is_searchable_some_low_of_is_searchable_of_lt <;> assumption
  all_goals apply is_searchable_balance1 <;> assumption
#align rbnode.is_searchable_balance1_node Batteries.RBNode.isSearchableBalance1Node

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableBalance2 {l y r v t lo hi} :
    Batteries.RBNode.IsSearchable lt t lo (some v) →
      Batteries.RBNode.IsSearchable lt l (some v) (some y) →
        Batteries.RBNode.IsSearchable lt r (some y) hi →
          Batteries.RBNode.IsSearchable lt (Batteries.RBNode.balance2 l y r v t) lo hi :=
  by
  apply balance.cases l y r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
#align rbnode.is_searchable_balance2 Batteries.RBNode.isSearchableBalance2

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableBalance2Node {t} [IsTrans α lt] :
    ∀ {y s lo hi},
      Batteries.RBNode.IsSearchable lt s lo (some y) →
        Batteries.RBNode.IsSearchable lt t (some y) hi →
          Batteries.RBNode.IsSearchable lt (Batteries.RBNode.balance2Node t y s) lo hi :=
  by
  induction t <;> simp! <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases hi
    · apply is_searchable_none_high_of_is_searchable_some_high; assumption
    · simp at *; apply is_searchable_some_high_of_is_searchable_of_lt; assumption'
  all_goals apply is_searchable_balance2; assumption'
#align rbnode.is_searchable_balance2_node Batteries.RBNode.isSearchableBalance2Node

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableIns [DecidableRel lt] {t x} [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (h : Batteries.RBNode.IsSearchable lt t lo hi),
      Batteries.RBNode.Lift lt lo (some x) →
        Batteries.RBNode.Lift lt (some x) hi →
          Batteries.RBNode.IsSearchable lt (Batteries.RBNode.ins lt t x) lo hi :=
  by
  apply ins.induction lt t x <;> intros <;> simp_all! (config := { eta := false }) <;>
    run_tac
      is_searchable_tactic
  · apply ih h_hs₁; assumption; simp [*]
  · apply is_searchable_of_is_searchable_of_incomp hc; assumption
  · apply is_searchable_of_incomp_of_is_searchable hc; assumption
  · apply ih h_hs₂; cases hi <;> simp [*]; assumption
  · apply is_searchable_balance1_node; apply ih h_hs₁; assumption; simp [*]
    assumption
  · apply ih h_hs₁; assumption; simp [*]
  · apply is_searchable_of_is_searchable_of_incomp hc; assumption
  · apply is_searchable_of_incomp_of_is_searchable hc; assumption
  · apply is_searchable_balance2_node; assumption; apply ih h_hs₂; simp [*]
    assumption
  · apply ih h_hs₂; assumption; simp [*]
#align rbnode.is_searchable_ins Batteries.RBNode.isSearchableIns

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.isSearchableMkInsertResult {c t} :
    Batteries.RBNode.IsSearchable lt t none none →
      Batteries.RBNode.IsSearchable lt (Batteries.RBNode.mkInsertResult c t) none none :=
  by
  classical
  cases c <;> cases t <;> simp [mk_insert_result]
  · intro h;
    run_tac
      is_searchable_tactic
#align rbnode.is_searchable_mk_insert_result Batteries.RBNode.isSearchableMkInsertResult

theorem Batteries.RBNode.isSearchableInsert [DecidableRel lt] {t x} [IsStrictWeakOrder α lt] :
    Batteries.RBNode.IsSearchable lt t none none →
      Batteries.RBNode.IsSearchable lt (Batteries.RBNode.insert lt t x) none none :=
  by intro h; simp [insert]; apply is_searchable_mk_insert_result;
  apply is_searchable_ins <;>
    ·
      first
      | assumption
      | simp
#align rbnode.is_searchable_insert Batteries.RBNode.isSearchableInsert

end Batteries.RBNode

namespace Batteries.RBNode

section MembershipLemmas

parameter {α : Type u} (lt : α → α → Prop)

attribute [local simp] mem balance1_node balance2_node

local infixl:0 " ∈ " => Batteries.RBNode.Mem lt

theorem Batteries.RBNode.mem_balance1Node_of_mem_left {x s} (v) (t : Batteries.RBNode α) :
    (x ∈ s) → (x ∈ Batteries.RBNode.balance1Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp at * <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_balance1_node_of_mem_left Batteries.RBNode.mem_balance1Node_of_mem_left

theorem Batteries.RBNode.mem_balance2Node_of_mem_left {x s} (v) (t : Batteries.RBNode α) :
    (x ∈ s) → (x ∈ Batteries.RBNode.balance2Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp at * <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_balance2_node_of_mem_left Batteries.RBNode.mem_balance2Node_of_mem_left

theorem Batteries.RBNode.mem_balance1Node_of_mem_right {x t} (v) (s : Batteries.RBNode α) :
    (x ∈ t) → (x ∈ Batteries.RBNode.balance1Node s v t) :=
  by
  intros; cases s <;> simp [*]
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance1_node_of_mem_right Batteries.RBNode.mem_balance1Node_of_mem_right

theorem Batteries.RBNode.mem_balance2Node_of_mem_right {x t} (v) (s : Batteries.RBNode α) :
    (x ∈ t) → (x ∈ Batteries.RBNode.balance2Node s v t) :=
  by
  intros; cases s <;> simp [*]
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance2_node_of_mem_right Batteries.RBNode.mem_balance2Node_of_mem_right

theorem Batteries.RBNode.mem_balance1Node_of_incomp {x v} (s t) :
    ¬lt x v ∧ ¬lt v x → s ≠ Batteries.RBNode.nil → (x ∈ Batteries.RBNode.balance1Node s v t) :=
  by
  intros; cases s <;> simp
  · contradiction
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance1_node_of_incomp Batteries.RBNode.mem_balance1Node_of_incomp

theorem Batteries.RBNode.mem_balance2Node_of_incomp {x v} (s t) :
    ¬lt v x ∧ ¬lt x v → s ≠ Batteries.RBNode.nil → (x ∈ Batteries.RBNode.balance2Node s v t) :=
  by
  intros; cases s <;> simp
  · contradiction
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance2_node_of_incomp Batteries.RBNode.mem_balance2Node_of_incomp

theorem Batteries.RBNode.ins_ne_nil [DecidableRel lt] (t : Batteries.RBNode α) (x : α) :
    t.ins lt x ≠ Batteries.RBNode.nil :=
  by
  apply ins.induction lt t x
  any_goals intros; simp [ins, *]
  · intros; apply balance1_node_ne_leaf; assumption
  · intros; apply balance2_node_ne_leaf; assumption
#align rbnode.ins_ne_leaf Batteries.RBNode.ins_ne_nil

theorem Batteries.RBNode.insert_ne_nil [DecidableRel lt] (t : Batteries.RBNode α) (x : α) :
    Batteries.RBNode.insert lt t x ≠ Batteries.RBNode.nil :=
  by
  simp [insert]
  cases he : ins lt t x <;> cases get_color t <;> simp [mk_insert_result]
  · have := ins_ne_leaf lt t x; contradiction
  · exact absurd he (ins_ne_leaf _ _ _)
#align rbnode.insert_ne_leaf Batteries.RBNode.insert_ne_nil

theorem Batteries.RBNode.mem_ins_of_incomp [DecidableRel lt] (t : Batteries.RBNode α) {x y : α} :
    ∀ h : ¬lt x y ∧ ¬lt y x, x ∈ t.ins lt y :=
  by
  apply ins.induction lt t y <;> intros <;> simp [ins, *]
  · have := ih h; apply mem_balance1_node_of_mem_left; assumption
  · have := ih h; apply mem_balance2_node_of_mem_left; assumption
#align rbnode.mem_ins_of_incomp Batteries.RBNode.mem_ins_of_incomp

theorem Batteries.RBNode.mem_ins_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt]
    {t : Batteries.RBNode α} (z : α) : ∀ {x} (h : x ∈ t), x ∈ t.ins lt z :=
  by
  apply ins.induction lt t z <;> intros <;> simp_all [ins] <;> try contradiction <;>
    cases_type* or.1
  any_goals intros; simp [h]; done
  any_goals intros; simp [ih h]; done
  · have := incomp_trans_of lt h ⟨hc.2, hc.1⟩; simp [this]
  · apply mem_balance1_node_of_mem_left; apply ih h
  · apply mem_balance1_node_of_incomp; cases h; all_goals simp [*, ins_ne_leaf lt a z]
  · apply mem_balance1_node_of_mem_right; assumption
  · have := incomp_trans_of lt hc ⟨h.2, h.1⟩; simp [this]
  · apply mem_balance2_node_of_mem_right; assumption
  · have := ins_ne_leaf lt a z; apply mem_balance2_node_of_incomp; cases h; simp [*]
    apply ins_ne_leaf
  · apply mem_balance2_node_of_mem_left; apply ih h
#align rbnode.mem_ins_of_mem Batteries.RBNode.mem_ins_of_mem

theorem Batteries.RBNode.mem_mkInsertResult {a t} (c) :
    Batteries.RBNode.Mem lt a t → Batteries.RBNode.Mem lt a (Batteries.RBNode.mkInsertResult c t) :=
  by intros <;> cases c <;> cases t <;> simp_all [mk_insert_result, mem]
#align rbnode.mem_mk_insert_result Batteries.RBNode.mem_mkInsertResult

theorem Batteries.RBNode.mem_of_mem_mkInsertResult {a t c} :
    Batteries.RBNode.Mem lt a (Batteries.RBNode.mkInsertResult c t) → Batteries.RBNode.Mem lt a t :=
  by cases t <;> cases c <;> simp [mk_insert_result, mem] <;> intros <;> assumption
#align rbnode.mem_of_mem_mk_insert_result Batteries.RBNode.mem_of_mem_mkInsertResult

theorem Batteries.RBNode.mem_insert_of_incomp [DecidableRel lt] (t : Batteries.RBNode α) {x y : α} :
    ∀ h : ¬lt x y ∧ ¬lt y x, x ∈ t.insert lt y := by
  intros <;> unfold insert <;> apply mem_mk_insert_result <;> apply mem_ins_of_incomp <;> assumption
#align rbnode.mem_insert_of_incomp Batteries.RBNode.mem_insert_of_incomp

theorem Batteries.RBNode.mem_insert_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt] {t x} (z) :
    (x ∈ t) → (x ∈ t.insert lt z) := by
  intros <;> apply mem_mk_insert_result <;> apply mem_ins_of_mem <;> assumption
#align rbnode.mem_insert_of_mem Batteries.RBNode.mem_insert_of_mem

theorem Batteries.RBNode.of_mem_balance1Node {x s v t} :
    (x ∈ Batteries.RBNode.balance1Node s v t) → (x ∈ s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x ∈ t) :=
  by
  cases s <;> simp
  · intros; simp [*]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.of_mem_balance1_node Batteries.RBNode.of_mem_balance1Node

theorem Batteries.RBNode.of_mem_balance2Node {x s v t} :
    (x ∈ Batteries.RBNode.balance2Node s v t) → (x ∈ s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x ∈ t) :=
  by
  cases s <;> simp
  · intros; simp [*]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.of_mem_balance2_node Batteries.RBNode.of_mem_balance2Node

theorem Batteries.RBNode.equiv_or_mem_of_mem_ins [DecidableRel lt] {t : Batteries.RBNode α} {x z} :
    ∀ h : x ∈ t.ins lt z, x ≈[lt]z ∨ (x ∈ t) :=
  by
  apply ins.induction lt t z <;> intros <;> simp_all [ins, StrictWeakOrder.Equiv] <;>
    cases_type* or.1
  any_goals intros; simp [h]
  any_goals intros; have ih := ih h; cases ih <;> simp [*]; done
  · have h' := of_mem_balance1_node lt h; cases_type* or.1
    have := ih h'; cases_type* or.1
    all_goals simp [h, *]
  · have h' := of_mem_balance2_node lt h; cases_type* or.1
    have := ih h'; cases_type* or.1
    all_goals simp [h, *]
#align rbnode.equiv_or_mem_of_mem_ins Batteries.RBNode.equiv_or_mem_of_mem_ins

theorem Batteries.RBNode.equiv_or_mem_of_mem_insert [DecidableRel lt] {t : Batteries.RBNode α}
    {x z} : ∀ h : x ∈ t.insert lt z, x ≈[lt]z ∨ (x ∈ t) := by simp [insert]; intros;
  apply equiv_or_mem_of_mem_ins; exact mem_of_mem_mk_insert_result lt h
#align rbnode.equiv_or_mem_of_mem_insert Batteries.RBNode.equiv_or_mem_of_mem_insert

attribute [local simp] mem_exact

theorem Batteries.RBNode.memExact_balance1Node_of_memExact {x s} (v) (t : Batteries.RBNode α) :
    Batteries.RBNode.MemExact x s →
      Batteries.RBNode.MemExact x (Batteries.RBNode.balance1Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_exact_balance1_node_of_mem_exact Batteries.RBNode.memExact_balance1Node_of_memExact

theorem Batteries.RBNode.memExact_balance2Node_of_memExact {x s} (v) (t : Batteries.RBNode α) :
    Batteries.RBNode.MemExact x s →
      Batteries.RBNode.MemExact x (Batteries.RBNode.balance2Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_exact_balance2_node_of_mem_exact Batteries.RBNode.memExact_balance2Node_of_memExact

theorem Batteries.RBNode.find?_balance1Node [DecidableRel lt] [IsStrictWeakOrder α lt] {x y z t s} :
    ∀ {lo hi},
      Batteries.RBNode.IsSearchable lt t lo (some z) →
        Batteries.RBNode.IsSearchable lt s (some z) hi →
          Batteries.RBNode.find? lt t y = some x →
            y ≈[lt]x → Batteries.RBNode.find? lt (Batteries.RBNode.balance1Node t z s) y = some x :=
  by
  intro _ _ hs₁ hs₂ heq heqv
  have hs := is_searchable_balance1_node lt hs₁ hs₂
  have := Eq.trans (find_eq_find_of_eqv hs₁ heqv.symm) HEq
  have := Iff.mpr (find_correct_exact hs₁) this
  have := mem_exact_balance1_node_of_mem_exact z s this
  have := Iff.mp (find_correct_exact hs) this
  exact Eq.trans (find_eq_find_of_eqv hs heqv) this
#align rbnode.find_balance1_node Batteries.RBNode.find?_balance1Node

theorem Batteries.RBNode.find?_balance2Node [DecidableRel lt] [IsStrictWeakOrder α lt] {x y z s t}
    [IsTrans α lt] :
    ∀ {lo hi},
      Batteries.RBNode.IsSearchable lt s lo (some z) →
        Batteries.RBNode.IsSearchable lt t (some z) hi →
          Batteries.RBNode.find? lt t y = some x →
            y ≈[lt]x → Batteries.RBNode.find? lt (Batteries.RBNode.balance2Node t z s) y = some x :=
  by
  intro _ _ hs₁ hs₂ heq heqv
  have hs := is_searchable_balance2_node lt hs₁ hs₂
  have := Eq.trans (find_eq_find_of_eqv hs₂ heqv.symm) HEq
  have := Iff.mpr (find_correct_exact hs₂) this
  have := mem_exact_balance2_node_of_mem_exact z s this
  have := Iff.mp (find_correct_exact hs) this
  exact Eq.trans (find_eq_find_of_eqv hs heqv) this
#align rbnode.find_balance2_node Batteries.RBNode.find?_balance2Node

-- Auxiliary lemma
theorem Batteries.RBNode.ite_eq_of_not_lt [DecidableRel lt] [IsStrictOrder α lt] {a b} {β : Type v}
    (t s : β) (h : lt b a) : (if lt a b then t else s) = s := by have := not_lt_of_lt h; simp [*]
#align rbnode.ite_eq_of_not_lt Batteries.RBNode.ite_eq_of_not_lt

attribute [local simp] ite_eq_of_not_lt

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def simp_fi : tactic Unit :=
  sorry

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
theorem Batteries.RBNode.find?_ins_of_eqv [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Batteries.RBNode α} (he : x ≈[lt]y) :
    ∀ {lo hi} (hs : Batteries.RBNode.IsSearchable lt t lo hi)
      (hlt₁ : Batteries.RBNode.Lift lt lo (some x)) (hlt₂ : Batteries.RBNode.Lift lt (some x) hi),
      Batteries.RBNode.find? lt (Batteries.RBNode.ins lt t x) y = some x :=
  by
  simp [StrictWeakOrder.Equiv] at he
  apply ins.induction lt t x <;> intros
  ·
    run_tac
      simp_fi
  all_goals simp at hc; cases hs
  · have := lt_of_incomp_of_lt he.swap hc
    have := ih hs_hs₁ hlt₁ hc
    run_tac
      simp_fi
  ·
    run_tac
      simp_fi
  · have := lt_of_lt_of_incomp hc he
    have := ih hs_hs₂ hc hlt₂
    run_tac
      simp_fi
  · run_tac
      simp_fi
    have := is_searchable_ins lt hs_hs₁ hlt₁ hc
    apply find_balance1_node lt this hs_hs₂ (ih hs_hs₁ hlt₁ hc) he.symm
  · have := lt_of_incomp_of_lt he.swap hc
    have := ih hs_hs₁ hlt₁ hc
    run_tac
      simp_fi
  ·
    run_tac
      simp_fi
  · run_tac
      simp_fi
    have := is_searchable_ins lt hs_hs₂ hc hlt₂
    apply find_balance2_node lt hs_hs₁ this (ih hs_hs₂ hc hlt₂) he.symm
  · have := lt_of_lt_of_incomp hc he
    have := ih hs_hs₂ hc hlt₂
    run_tac
      simp_fi
#align rbnode.find_ins_of_eqv Batteries.RBNode.find?_ins_of_eqv

theorem Batteries.RBNode.find?_mkInsertResult [DecidableRel lt] (c : RBColor)
    (t : Batteries.RBNode α) (x : α) :
    Batteries.RBNode.find? lt (Batteries.RBNode.mkInsertResult c t) x =
      Batteries.RBNode.find? lt t x :=
  by
  cases t <;> cases c <;> simp [mk_insert_result]
  · simp [find]; cases cmpUsing lt x t_val <;> simp [find]
#align rbnode.find_mk_insert_result Batteries.RBNode.find?_mkInsertResult

theorem Batteries.RBNode.find?_insert_of_eqv [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Batteries.RBNode α} (he : x ≈[lt]y) :
    Batteries.RBNode.IsSearchable lt t none none →
      Batteries.RBNode.find? lt (Batteries.RBNode.insert lt t x) y = some x :=
  by
  intro hs
  simp [insert, find_mk_insert_result]
  apply find_ins_of_eqv lt he hs <;> simp
#align rbnode.find_insert_of_eqv Batteries.RBNode.find?_insert_of_eqv

theorem Batteries.RBNode.weak_trichotomous (x y) {p : Prop} (is_lt : ∀ h : lt x y, p)
    (is_eqv : ∀ h : ¬lt x y ∧ ¬lt y x, p) (is_gt : ∀ h : lt y x, p) : p :=
  by
  by_cases lt x y
  · apply is_lt; assumption
  by_cases lt y x
  · apply is_gt; assumption
  · apply is_eqv; constructor <;> assumption
#align rbnode.weak_trichotomous Batteries.RBNode.weak_trichotomous

section FindInsOfNotEqv

section SimpAuxLemmas

theorem Batteries.RBNode.find?_black_eq_find?_red [DecidableRel lt] {l y r x} :
    Batteries.RBNode.find? lt (black_node l y r) x =
      Batteries.RBNode.find? lt (Batteries.RBNode.node l y r) x :=
  by simp [find]; all_goals cases cmpUsing lt x y <;> simp [find]
#align rbnode.find_black_eq_find_red Batteries.RBNode.find?_black_eq_find?_red

theorem Batteries.RBNode.find?_red_of_lt [DecidableRel lt] {l y r x} (h : lt x y) :
    Batteries.RBNode.find? lt (Batteries.RBNode.node l y r) x = Batteries.RBNode.find? lt l x := by
  simp [find, cmpUsing, *]
#align rbnode.find_red_of_lt Batteries.RBNode.find?_red_of_lt

theorem Batteries.RBNode.find?_red_of_gt [DecidableRel lt] [IsStrictOrder α lt] {l y r x}
    (h : lt y x) :
    Batteries.RBNode.find? lt (Batteries.RBNode.node l y r) x = Batteries.RBNode.find? lt r x := by
  have := not_lt_of_lt h; simp [find, cmpUsing, *]
#align rbnode.find_red_of_gt Batteries.RBNode.find?_red_of_gt

theorem Batteries.RBNode.find?_red_of_incomp [DecidableRel lt] {l y r x} (h : ¬lt x y ∧ ¬lt y x) :
    Batteries.RBNode.find? lt (Batteries.RBNode.node l y r) x = some y := by
  simp [find, cmpUsing, *]
#align rbnode.find_red_of_incomp Batteries.RBNode.find?_red_of_incomp

end SimpAuxLemmas

attribute [local simp] find_black_eq_find_red find_red_of_lt find_red_of_lt find_red_of_gt
  find_red_of_incomp

variable [IsStrictWeakOrder α lt] [DecidableRel lt]

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.find?_balance1_lt {l r t v x y lo hi} (h : lt x y)
    (hl : Batteries.RBNode.IsSearchable lt l lo (some v))
    (hr : Batteries.RBNode.IsSearchable lt r (some v) (some y))
    (ht : Batteries.RBNode.IsSearchable lt t (some y) hi) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance1 l v r y t) x =
      Batteries.RBNode.find? lt (Batteries.RBNode.node l v r) x :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · apply weak_trichotomous lt y_1 x <;> intros <;> simp [*]
  · apply weak_trichotomous lt x_1 x <;> intro h'
    · have := trans_of lt (lo_lt_hi hr_hs₁) h'; simp [*]
    · have : lt y_1 x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₁) h'; simp [*]
    · apply weak_trichotomous lt y_1 x <;> intros <;> simp [*]
#align rbnode.find_balance1_lt Batteries.RBNode.find?_balance1_lt

/- ././././Mathport/Syntax/Translate/Expr.lean:338:4: warning: unsupported (TODO): `[tacs] -/
unsafe def ins_ne_leaf_tac :=
  sorry
#align rbnode.ins_ne_leaf_tac rbnode.ins_ne_leaf_tac

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Batteries.RBNode.find?_balance1Node_lt {t s x y lo hi} (hlt : lt y x)
    (ht : Batteries.RBNode.IsSearchable lt t lo (some x))
    (hs : Batteries.RBNode.IsSearchable lt s (some x) hi)
    (hne : t ≠ Batteries.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance1Node t x s) y =
      Batteries.RBNode.find? lt t y :=
  by
  cases t <;> simp [balance1_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance1_lt; assumption'
#align rbnode.find_balance1_node_lt Batteries.RBNode.find?_balance1Node_lt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.find?_balance1_gt {l r t v x y lo hi} (h : lt y x)
    (hl : Batteries.RBNode.IsSearchable lt l lo (some v))
    (hr : Batteries.RBNode.IsSearchable lt r (some v) (some y))
    (ht : Batteries.RBNode.IsSearchable lt t (some y) hi) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance1 l v r y t) x =
      Batteries.RBNode.find? lt t x :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have := trans_of lt (lo_lt_hi hr) h; simp [*]
  · have := trans_of lt (lo_lt_hi hr_hs₂) h; simp [*]
#align rbnode.find_balance1_gt Batteries.RBNode.find?_balance1_gt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Batteries.RBNode.find?_balance1Node_gt {t s x y lo hi} (h : lt x y)
    (ht : Batteries.RBNode.IsSearchable lt t lo (some x))
    (hs : Batteries.RBNode.IsSearchable lt s (some x) hi)
    (hne : t ≠ Batteries.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance1Node t x s) y =
      Batteries.RBNode.find? lt s y :=
  by
  cases t <;> simp [balance1_node]
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance1_gt; assumption'
#align rbnode.find_balance1_node_gt Batteries.RBNode.find?_balance1Node_gt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.find?_balance1_eqv {l r t v x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (hl : Batteries.RBNode.IsSearchable lt l lo (some v))
    (hr : Batteries.RBNode.IsSearchable lt r (some v) (some y))
    (ht : Batteries.RBNode.IsSearchable lt t (some y) hi) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance1 l v r y t) x = some y :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have : lt y_1 x := lt_of_lt_of_incomp (lo_lt_hi hr) h.swap
    simp [*]
  · have : lt x_1 x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₂) h.swap
    simp [*]
#align rbnode.find_balance1_eqv Batteries.RBNode.find?_balance1_eqv

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Batteries.RBNode.find?_balance1Node_eqv {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (ht : Batteries.RBNode.IsSearchable lt t lo (some y))
    (hs : Batteries.RBNode.IsSearchable lt s (some y) hi)
    (hne : t ≠ Batteries.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance1Node t y s) x = some y :=
  by
  cases t <;> simp [balance1_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance1_eqv; assumption'
#align rbnode.find_balance1_node_eqv Batteries.RBNode.find?_balance1Node_eqv

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.find?_balance2_lt {l v r t x y lo hi} (h : lt x y)
    (hl : Batteries.RBNode.IsSearchable lt l (some y) (some v))
    (hr : Batteries.RBNode.IsSearchable lt r (some v) hi)
    (ht : Batteries.RBNode.IsSearchable lt t lo (some y)) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance2 l v r y t) x =
      Batteries.RBNode.find? lt t x :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have := trans h (lo_lt_hi hl_hs₁); simp [*]
  · have := trans h (lo_lt_hi hl); simp [*]
#align rbnode.find_balance2_lt Batteries.RBNode.find?_balance2_lt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Batteries.RBNode.find?_balance2Node_lt {s t x y lo hi} (h : lt x y)
    (ht : Batteries.RBNode.IsSearchable lt t (some y) hi)
    (hs : Batteries.RBNode.IsSearchable lt s lo (some y))
    (hne : t ≠ Batteries.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance2Node t y s) x =
      Batteries.RBNode.find? lt s x :=
  by
  cases t <;> simp [balance2_node]
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance2_lt; assumption'
#align rbnode.find_balance2_node_lt Batteries.RBNode.find?_balance2Node_lt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.find?_balance2_gt {l v r t x y lo hi} (h : lt y x)
    (hl : Batteries.RBNode.IsSearchable lt l (some y) (some v))
    (hr : Batteries.RBNode.IsSearchable lt r (some v) hi)
    (ht : Batteries.RBNode.IsSearchable lt t lo (some y)) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance2 l v r y t) x =
      Batteries.RBNode.find? lt (Batteries.RBNode.node l v r) x :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · apply weak_trichotomous lt x_1 x <;> intro h' <;> simp [*]
    · apply weak_trichotomous lt y_1 x <;> intros <;> simp [*]
    · have : lt x _ := lt_of_incomp_of_lt h'.swap (lo_lt_hi hl_hs₂); simp [*]
    · have := trans h' (lo_lt_hi hl_hs₂); simp [*]
  · apply weak_trichotomous lt y_1 x <;> intros <;> simp [*]
#align rbnode.find_balance2_gt Batteries.RBNode.find?_balance2_gt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Batteries.RBNode.find?_balance2Node_gt {s t x y lo hi} (h : lt y x)
    (ht : Batteries.RBNode.IsSearchable lt t (some y) hi)
    (hs : Batteries.RBNode.IsSearchable lt s lo (some y))
    (hne : t ≠ Batteries.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance2Node t y s) x =
      Batteries.RBNode.find? lt t x :=
  by
  cases t <;> simp [balance2_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance2_gt; assumption'
#align rbnode.find_balance2_node_gt Batteries.RBNode.find?_balance2Node_gt

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Batteries.RBNode.find?_balance2_eqv {l v r t x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (hl : Batteries.RBNode.IsSearchable lt l (some y) (some v))
    (hr : Batteries.RBNode.IsSearchable lt r (some v) hi)
    (ht : Batteries.RBNode.IsSearchable lt t lo (some y)) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance2 l v r y t) x = some y :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have := lt_of_incomp_of_lt h (lo_lt_hi hl_hs₁); simp [*]
  · have := lt_of_incomp_of_lt h (lo_lt_hi hl); simp [*]
#align rbnode.find_balance2_eqv Batteries.RBNode.find?_balance2_eqv

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Batteries.RBNode.find?_balance2Node_eqv {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (ht : Batteries.RBNode.IsSearchable lt t (some y) hi)
    (hs : Batteries.RBNode.IsSearchable lt s lo (some y))
    (hne : t ≠ Batteries.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Batteries.RBNode.find? lt (Batteries.RBNode.balance2Node t y s) x = some y :=
  by
  cases t <;> simp [balance2_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance2_eqv; assumption'
#align rbnode.find_balance2_node_eqv Batteries.RBNode.find?_balance2Node_eqv

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
theorem Batteries.RBNode.find?_ins_of_disj {x y : α} {t : Batteries.RBNode α}
    (hn : lt x y ∨ lt y x) :
    ∀ {lo hi} (hs : Batteries.RBNode.IsSearchable lt t lo hi)
      (hlt₁ : Batteries.RBNode.Lift lt lo (some x)) (hlt₂ : Batteries.RBNode.Lift lt (some x) hi),
      Batteries.RBNode.find? lt (Batteries.RBNode.ins lt t x) y = Batteries.RBNode.find? lt t y :=
  by
  apply ins.induction lt t x <;> intros
  · cases hn
    all_goals simp [find, ins, cmpUsing, *]
  all_goals simp at hc; cases hs
  · have := ih hs_hs₁ hlt₁ hc;
    run_tac
      simp_fi
  · cases hn
    · have := lt_of_incomp_of_lt hc.symm hn
      run_tac
        simp_fi
    · have := lt_of_lt_of_incomp hn hc
      run_tac
        simp_fi
  · have := ih hs_hs₂ hc hlt₂
    run_tac
      simp_fi
  · have ih := ih hs_hs₁ hlt₁ hc
    cases hn
    · cases hc' : cmpUsing lt y y_1 <;> simp at hc'
      · have hsi := is_searchable_ins lt hs_hs₁ hlt₁ (trans_of lt hn hc')
        have := find_balance1_node_lt lt hc' hsi hs_hs₂
        run_tac
          simp_fi
      · have hlt := lt_of_lt_of_incomp hn hc'
        have hsi := is_searchable_ins lt hs_hs₁ hlt₁ hlt
        have := find_balance1_node_eqv lt hc' hsi hs_hs₂
        run_tac
          simp_fi
      · have hsi := is_searchable_ins lt hs_hs₁ hlt₁ hc
        have := find_balance1_node_gt lt hc' hsi hs_hs₂
        simp [*];
        run_tac
          simp_fi
    · have hlt := trans hn hc
      have hsi := is_searchable_ins lt hs_hs₁ hlt₁ hc
      have := find_balance1_node_lt lt hlt hsi hs_hs₂
      run_tac
        simp_fi
  · have := ih hs_hs₁ hlt₁ hc;
    run_tac
      simp_fi
  · cases hn
    · have := lt_of_incomp_of_lt hc.swap hn;
      run_tac
        simp_fi
    · have := lt_of_lt_of_incomp hn hc;
      run_tac
        simp_fi
  · have ih := ih hs_hs₂ hc hlt₂
    cases hn
    · have hlt := trans hc hn;
      run_tac
        simp_fi
      have hsi := is_searchable_ins lt hs_hs₂ hc hlt₂
      have := find_balance2_node_gt lt hlt hsi hs_hs₁
      run_tac
        simp_fi
    · run_tac
        simp_fi
      cases hc' : cmpUsing lt y y_1 <;> simp at hc'
      · have hsi := is_searchable_ins lt hs_hs₂ hc hlt₂
        have := find_balance2_node_lt lt hc' hsi hs_hs₁
        run_tac
          simp_fi
      · have hlt := lt_of_incomp_of_lt hc'.swap hn
        have hsi := is_searchable_ins lt hs_hs₂ hlt hlt₂
        have := find_balance2_node_eqv lt hc' hsi hs_hs₁
        run_tac
          simp_fi
      · have hsi := is_searchable_ins lt hs_hs₂ hc hlt₂
        have := find_balance2_node_gt lt hc' hsi hs_hs₁
        run_tac
          simp_fi
  · have ih := ih hs_hs₂ hc hlt₂
    run_tac
      simp_fi
#align rbnode.find_ins_of_disj Batteries.RBNode.find?_ins_of_disj

end FindInsOfNotEqv

theorem Batteries.RBNode.find?_insert_of_disj [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Batteries.RBNode α} (hd : lt x y ∨ lt y x) :
    Batteries.RBNode.IsSearchable lt t none none →
      Batteries.RBNode.find? lt (Batteries.RBNode.insert lt t x) y =
        Batteries.RBNode.find? lt t y :=
  by
  intro hs
  simp [insert, find_mk_insert_result]
  apply find_ins_of_disj lt hd hs <;> simp
#align rbnode.find_insert_of_disj Batteries.RBNode.find?_insert_of_disj

theorem Batteries.RBNode.find?_insert_of_not_eqv [DecidableRel lt] [IsStrictWeakOrder α lt]
    {x y : α} {t : Batteries.RBNode α} (hn : ¬x ≈[lt]y) :
    Batteries.RBNode.IsSearchable lt t none none →
      Batteries.RBNode.find? lt (Batteries.RBNode.insert lt t x) y =
        Batteries.RBNode.find? lt t y :=
  by
  intro hs
  simp [insert, find_mk_insert_result]
  have he : lt x y ∨ lt y x :=
    by
    simp [StrictWeakOrder.Equiv, Decidable.not_and_iff_or_not, Decidable.not_not_iff] at hn
    assumption
  apply find_ins_of_disj lt he hs <;> simp
#align rbnode.find_insert_of_not_eqv Batteries.RBNode.find?_insert_of_not_eqv

end MembershipLemmas

section IsRedBlack

variable {α : Type u}

open Nat Color

inductive Batteries.RBNode.IsBadRedBlack : Batteries.RBNode α → Nat → Prop
  |
  bad_red {c₁ c₂ n l r v} (rb_l : Batteries.RBNode.IsRedBlack l c₁ n)
    (rb_r : Batteries.RBNode.IsRedBlack r c₂ n) : is_bad_red_black (Batteries.RBNode.node l v r) n
#align rbnode.is_bad_red_black Batteries.RBNode.IsBadRedBlack

theorem Batteries.RBNode.balance1_rb {l r t : Batteries.RBNode α} {y v : α} {c_l c_r c_t n} :
    Batteries.RBNode.IsRedBlack l c_l n →
      Batteries.RBNode.IsRedBlack r c_r n →
        Batteries.RBNode.IsRedBlack t c_t n →
          ∃ c, Batteries.RBNode.IsRedBlack (Batteries.RBNode.balance1 l y r v t) c (succ n) :=
  by
  intro h₁ h₂ _ <;> cases h₁ <;> cases h₂ <;>
    repeat'
      first
      | assumption
      | constructor
#align rbnode.balance1_rb Batteries.RBNode.balance1_rb

theorem Batteries.RBNode.balance2_rb {l r t : Batteries.RBNode α} {y v : α} {c_l c_r c_t n} :
    Batteries.RBNode.IsRedBlack l c_l n →
      Batteries.RBNode.IsRedBlack r c_r n →
        Batteries.RBNode.IsRedBlack t c_t n →
          ∃ c, Batteries.RBNode.IsRedBlack (Batteries.RBNode.balance2 l y r v t) c (succ n) :=
  by
  intro h₁ h₂ _ <;> cases h₁ <;> cases h₂ <;>
    repeat'
      first
      | assumption
      | constructor
#align rbnode.balance2_rb Batteries.RBNode.balance2_rb

theorem Batteries.RBNode.balance1Node_rb {t s : Batteries.RBNode α} {y : α} {c n} :
    Batteries.RBNode.IsBadRedBlack t n →
      Batteries.RBNode.IsRedBlack s c n →
        ∃ c, Batteries.RBNode.IsRedBlack (Batteries.RBNode.balance1Node t y s) c (succ n) :=
  by intro h _ <;> cases h <;> simp [balance1_node] <;> apply balance1_rb <;> assumption'
#align rbnode.balance1_node_rb Batteries.RBNode.balance1Node_rb

theorem Batteries.RBNode.balance2Node_rb {t s : Batteries.RBNode α} {y : α} {c n} :
    Batteries.RBNode.IsBadRedBlack t n →
      Batteries.RBNode.IsRedBlack s c n →
        ∃ c, Batteries.RBNode.IsRedBlack (Batteries.RBNode.balance2Node t y s) c (succ n) :=
  by intro h _ <;> cases h <;> simp [balance2_node] <;> apply balance2_rb <;> assumption'
#align rbnode.balance2_node_rb Batteries.RBNode.balance2Node_rb

def Batteries.RBNode.InsRbResult : Batteries.RBNode α → RBColor → Nat → Prop
  | t, red, n => Batteries.RBNode.IsBadRedBlack t n
  | t, black, n => ∃ c, Batteries.RBNode.IsRedBlack t c n
#align rbnode.ins_rb_result Batteries.RBNode.InsRbResult

variable {lt : α → α → Prop} [DecidableRel lt]

theorem Batteries.RBNode.of_getColor_eq_red {t : Batteries.RBNode α} {c n} :
    Batteries.RBNode.getColor t = red → Batteries.RBNode.IsRedBlack t c n → c = red := by
  intro h₁ h₂; cases h₂ <;> simp only [get_color] at h₁ <;> contradiction
#align rbnode.of_get_color_eq_red Batteries.RBNode.of_getColor_eq_red

theorem Batteries.RBNode.of_getColor_ne_red {t : Batteries.RBNode α} {c n} :
    Batteries.RBNode.getColor t ≠ red → Batteries.RBNode.IsRedBlack t c n → c = black := by
  intro h₁ h₂; cases h₂ <;> simp only [get_color] at h₁ <;> contradiction
#align rbnode.of_get_color_ne_red Batteries.RBNode.of_getColor_ne_red

variable (lt)

theorem Batteries.RBNode.ins_rb {t : Batteries.RBNode α} (x) :
    ∀ {c n} (h : Batteries.RBNode.IsRedBlack t c n),
      Batteries.RBNode.InsRbResult (Batteries.RBNode.ins lt t x) c n :=
  by
  apply ins.induction lt t x <;> intros <;> cases h <;> simp [ins, *, ins_rb_result]
  · repeat' constructor
  · specialize ih h_rb_l; cases ih; constructor <;> assumption
  · constructor <;> assumption
  · specialize ih h_rb_r; cases ih; constructor <;> assumption
  · specialize ih h_rb_l
    cases of_get_color_eq_red hr h_rb_l
    apply balance1_node_rb <;> assumption
  · specialize ih h_rb_l
    cases of_get_color_ne_red hnr h_rb_l
    cases ih
    constructor; constructor <;> assumption
  · constructor; constructor <;> assumption
  · specialize ih h_rb_r
    cases of_get_color_eq_red hr h_rb_r
    apply balance2_node_rb <;> assumption
  · specialize ih h_rb_r
    cases of_get_color_ne_red hnr h_rb_r
    cases ih
    constructor; constructor <;> assumption
#align rbnode.ins_rb Batteries.RBNode.ins_rb

def Batteries.RBNode.InsertRbResult : Batteries.RBNode α → RBColor → Nat → Prop
  | t, red, n => Batteries.RBNode.IsRedBlack t black (succ n)
  | t, black, n => ∃ c, Batteries.RBNode.IsRedBlack t c n
#align rbnode.insert_rb_result Batteries.RBNode.InsertRbResult

theorem Batteries.RBNode.insert_rb {t : Batteries.RBNode α} (x) {c n}
    (h : Batteries.RBNode.IsRedBlack t c n) :
    Batteries.RBNode.InsertRbResult (Batteries.RBNode.insert lt t x) c n :=
  by
  simp [insert]
  have hi := ins_rb lt x h
  generalize he : ins lt t x = r
  simp [he] at hi
  cases h <;> simp [get_color, ins_rb_result, insert_rb_result, mk_insert_result] at *
  assumption'
  · cases hi; simp [mk_insert_result]; constructor <;> assumption
#align rbnode.insert_rb Batteries.RBNode.insert_rb

theorem Batteries.RBNode.insert_isRedBlack {t : Batteries.RBNode α} {c n} (x) :
    Batteries.RBNode.IsRedBlack t c n →
      ∃ c n, Batteries.RBNode.IsRedBlack (Batteries.RBNode.insert lt t x) c n :=
  by
  intro h
  have := insert_rb lt x h
  cases c <;> simp [insert_rb_result] at this
  · constructor; constructor; assumption
  · cases this; constructor; constructor; assumption
#align rbnode.insert_is_red_black Batteries.RBNode.insert_isRedBlack

end IsRedBlack

end Batteries.RBNode

