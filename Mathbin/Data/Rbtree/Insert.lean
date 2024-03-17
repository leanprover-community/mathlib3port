/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Data.Rbtree.Find

#align_import data.rbtree.insert from "leanprover-community/mathlib"@"4d4167104581a21259f7f448e1972a63a4546be7"

universe u v

attribute [local simp] Std.RBNode.Lift

namespace Std.RBNode

variable {α : Type u}

open Color

@[simp]
theorem Std.RBNode.balance1_eq₁ (l : Std.RBNode α) (x r₁ y r₂ v t) :
    Std.RBNode.balance1 (Std.RBNode.node l x r₁) y r₂ v t =
      Std.RBNode.node (black_node l x r₁) y (black_node r₂ v t) :=
  by cases r₂ <;> rfl
#align rbnode.balance1_eq₁ Std.RBNode.balance1_eq₁

@[simp]
theorem Std.RBNode.balance1_eq₂ (l₁ : Std.RBNode α) (y l₂ x r v t) :
    Std.RBNode.getColor l₁ ≠ red →
      Std.RBNode.balance1 l₁ y (Std.RBNode.node l₂ x r) v t =
        Std.RBNode.node (black_node l₁ y l₂) x (black_node r v t) :=
  by cases l₁ <;> simp [get_color, balance1, false_imp_iff]
#align rbnode.balance1_eq₂ Std.RBNode.balance1_eq₂

@[simp]
theorem Std.RBNode.balance1_eq₃ (l : Std.RBNode α) (y r v t) :
    Std.RBNode.getColor l ≠ red →
      Std.RBNode.getColor r ≠ red →
        Std.RBNode.balance1 l y r v t = black_node (Std.RBNode.node l y r) v t :=
  by cases l <;> cases r <;> simp [get_color, balance1, false_imp_iff]
#align rbnode.balance1_eq₃ Std.RBNode.balance1_eq₃

@[simp]
theorem Std.RBNode.balance2_eq₁ (l : Std.RBNode α) (x₁ r₁ y r₂ v t) :
    Std.RBNode.balance2 (Std.RBNode.node l x₁ r₁) y r₂ v t =
      Std.RBNode.node (black_node t v l) x₁ (black_node r₁ y r₂) :=
  by cases r₂ <;> rfl
#align rbnode.balance2_eq₁ Std.RBNode.balance2_eq₁

@[simp]
theorem Std.RBNode.balance2_eq₂ (l₁ : Std.RBNode α) (y l₂ x₂ r₂ v t) :
    Std.RBNode.getColor l₁ ≠ red →
      Std.RBNode.balance2 l₁ y (Std.RBNode.node l₂ x₂ r₂) v t =
        Std.RBNode.node (black_node t v l₁) y (black_node l₂ x₂ r₂) :=
  by cases l₁ <;> simp [get_color, balance2, false_imp_iff]
#align rbnode.balance2_eq₂ Std.RBNode.balance2_eq₂

@[simp]
theorem Std.RBNode.balance2_eq₃ (l : Std.RBNode α) (y r v t) :
    Std.RBNode.getColor l ≠ red →
      Std.RBNode.getColor r ≠ red →
        Std.RBNode.balance2 l y r v t = black_node t v (Std.RBNode.node l y r) :=
  by cases l <;> cases r <;> simp [get_color, balance2, false_imp_iff]
#align rbnode.balance2_eq₃ Std.RBNode.balance2_eq₃

-- We can use the same induction principle for balance1 and balance2
theorem Std.RBNode.Balance.cases {p : Std.RBNode α → α → Std.RBNode α → Prop} (l y r)
    (red_left : ∀ l x r₁ y r₂, p (Std.RBNode.node l x r₁) y r₂)
    (red_right : ∀ l₁ y l₂ x r, Std.RBNode.getColor l₁ ≠ red → p l₁ y (Std.RBNode.node l₂ x r))
    (other : ∀ l y r, Std.RBNode.getColor l ≠ red → Std.RBNode.getColor r ≠ red → p l y r) :
    p l y r := by
  cases l <;> cases r
  any_goals apply red_left
  any_goals apply red_right <;> simp [get_color] <;> contradiction <;> done
  any_goals apply other <;> simp [get_color] <;> contradiction <;> done
#align rbnode.balance.cases Std.RBNode.Balance.cases

theorem Std.RBNode.balance1_ne_nil (l : Std.RBNode α) (x r v t) :
    Std.RBNode.balance1 l x r v t ≠ Std.RBNode.nil := by
  apply balance.cases l x r <;> intros <;> simp [*] <;> contradiction
#align rbnode.balance1_ne_leaf Std.RBNode.balance1_ne_nil

theorem Std.RBNode.balance1Node_ne_nil {s : Std.RBNode α} (a : α) (t : Std.RBNode α) :
    s ≠ Std.RBNode.nil → Std.RBNode.balance1Node s a t ≠ Std.RBNode.nil :=
  by
  intro h; cases s
  · contradiction
  all_goals simp [balance1_node]; apply balance1_ne_leaf
#align rbnode.balance1_node_ne_leaf Std.RBNode.balance1Node_ne_nil

theorem Std.RBNode.balance2_ne_nil (l : Std.RBNode α) (x r v t) :
    Std.RBNode.balance2 l x r v t ≠ Std.RBNode.nil := by
  apply balance.cases l x r <;> intros <;> simp [*] <;> contradiction
#align rbnode.balance2_ne_leaf Std.RBNode.balance2_ne_nil

theorem Std.RBNode.balance2Node_ne_nil {s : Std.RBNode α} (a : α) (t : Std.RBNode α) :
    s ≠ Std.RBNode.nil → Std.RBNode.balance2Node s a t ≠ Std.RBNode.nil :=
  by
  intro h; cases s
  · contradiction
  all_goals simp [balance2_node]; apply balance2_ne_leaf
#align rbnode.balance2_node_ne_leaf Std.RBNode.balance2Node_ne_nil

variable (lt : α → α → Prop)

@[elab_as_elim]
theorem Std.RBNode.ins.induction [DecidableRel lt] {p : Std.RBNode α → Prop} (t x)
    (is_leaf : p Std.RBNode.nil)
    (is_red_lt :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.lt) (ih : p a), p (Std.RBNode.node a y b))
    (is_red_eq : ∀ (a y b) (hc : cmpUsing lt x y = Ordering.eq), p (Std.RBNode.node a y b))
    (is_red_gt :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.gt) (ih : p b), p (Std.RBNode.node a y b))
    (is_black_lt_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.lt) (hr : Std.RBNode.getColor a = red) (ih : p a),
        p (black_node a y b))
    (is_black_lt_not_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.lt) (hnr : Std.RBNode.getColor a ≠ red) (ih : p a),
        p (black_node a y b))
    (is_black_eq : ∀ (a y b) (hc : cmpUsing lt x y = Ordering.eq), p (black_node a y b))
    (is_black_gt_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.gt) (hr : Std.RBNode.getColor b = red) (ih : p b),
        p (black_node a y b))
    (is_black_gt_not_red :
      ∀ (a y b) (hc : cmpUsing lt x y = Ordering.gt) (hnr : Std.RBNode.getColor b ≠ red) (ih : p b),
        p (black_node a y b)) :
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
#align rbnode.ins.induction Std.RBNode.ins.induction

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.isSearchableBalance1 {l y r v t lo hi} :
    Std.RBNode.IsSearchable lt l lo (some y) →
      Std.RBNode.IsSearchable lt r (some y) (some v) →
        Std.RBNode.IsSearchable lt t (some v) hi →
          Std.RBNode.IsSearchable lt (Std.RBNode.balance1 l y r v t) lo hi :=
  by
  apply balance.cases l y r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
#align rbnode.is_searchable_balance1 Std.RBNode.isSearchableBalance1

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.isSearchableBalance1Node {t} [IsTrans α lt] :
    ∀ {y s lo hi},
      Std.RBNode.IsSearchable lt t lo (some y) →
        Std.RBNode.IsSearchable lt s (some y) hi →
          Std.RBNode.IsSearchable lt (Std.RBNode.balance1Node t y s) lo hi :=
  by
  cases t <;> simp! <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases lo
    · apply is_searchable_none_low_of_is_searchable_some_low; assumption
    · simp at *; apply is_searchable_some_low_of_is_searchable_of_lt <;> assumption
  all_goals apply is_searchable_balance1 <;> assumption
#align rbnode.is_searchable_balance1_node Std.RBNode.isSearchableBalance1Node

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.isSearchableBalance2 {l y r v t lo hi} :
    Std.RBNode.IsSearchable lt t lo (some v) →
      Std.RBNode.IsSearchable lt l (some v) (some y) →
        Std.RBNode.IsSearchable lt r (some y) hi →
          Std.RBNode.IsSearchable lt (Std.RBNode.balance2 l y r v t) lo hi :=
  by
  apply balance.cases l y r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
#align rbnode.is_searchable_balance2 Std.RBNode.isSearchableBalance2

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.isSearchableBalance2Node {t} [IsTrans α lt] :
    ∀ {y s lo hi},
      Std.RBNode.IsSearchable lt s lo (some y) →
        Std.RBNode.IsSearchable lt t (some y) hi →
          Std.RBNode.IsSearchable lt (Std.RBNode.balance2Node t y s) lo hi :=
  by
  induction t <;> simp! <;> intros <;>
    run_tac
      is_searchable_tactic
  · cases hi
    · apply is_searchable_none_high_of_is_searchable_some_high; assumption
    · simp at *; apply is_searchable_some_high_of_is_searchable_of_lt; assumption'
  all_goals apply is_searchable_balance2; assumption'
#align rbnode.is_searchable_balance2_node Std.RBNode.isSearchableBalance2Node

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.isSearchableIns [DecidableRel lt] {t x} [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (h : Std.RBNode.IsSearchable lt t lo hi),
      Std.RBNode.Lift lt lo (some x) →
        Std.RBNode.Lift lt (some x) hi → Std.RBNode.IsSearchable lt (Std.RBNode.ins lt t x) lo hi :=
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
#align rbnode.is_searchable_ins Std.RBNode.isSearchableIns

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.isSearchableMkInsertResult {c t} :
    Std.RBNode.IsSearchable lt t none none →
      Std.RBNode.IsSearchable lt (Std.RBNode.mkInsertResult c t) none none :=
  by
  classical
  cases c <;> cases t <;> simp [mk_insert_result]
  · intro h;
    run_tac
      is_searchable_tactic
#align rbnode.is_searchable_mk_insert_result Std.RBNode.isSearchableMkInsertResult

theorem Std.RBNode.isSearchableInsert [DecidableRel lt] {t x} [IsStrictWeakOrder α lt] :
    Std.RBNode.IsSearchable lt t none none →
      Std.RBNode.IsSearchable lt (Std.RBNode.insert lt t x) none none :=
  by intro h; simp [insert]; apply is_searchable_mk_insert_result;
  apply is_searchable_ins <;>
    ·
      first
      | assumption
      | simp
#align rbnode.is_searchable_insert Std.RBNode.isSearchableInsert

end Std.RBNode

namespace Std.RBNode

section MembershipLemmas

parameter {α : Type u} (lt : α → α → Prop)

attribute [local simp] mem balance1_node balance2_node

local infixl:0 " ∈ " => Std.RBNode.Mem lt

theorem Std.RBNode.mem_balance1Node_of_mem_left {x s} (v) (t : Std.RBNode α) :
    (x ∈ s) → (x ∈ Std.RBNode.balance1Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp at * <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_balance1_node_of_mem_left Std.RBNode.mem_balance1Node_of_mem_left

theorem Std.RBNode.mem_balance2Node_of_mem_left {x s} (v) (t : Std.RBNode α) :
    (x ∈ s) → (x ∈ Std.RBNode.balance2Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp at * <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_balance2_node_of_mem_left Std.RBNode.mem_balance2Node_of_mem_left

theorem Std.RBNode.mem_balance1Node_of_mem_right {x t} (v) (s : Std.RBNode α) :
    (x ∈ t) → (x ∈ Std.RBNode.balance1Node s v t) :=
  by
  intros; cases s <;> simp [*]
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance1_node_of_mem_right Std.RBNode.mem_balance1Node_of_mem_right

theorem Std.RBNode.mem_balance2Node_of_mem_right {x t} (v) (s : Std.RBNode α) :
    (x ∈ t) → (x ∈ Std.RBNode.balance2Node s v t) :=
  by
  intros; cases s <;> simp [*]
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance2_node_of_mem_right Std.RBNode.mem_balance2Node_of_mem_right

theorem Std.RBNode.mem_balance1Node_of_incomp {x v} (s t) :
    ¬lt x v ∧ ¬lt v x → s ≠ Std.RBNode.nil → (x ∈ Std.RBNode.balance1Node s v t) :=
  by
  intros; cases s <;> simp
  · contradiction
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance1_node_of_incomp Std.RBNode.mem_balance1Node_of_incomp

theorem Std.RBNode.mem_balance2Node_of_incomp {x v} (s t) :
    ¬lt v x ∧ ¬lt x v → s ≠ Std.RBNode.nil → (x ∈ Std.RBNode.balance2Node s v t) :=
  by
  intros; cases s <;> simp
  · contradiction
  all_goals apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp [*]
#align rbnode.mem_balance2_node_of_incomp Std.RBNode.mem_balance2Node_of_incomp

theorem Std.RBNode.ins_ne_nil [DecidableRel lt] (t : Std.RBNode α) (x : α) :
    t.ins lt x ≠ Std.RBNode.nil := by
  apply ins.induction lt t x
  any_goals intros; simp [ins, *]
  · intros; apply balance1_node_ne_leaf; assumption
  · intros; apply balance2_node_ne_leaf; assumption
#align rbnode.ins_ne_leaf Std.RBNode.ins_ne_nil

theorem Std.RBNode.insert_ne_nil [DecidableRel lt] (t : Std.RBNode α) (x : α) :
    Std.RBNode.insert lt t x ≠ Std.RBNode.nil :=
  by
  simp [insert]
  cases he : ins lt t x <;> cases get_color t <;> simp [mk_insert_result]
  · have := ins_ne_leaf lt t x; contradiction
  · exact absurd he (ins_ne_leaf _ _ _)
#align rbnode.insert_ne_leaf Std.RBNode.insert_ne_nil

theorem Std.RBNode.mem_ins_of_incomp [DecidableRel lt] (t : Std.RBNode α) {x y : α} :
    ∀ h : ¬lt x y ∧ ¬lt y x, x ∈ t.ins lt y :=
  by
  apply ins.induction lt t y <;> intros <;> simp [ins, *]
  · have := ih h; apply mem_balance1_node_of_mem_left; assumption
  · have := ih h; apply mem_balance2_node_of_mem_left; assumption
#align rbnode.mem_ins_of_incomp Std.RBNode.mem_ins_of_incomp

theorem Std.RBNode.mem_ins_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt] {t : Std.RBNode α}
    (z : α) : ∀ {x} (h : x ∈ t), x ∈ t.ins lt z :=
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
#align rbnode.mem_ins_of_mem Std.RBNode.mem_ins_of_mem

theorem Std.RBNode.mem_mkInsertResult {a t} (c) :
    Std.RBNode.Mem lt a t → Std.RBNode.Mem lt a (Std.RBNode.mkInsertResult c t) := by
  intros <;> cases c <;> cases t <;> simp_all [mk_insert_result, mem]
#align rbnode.mem_mk_insert_result Std.RBNode.mem_mkInsertResult

theorem Std.RBNode.mem_of_mem_mkInsertResult {a t c} :
    Std.RBNode.Mem lt a (Std.RBNode.mkInsertResult c t) → Std.RBNode.Mem lt a t := by
  cases t <;> cases c <;> simp [mk_insert_result, mem] <;> intros <;> assumption
#align rbnode.mem_of_mem_mk_insert_result Std.RBNode.mem_of_mem_mkInsertResult

theorem Std.RBNode.mem_insert_of_incomp [DecidableRel lt] (t : Std.RBNode α) {x y : α} :
    ∀ h : ¬lt x y ∧ ¬lt y x, x ∈ t.insert lt y := by
  intros <;> unfold insert <;> apply mem_mk_insert_result <;> apply mem_ins_of_incomp <;> assumption
#align rbnode.mem_insert_of_incomp Std.RBNode.mem_insert_of_incomp

#print Std.RBNode.mem_insert_of_mem /-
theorem Std.RBNode.mem_insert_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt] {t x} (z) :
    (x ∈ t) → (x ∈ t.insert lt z) := by
  intros <;> apply mem_mk_insert_result <;> apply mem_ins_of_mem <;> assumption
#align rbnode.mem_insert_of_mem Std.RBNode.mem_insert_of_mem
-/

theorem Std.RBNode.of_mem_balance1Node {x s v t} :
    (x ∈ Std.RBNode.balance1Node s v t) → (x ∈ s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x ∈ t) :=
  by
  cases s <;> simp
  · intros; simp [*]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.of_mem_balance1_node Std.RBNode.of_mem_balance1Node

theorem Std.RBNode.of_mem_balance2Node {x s v t} :
    (x ∈ Std.RBNode.balance2Node s v t) → (x ∈ s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x ∈ t) :=
  by
  cases s <;> simp
  · intros; simp [*]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.of_mem_balance2_node Std.RBNode.of_mem_balance2Node

theorem Std.RBNode.equiv_or_mem_of_mem_ins [DecidableRel lt] {t : Std.RBNode α} {x z} :
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
#align rbnode.equiv_or_mem_of_mem_ins Std.RBNode.equiv_or_mem_of_mem_ins

theorem Std.RBNode.equiv_or_mem_of_mem_insert [DecidableRel lt] {t : Std.RBNode α} {x z} :
    ∀ h : x ∈ t.insert lt z, x ≈[lt]z ∨ (x ∈ t) := by simp [insert]; intros;
  apply equiv_or_mem_of_mem_ins; exact mem_of_mem_mk_insert_result lt h
#align rbnode.equiv_or_mem_of_mem_insert Std.RBNode.equiv_or_mem_of_mem_insert

attribute [local simp] mem_exact

theorem Std.RBNode.memExact_balance1Node_of_memExact {x s} (v) (t : Std.RBNode α) :
    Std.RBNode.MemExact x s → Std.RBNode.MemExact x (Std.RBNode.balance1Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_exact_balance1_node_of_mem_exact Std.RBNode.memExact_balance1Node_of_memExact

theorem Std.RBNode.memExact_balance2Node_of_memExact {x s} (v) (t : Std.RBNode α) :
    Std.RBNode.MemExact x s → Std.RBNode.MemExact x (Std.RBNode.balance2Node s v t) :=
  by
  cases s <;> simp [false_imp_iff]
  all_goals
    apply balance.cases s_lchild s_val s_rchild <;> intros <;> simp_all <;> cases_type* or.1 <;>
      simp [*]
#align rbnode.mem_exact_balance2_node_of_mem_exact Std.RBNode.memExact_balance2Node_of_memExact

theorem Std.RBNode.find?_balance1Node [DecidableRel lt] [IsStrictWeakOrder α lt] {x y z t s} :
    ∀ {lo hi},
      Std.RBNode.IsSearchable lt t lo (some z) →
        Std.RBNode.IsSearchable lt s (some z) hi →
          Std.RBNode.find? lt t y = some x →
            y ≈[lt]x → Std.RBNode.find? lt (Std.RBNode.balance1Node t z s) y = some x :=
  by
  intro _ _ hs₁ hs₂ heq heqv
  have hs := is_searchable_balance1_node lt hs₁ hs₂
  have := Eq.trans (find_eq_find_of_eqv hs₁ heqv.symm) HEq
  have := Iff.mpr (find_correct_exact hs₁) this
  have := mem_exact_balance1_node_of_mem_exact z s this
  have := Iff.mp (find_correct_exact hs) this
  exact Eq.trans (find_eq_find_of_eqv hs heqv) this
#align rbnode.find_balance1_node Std.RBNode.find?_balance1Node

theorem Std.RBNode.find?_balance2Node [DecidableRel lt] [IsStrictWeakOrder α lt] {x y z s t}
    [IsTrans α lt] :
    ∀ {lo hi},
      Std.RBNode.IsSearchable lt s lo (some z) →
        Std.RBNode.IsSearchable lt t (some z) hi →
          Std.RBNode.find? lt t y = some x →
            y ≈[lt]x → Std.RBNode.find? lt (Std.RBNode.balance2Node t z s) y = some x :=
  by
  intro _ _ hs₁ hs₂ heq heqv
  have hs := is_searchable_balance2_node lt hs₁ hs₂
  have := Eq.trans (find_eq_find_of_eqv hs₂ heqv.symm) HEq
  have := Iff.mpr (find_correct_exact hs₂) this
  have := mem_exact_balance2_node_of_mem_exact z s this
  have := Iff.mp (find_correct_exact hs) this
  exact Eq.trans (find_eq_find_of_eqv hs heqv) this
#align rbnode.find_balance2_node Std.RBNode.find?_balance2Node

-- Auxiliary lemma
theorem Std.RBNode.ite_eq_of_not_lt [DecidableRel lt] [IsStrictOrder α lt] {a b} {β : Type v}
    (t s : β) (h : lt b a) : (if lt a b then t else s) = s := by have := not_lt_of_lt h; simp [*]
#align rbnode.ite_eq_of_not_lt Std.RBNode.ite_eq_of_not_lt

attribute [local simp] ite_eq_of_not_lt

/- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
private unsafe def simp_fi : tactic Unit :=
  sorry

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
theorem Std.RBNode.find?_ins_of_eqv [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Std.RBNode α} (he : x ≈[lt]y) :
    ∀ {lo hi} (hs : Std.RBNode.IsSearchable lt t lo hi) (hlt₁ : Std.RBNode.Lift lt lo (some x))
      (hlt₂ : Std.RBNode.Lift lt (some x) hi),
      Std.RBNode.find? lt (Std.RBNode.ins lt t x) y = some x :=
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
#align rbnode.find_ins_of_eqv Std.RBNode.find?_ins_of_eqv

theorem Std.RBNode.find?_mkInsertResult [DecidableRel lt] (c : RBColor) (t : Std.RBNode α) (x : α) :
    Std.RBNode.find? lt (Std.RBNode.mkInsertResult c t) x = Std.RBNode.find? lt t x :=
  by
  cases t <;> cases c <;> simp [mk_insert_result]
  · simp [find]; cases cmpUsing lt x t_val <;> simp [find]
#align rbnode.find_mk_insert_result Std.RBNode.find?_mkInsertResult

theorem Std.RBNode.find?_insert_of_eqv [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Std.RBNode α} (he : x ≈[lt]y) :
    Std.RBNode.IsSearchable lt t none none →
      Std.RBNode.find? lt (Std.RBNode.insert lt t x) y = some x :=
  by
  intro hs
  simp [insert, find_mk_insert_result]
  apply find_ins_of_eqv lt he hs <;> simp
#align rbnode.find_insert_of_eqv Std.RBNode.find?_insert_of_eqv

theorem Std.RBNode.weak_trichotomous (x y) {p : Prop} (is_lt : ∀ h : lt x y, p)
    (is_eqv : ∀ h : ¬lt x y ∧ ¬lt y x, p) (is_gt : ∀ h : lt y x, p) : p :=
  by
  by_cases lt x y
  · apply is_lt; assumption
  by_cases lt y x
  · apply is_gt; assumption
  · apply is_eqv; constructor <;> assumption
#align rbnode.weak_trichotomous Std.RBNode.weak_trichotomous

section FindInsOfNotEqv

section SimpAuxLemmas

theorem Std.RBNode.find?_black_eq_find?_red [DecidableRel lt] {l y r x} :
    Std.RBNode.find? lt (black_node l y r) x = Std.RBNode.find? lt (Std.RBNode.node l y r) x := by
  simp [find]; all_goals cases cmpUsing lt x y <;> simp [find]
#align rbnode.find_black_eq_find_red Std.RBNode.find?_black_eq_find?_red

theorem Std.RBNode.find?_red_of_lt [DecidableRel lt] {l y r x} (h : lt x y) :
    Std.RBNode.find? lt (Std.RBNode.node l y r) x = Std.RBNode.find? lt l x := by
  simp [find, cmpUsing, *]
#align rbnode.find_red_of_lt Std.RBNode.find?_red_of_lt

theorem Std.RBNode.find?_red_of_gt [DecidableRel lt] [IsStrictOrder α lt] {l y r x} (h : lt y x) :
    Std.RBNode.find? lt (Std.RBNode.node l y r) x = Std.RBNode.find? lt r x := by
  have := not_lt_of_lt h; simp [find, cmpUsing, *]
#align rbnode.find_red_of_gt Std.RBNode.find?_red_of_gt

theorem Std.RBNode.find?_red_of_incomp [DecidableRel lt] {l y r x} (h : ¬lt x y ∧ ¬lt y x) :
    Std.RBNode.find? lt (Std.RBNode.node l y r) x = some y := by simp [find, cmpUsing, *]
#align rbnode.find_red_of_incomp Std.RBNode.find?_red_of_incomp

end SimpAuxLemmas

attribute [local simp] find_black_eq_find_red find_red_of_lt find_red_of_lt find_red_of_gt
  find_red_of_incomp

variable [IsStrictWeakOrder α lt] [DecidableRel lt]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.find?_balance1_lt {l r t v x y lo hi} (h : lt x y)
    (hl : Std.RBNode.IsSearchable lt l lo (some v))
    (hr : Std.RBNode.IsSearchable lt r (some v) (some y))
    (ht : Std.RBNode.IsSearchable lt t (some y) hi) :
    Std.RBNode.find? lt (Std.RBNode.balance1 l v r y t) x =
      Std.RBNode.find? lt (Std.RBNode.node l v r) x :=
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
#align rbnode.find_balance1_lt Std.RBNode.find?_balance1_lt

/- ./././Mathport/Syntax/Translate/Expr.lean:337:4: warning: unsupported (TODO): `[tacs] -/
unsafe def ins_ne_leaf_tac :=
  sorry
#align rbnode.ins_ne_leaf_tac rbnode.ins_ne_leaf_tac

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Std.RBNode.find?_balance1Node_lt {t s x y lo hi} (hlt : lt y x)
    (ht : Std.RBNode.IsSearchable lt t lo (some x)) (hs : Std.RBNode.IsSearchable lt s (some x) hi)
    (hne : t ≠ Std.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Std.RBNode.find? lt (Std.RBNode.balance1Node t x s) y = Std.RBNode.find? lt t y :=
  by
  cases t <;> simp [balance1_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance1_lt; assumption'
#align rbnode.find_balance1_node_lt Std.RBNode.find?_balance1Node_lt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.find?_balance1_gt {l r t v x y lo hi} (h : lt y x)
    (hl : Std.RBNode.IsSearchable lt l lo (some v))
    (hr : Std.RBNode.IsSearchable lt r (some v) (some y))
    (ht : Std.RBNode.IsSearchable lt t (some y) hi) :
    Std.RBNode.find? lt (Std.RBNode.balance1 l v r y t) x = Std.RBNode.find? lt t x :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have := trans_of lt (lo_lt_hi hr) h; simp [*]
  · have := trans_of lt (lo_lt_hi hr_hs₂) h; simp [*]
#align rbnode.find_balance1_gt Std.RBNode.find?_balance1_gt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Std.RBNode.find?_balance1Node_gt {t s x y lo hi} (h : lt x y)
    (ht : Std.RBNode.IsSearchable lt t lo (some x)) (hs : Std.RBNode.IsSearchable lt s (some x) hi)
    (hne : t ≠ Std.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Std.RBNode.find? lt (Std.RBNode.balance1Node t x s) y = Std.RBNode.find? lt s y :=
  by
  cases t <;> simp [balance1_node]
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance1_gt; assumption'
#align rbnode.find_balance1_node_gt Std.RBNode.find?_balance1Node_gt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.find?_balance1_eqv {l r t v x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (hl : Std.RBNode.IsSearchable lt l lo (some v))
    (hr : Std.RBNode.IsSearchable lt r (some v) (some y))
    (ht : Std.RBNode.IsSearchable lt t (some y) hi) :
    Std.RBNode.find? lt (Std.RBNode.balance1 l v r y t) x = some y :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have : lt y_1 x := lt_of_lt_of_incomp (lo_lt_hi hr) h.swap
    simp [*]
  · have : lt x_1 x := lt_of_lt_of_incomp (lo_lt_hi hr_hs₂) h.swap
    simp [*]
#align rbnode.find_balance1_eqv Std.RBNode.find?_balance1_eqv

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Std.RBNode.find?_balance1Node_eqv {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (ht : Std.RBNode.IsSearchable lt t lo (some y)) (hs : Std.RBNode.IsSearchable lt s (some y) hi)
    (hne : t ≠ Std.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Std.RBNode.find? lt (Std.RBNode.balance1Node t y s) x = some y :=
  by
  cases t <;> simp [balance1_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance1_eqv; assumption'
#align rbnode.find_balance1_node_eqv Std.RBNode.find?_balance1Node_eqv

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.find?_balance2_lt {l v r t x y lo hi} (h : lt x y)
    (hl : Std.RBNode.IsSearchable lt l (some y) (some v))
    (hr : Std.RBNode.IsSearchable lt r (some v) hi)
    (ht : Std.RBNode.IsSearchable lt t lo (some y)) :
    Std.RBNode.find? lt (Std.RBNode.balance2 l v r y t) x = Std.RBNode.find? lt t x :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have := trans h (lo_lt_hi hl_hs₁); simp [*]
  · have := trans h (lo_lt_hi hl); simp [*]
#align rbnode.find_balance2_lt Std.RBNode.find?_balance2_lt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Std.RBNode.find?_balance2Node_lt {s t x y lo hi} (h : lt x y)
    (ht : Std.RBNode.IsSearchable lt t (some y) hi) (hs : Std.RBNode.IsSearchable lt s lo (some y))
    (hne : t ≠ Std.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Std.RBNode.find? lt (Std.RBNode.balance2Node t y s) x = Std.RBNode.find? lt s x :=
  by
  cases t <;> simp [balance2_node]
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance2_lt; assumption'
#align rbnode.find_balance2_node_lt Std.RBNode.find?_balance2Node_lt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.find?_balance2_gt {l v r t x y lo hi} (h : lt y x)
    (hl : Std.RBNode.IsSearchable lt l (some y) (some v))
    (hr : Std.RBNode.IsSearchable lt r (some v) hi)
    (ht : Std.RBNode.IsSearchable lt t lo (some y)) :
    Std.RBNode.find? lt (Std.RBNode.balance2 l v r y t) x =
      Std.RBNode.find? lt (Std.RBNode.node l v r) x :=
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
#align rbnode.find_balance2_gt Std.RBNode.find?_balance2_gt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Std.RBNode.find?_balance2Node_gt {s t x y lo hi} (h : lt y x)
    (ht : Std.RBNode.IsSearchable lt t (some y) hi) (hs : Std.RBNode.IsSearchable lt s lo (some y))
    (hne : t ≠ Std.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Std.RBNode.find? lt (Std.RBNode.balance2Node t y s) x = Std.RBNode.find? lt t x :=
  by
  cases t <;> simp [balance2_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance2_gt; assumption'
#align rbnode.find_balance2_node_gt Std.RBNode.find?_balance2Node_gt

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
theorem Std.RBNode.find?_balance2_eqv {l v r t x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (hl : Std.RBNode.IsSearchable lt l (some y) (some v))
    (hr : Std.RBNode.IsSearchable lt r (some v) hi)
    (ht : Std.RBNode.IsSearchable lt t lo (some y)) :
    Std.RBNode.find? lt (Std.RBNode.balance2 l v r y t) x = some y :=
  by
  revert hl hr ht;
  apply balance.cases l v r <;> intros <;> simp [*] <;>
    run_tac
      is_searchable_tactic
  · have := lt_of_incomp_of_lt h (lo_lt_hi hl_hs₁); simp [*]
  · have := lt_of_incomp_of_lt h (lo_lt_hi hl); simp [*]
#align rbnode.find_balance2_eqv Std.RBNode.find?_balance2_eqv

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic rbnode.is_searchable_tactic -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ins_ne_leaf_tac -/
theorem Std.RBNode.find?_balance2Node_eqv {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x)
    (ht : Std.RBNode.IsSearchable lt t (some y) hi) (hs : Std.RBNode.IsSearchable lt s lo (some y))
    (hne : t ≠ Std.RBNode.nil := by
      run_tac
        ins_ne_leaf_tac) :
    Std.RBNode.find? lt (Std.RBNode.balance2Node t y s) x = some y :=
  by
  cases t <;> simp [balance2_node]
  · contradiction
  all_goals intros;
    run_tac
      is_searchable_tactic;
    apply find_balance2_eqv; assumption'
#align rbnode.find_balance2_node_eqv Std.RBNode.find?_balance2Node_eqv

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic _private.3968712505.simp_fi -/
theorem Std.RBNode.find?_ins_of_disj {x y : α} {t : Std.RBNode α} (hn : lt x y ∨ lt y x) :
    ∀ {lo hi} (hs : Std.RBNode.IsSearchable lt t lo hi) (hlt₁ : Std.RBNode.Lift lt lo (some x))
      (hlt₂ : Std.RBNode.Lift lt (some x) hi),
      Std.RBNode.find? lt (Std.RBNode.ins lt t x) y = Std.RBNode.find? lt t y :=
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
#align rbnode.find_ins_of_disj Std.RBNode.find?_ins_of_disj

end FindInsOfNotEqv

theorem Std.RBNode.find?_insert_of_disj [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Std.RBNode α} (hd : lt x y ∨ lt y x) :
    Std.RBNode.IsSearchable lt t none none →
      Std.RBNode.find? lt (Std.RBNode.insert lt t x) y = Std.RBNode.find? lt t y :=
  by
  intro hs
  simp [insert, find_mk_insert_result]
  apply find_ins_of_disj lt hd hs <;> simp
#align rbnode.find_insert_of_disj Std.RBNode.find?_insert_of_disj

theorem Std.RBNode.find?_insert_of_not_eqv [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α}
    {t : Std.RBNode α} (hn : ¬x ≈[lt]y) :
    Std.RBNode.IsSearchable lt t none none →
      Std.RBNode.find? lt (Std.RBNode.insert lt t x) y = Std.RBNode.find? lt t y :=
  by
  intro hs
  simp [insert, find_mk_insert_result]
  have he : lt x y ∨ lt y x :=
    by
    simp [StrictWeakOrder.Equiv, Decidable.not_and_iff_or_not, Decidable.not_not_iff] at hn
    assumption
  apply find_ins_of_disj lt he hs <;> simp
#align rbnode.find_insert_of_not_eqv Std.RBNode.find?_insert_of_not_eqv

end MembershipLemmas

section IsRedBlack

variable {α : Type u}

open Nat Color

inductive Std.RBNode.IsBadRedBlack : Std.RBNode α → Nat → Prop
  |
  bad_red {c₁ c₂ n l r v} (rb_l : Std.RBNode.IsRedBlack l c₁ n)
    (rb_r : Std.RBNode.IsRedBlack r c₂ n) : is_bad_red_black (Std.RBNode.node l v r) n
#align rbnode.is_bad_red_black Std.RBNode.IsBadRedBlack

theorem Std.RBNode.balance1_rb {l r t : Std.RBNode α} {y v : α} {c_l c_r c_t n} :
    Std.RBNode.IsRedBlack l c_l n →
      Std.RBNode.IsRedBlack r c_r n →
        Std.RBNode.IsRedBlack t c_t n →
          ∃ c, Std.RBNode.IsRedBlack (Std.RBNode.balance1 l y r v t) c (succ n) :=
  by
  intro h₁ h₂ _ <;> cases h₁ <;> cases h₂ <;>
    repeat'
      first
      | assumption
      | constructor
#align rbnode.balance1_rb Std.RBNode.balance1_rb

theorem Std.RBNode.balance2_rb {l r t : Std.RBNode α} {y v : α} {c_l c_r c_t n} :
    Std.RBNode.IsRedBlack l c_l n →
      Std.RBNode.IsRedBlack r c_r n →
        Std.RBNode.IsRedBlack t c_t n →
          ∃ c, Std.RBNode.IsRedBlack (Std.RBNode.balance2 l y r v t) c (succ n) :=
  by
  intro h₁ h₂ _ <;> cases h₁ <;> cases h₂ <;>
    repeat'
      first
      | assumption
      | constructor
#align rbnode.balance2_rb Std.RBNode.balance2_rb

theorem Std.RBNode.balance1Node_rb {t s : Std.RBNode α} {y : α} {c n} :
    Std.RBNode.IsBadRedBlack t n →
      Std.RBNode.IsRedBlack s c n →
        ∃ c, Std.RBNode.IsRedBlack (Std.RBNode.balance1Node t y s) c (succ n) :=
  by intro h _ <;> cases h <;> simp [balance1_node] <;> apply balance1_rb <;> assumption'
#align rbnode.balance1_node_rb Std.RBNode.balance1Node_rb

theorem Std.RBNode.balance2Node_rb {t s : Std.RBNode α} {y : α} {c n} :
    Std.RBNode.IsBadRedBlack t n →
      Std.RBNode.IsRedBlack s c n →
        ∃ c, Std.RBNode.IsRedBlack (Std.RBNode.balance2Node t y s) c (succ n) :=
  by intro h _ <;> cases h <;> simp [balance2_node] <;> apply balance2_rb <;> assumption'
#align rbnode.balance2_node_rb Std.RBNode.balance2Node_rb

def Std.RBNode.InsRbResult : Std.RBNode α → RBColor → Nat → Prop
  | t, red, n => Std.RBNode.IsBadRedBlack t n
  | t, black, n => ∃ c, Std.RBNode.IsRedBlack t c n
#align rbnode.ins_rb_result Std.RBNode.InsRbResult

variable {lt : α → α → Prop} [DecidableRel lt]

theorem Std.RBNode.of_getColor_eq_red {t : Std.RBNode α} {c n} :
    Std.RBNode.getColor t = red → Std.RBNode.IsRedBlack t c n → c = red := by intro h₁ h₂;
  cases h₂ <;> simp only [get_color] at h₁ <;> contradiction
#align rbnode.of_get_color_eq_red Std.RBNode.of_getColor_eq_red

theorem Std.RBNode.of_getColor_ne_red {t : Std.RBNode α} {c n} :
    Std.RBNode.getColor t ≠ red → Std.RBNode.IsRedBlack t c n → c = black := by intro h₁ h₂;
  cases h₂ <;> simp only [get_color] at h₁ <;> contradiction
#align rbnode.of_get_color_ne_red Std.RBNode.of_getColor_ne_red

variable (lt)

theorem Std.RBNode.ins_rb {t : Std.RBNode α} (x) :
    ∀ {c n} (h : Std.RBNode.IsRedBlack t c n), Std.RBNode.InsRbResult (Std.RBNode.ins lt t x) c n :=
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
#align rbnode.ins_rb Std.RBNode.ins_rb

def Std.RBNode.InsertRbResult : Std.RBNode α → RBColor → Nat → Prop
  | t, red, n => Std.RBNode.IsRedBlack t black (succ n)
  | t, black, n => ∃ c, Std.RBNode.IsRedBlack t c n
#align rbnode.insert_rb_result Std.RBNode.InsertRbResult

theorem Std.RBNode.insert_rb {t : Std.RBNode α} (x) {c n} (h : Std.RBNode.IsRedBlack t c n) :
    Std.RBNode.InsertRbResult (Std.RBNode.insert lt t x) c n :=
  by
  simp [insert]
  have hi := ins_rb lt x h
  generalize he : ins lt t x = r
  simp [he] at hi
  cases h <;> simp [get_color, ins_rb_result, insert_rb_result, mk_insert_result] at *
  assumption'
  · cases hi; simp [mk_insert_result]; constructor <;> assumption
#align rbnode.insert_rb Std.RBNode.insert_rb

theorem Std.RBNode.insert_isRedBlack {t : Std.RBNode α} {c n} (x) :
    Std.RBNode.IsRedBlack t c n → ∃ c n, Std.RBNode.IsRedBlack (Std.RBNode.insert lt t x) c n :=
  by
  intro h
  have := insert_rb lt x h
  cases c <;> simp [insert_rb_result] at this
  · constructor; constructor; assumption
  · cases this; constructor; constructor; assumption
#align rbnode.insert_is_red_black Std.RBNode.insert_isRedBlack

end IsRedBlack

end Std.RBNode

