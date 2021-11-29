import Mathbin.Data.Rbtree.Find

universe u v

attribute [local simp] Rbnode.Lift

namespace Rbnode

variable {α : Type u}

open Color

@[simp]
theorem balance1_eq₁ (l : Rbnode α) x r₁ y r₂ v t :
  balance1 (red_node l x r₁) y r₂ v t = red_node (black_node l x r₁) y (black_node r₂ v t) :=
  by 
    cases r₂ <;> rfl

@[simp]
theorem balance1_eq₂ (l₁ : Rbnode α) y l₂ x r v t :
  get_color l₁ ≠ red → balance1 l₁ y (red_node l₂ x r) v t = red_node (black_node l₁ y l₂) x (black_node r v t) :=
  by 
    cases l₁ <;> simp [get_color, balance1, false_implies_iff]

@[simp]
theorem balance1_eq₃ (l : Rbnode α) y r v t :
  get_color l ≠ red → get_color r ≠ red → balance1 l y r v t = black_node (red_node l y r) v t :=
  by 
    cases l <;> cases r <;> simp [get_color, balance1, false_implies_iff]

@[simp]
theorem balance2_eq₁ (l : Rbnode α) x₁ r₁ y r₂ v t :
  balance2 (red_node l x₁ r₁) y r₂ v t = red_node (black_node t v l) x₁ (black_node r₁ y r₂) :=
  by 
    cases r₂ <;> rfl

@[simp]
theorem balance2_eq₂ (l₁ : Rbnode α) y l₂ x₂ r₂ v t :
  get_color l₁ ≠ red → balance2 l₁ y (red_node l₂ x₂ r₂) v t = red_node (black_node t v l₁) y (black_node l₂ x₂ r₂) :=
  by 
    cases l₁ <;> simp [get_color, balance2, false_implies_iff]

@[simp]
theorem balance2_eq₃ (l : Rbnode α) y r v t :
  get_color l ≠ red → get_color r ≠ red → balance2 l y r v t = black_node t v (red_node l y r) :=
  by 
    cases l <;> cases r <;> simp [get_color, balance2, false_implies_iff]

theorem balance.cases {p : Rbnode α → α → Rbnode α → Prop} l y r (red_left : ∀ l x r₁ y r₂, p (red_node l x r₁) y r₂)
  (red_right : ∀ l₁ y l₂ x r, get_color l₁ ≠ red → p l₁ y (red_node l₂ x r))
  (other : ∀ l y r, get_color l ≠ red → get_color r ≠ red → p l y r) : p l y r :=
  by 
    cases l <;> cases r 
    any_goals 
      apply red_left 
    any_goals 
      apply red_right <;> simp [get_color] <;> contradiction <;> done 
    any_goals 
      apply other <;> simp [get_color] <;> contradiction <;> done

theorem balance1_ne_leaf (l : Rbnode α) x r v t : balance1 l x r v t ≠ leaf :=
  by 
    apply balance.cases l x r <;> intros  <;> simp  <;> contradiction

theorem balance1_node_ne_leaf {s : Rbnode α} (a : α) (t : Rbnode α) : s ≠ leaf → balance1_node s a t ≠ leaf :=
  by 
    intro h 
    cases s
    ·
      contradiction 
    all_goals 
      simp [balance1_node]
      apply balance1_ne_leaf

theorem balance2_ne_leaf (l : Rbnode α) x r v t : balance2 l x r v t ≠ leaf :=
  by 
    apply balance.cases l x r <;> intros  <;> simp  <;> contradiction

theorem balance2_node_ne_leaf {s : Rbnode α} (a : α) (t : Rbnode α) : s ≠ leaf → balance2_node s a t ≠ leaf :=
  by 
    intro h 
    cases s
    ·
      contradiction 
    all_goals 
      simp [balance2_node]
      apply balance2_ne_leaf

variable (lt : α → α → Prop)

@[elab_as_eliminator]
theorem ins.induction [DecidableRel lt] {p : Rbnode α → Prop} t x (is_leaf : p leaf)
  (is_red_lt : ∀ a y b hc : cmpUsing lt x y = Ordering.lt ih : p a, p (red_node a y b))
  (is_red_eq : ∀ a y b hc : cmpUsing lt x y = Ordering.eq, p (red_node a y b))
  (is_red_gt : ∀ a y b hc : cmpUsing lt x y = Ordering.gt ih : p b, p (red_node a y b))
  (is_black_lt_red : ∀ a y b hc : cmpUsing lt x y = Ordering.lt hr : get_color a = red ih : p a, p (black_node a y b))
  (is_black_lt_not_red :
    ∀ a y b hc : cmpUsing lt x y = Ordering.lt hnr : get_color a ≠ red ih : p a, p (black_node a y b))
  (is_black_eq : ∀ a y b hc : cmpUsing lt x y = Ordering.eq, p (black_node a y b))
  (is_black_gt_red : ∀ a y b hc : cmpUsing lt x y = Ordering.gt hr : get_color b = red ih : p b, p (black_node a y b))
  (is_black_gt_not_red :
    ∀ a y b hc : cmpUsing lt x y = Ordering.gt hnr : get_color b ≠ red ih : p b, p (black_node a y b)) :
  p t :=
  by 
    induction t 
    case leaf => 
      apply is_leaf 
    case red_node a y b => 
      cases h : cmpUsing lt x y 
      case ordering.lt => 
        apply is_red_lt <;> assumption 
      case ordering.eq => 
        apply is_red_eq <;> assumption 
      case ordering.gt => 
        apply is_red_gt <;> assumption 
    case black_node a y b => 
      cases h : cmpUsing lt x y 
      case ordering.lt => 
        byCases' get_color a = red
        ·
          apply is_black_lt_red <;> assumption
        ·
          apply is_black_lt_not_red <;> assumption 
      case ordering.eq => 
        apply is_black_eq <;> assumption 
      case ordering.gt => 
        byCases' get_color b = red
        ·
          apply is_black_gt_red <;> assumption
        ·
          apply is_black_gt_not_red <;> assumption

theorem is_searchable_balance1 {l y r v t lo hi} :
  is_searchable lt l lo (some y) →
    is_searchable lt r (some y) (some v) →
      is_searchable lt t (some v) hi → is_searchable lt (balance1 l y r v t) lo hi :=
  by 
    apply balance.cases l y r <;>
      intros  <;>
        simp  <;>
          runTac 
            is_searchable_tactic

theorem is_searchable_balance1_node {t} [IsTrans α lt] :
  ∀ {y s lo hi},
    is_searchable lt t lo (some y) → is_searchable lt s (some y) hi → is_searchable lt (balance1_node t y s) lo hi :=
  by 
    cases t <;>
      simp  <;>
        intros  <;>
          runTac 
            is_searchable_tactic
    ·
      cases lo
      ·
        apply is_searchable_none_low_of_is_searchable_some_low 
        assumption
      ·
        simp  at *
        apply is_searchable_some_low_of_is_searchable_of_lt <;> assumption 
    all_goals 
      apply is_searchable_balance1 <;> assumption

theorem is_searchable_balance2 {l y r v t lo hi} :
  is_searchable lt t lo (some v) →
    is_searchable lt l (some v) (some y) →
      is_searchable lt r (some y) hi → is_searchable lt (balance2 l y r v t) lo hi :=
  by 
    apply balance.cases l y r <;>
      intros  <;>
        simp  <;>
          runTac 
            is_searchable_tactic

theorem is_searchable_balance2_node {t} [IsTrans α lt] :
  ∀ {y s lo hi},
    is_searchable lt s lo (some y) → is_searchable lt t (some y) hi → is_searchable lt (balance2_node t y s) lo hi :=
  by 
    induction t <;>
      simp  <;>
        intros  <;>
          runTac 
            is_searchable_tactic
    ·
      cases hi
      ·
        apply is_searchable_none_high_of_is_searchable_some_high 
        assumption
      ·
        simp  at *
        apply is_searchable_some_high_of_is_searchable_of_lt 
        assumption' 
    all_goals 
      apply is_searchable_balance2 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_searchable_ins
[decidable_rel lt]
{t x}
[is_strict_weak_order α lt] : ∀
{lo hi}
(h : is_searchable lt t lo hi), lift lt lo (some x) → lift lt (some x) hi → is_searchable lt (ins lt t x) lo hi :=
begin
  with_cases { apply [expr ins.induction lt t x]; intros []; simp ["!"] [] [] ["[", "*", "]"] [] ["at", "*"] { eta := ff }; is_searchable_tactic },
  case [ident is_red_lt, ident hs₁] { apply [expr ih h_hs₁],
    assumption,
    simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident is_red_eq, ident hs₁] { apply [expr is_searchable_of_is_searchable_of_incomp hc],
    assumption },
  case [ident is_red_eq, ident hs₂] { apply [expr is_searchable_of_incomp_of_is_searchable hc],
    assumption },
  case [ident is_red_gt, ident hs₂] { apply [expr ih h_hs₂],
    cases [expr hi] []; simp [] [] [] ["[", "*", "]"] [] [],
    assumption },
  case [ident is_black_lt_red] { apply [expr is_searchable_balance1_node],
    apply [expr ih h_hs₁],
    assumption,
    simp [] [] [] ["[", "*", "]"] [] [],
    assumption },
  case [ident is_black_lt_not_red, ident hs₁] { apply [expr ih h_hs₁],
    assumption,
    simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident is_black_eq, ident hs₁] { apply [expr is_searchable_of_is_searchable_of_incomp hc],
    assumption },
  case [ident is_black_eq, ident hs₂] { apply [expr is_searchable_of_incomp_of_is_searchable hc],
    assumption },
  case [ident is_black_gt_red] { apply [expr is_searchable_balance2_node],
    assumption,
    apply [expr ih h_hs₂],
    simp [] [] [] ["[", "*", "]"] [] [],
    assumption },
  case [ident is_black_gt_not_red, ident hs₂] { apply [expr ih h_hs₂],
    assumption,
    simp [] [] [] ["[", "*", "]"] [] [] }
end

theorem is_searchable_mk_insert_result {c t} :
  is_searchable lt t none none → is_searchable lt (mk_insert_result c t) none none :=
  by 
    classical 
    cases c <;> cases t <;> simp [mk_insert_result]
    ·
      intro h 
      runTac 
        is_searchable_tactic

theorem is_searchable_insert [DecidableRel lt] {t x} [IsStrictWeakOrder α lt] :
  is_searchable lt t none none → is_searchable lt (insert lt t x) none none :=
  by 
    intro h 
    simp [insert]
    apply is_searchable_mk_insert_result 
    apply is_searchable_ins <;>
      ·
        first |
          assumption|
          simp 

end Rbnode

namespace Rbnode

section MembershipLemmas

parameter {α : Type u}(lt : α → α → Prop)

attribute [local simp] mem balance1_node balance2_node

local infixl:0 "∈" => mem lt

theorem mem_balance1_node_of_mem_left {x s} v (t : Rbnode α) : (x∈s) → (x∈balance1_node s v t) :=
  by 
    cases s <;> simp [false_implies_iff]
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp  at * <;> casesType* or.1 <;> simp 

theorem mem_balance2_node_of_mem_left {x s} v (t : Rbnode α) : (x∈s) → (x∈balance2_node s v t) :=
  by 
    cases s <;> simp [false_implies_iff]
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp  at * <;> casesType* or.1 <;> simp 

theorem mem_balance1_node_of_mem_right {x t} v (s : Rbnode α) : (x∈t) → (x∈balance1_node s v t) :=
  by 
    intros 
    cases s <;> simp 
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp 

theorem mem_balance2_node_of_mem_right {x t} v (s : Rbnode α) : (x∈t) → (x∈balance2_node s v t) :=
  by 
    intros 
    cases s <;> simp 
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp 

theorem mem_balance1_node_of_incomp {x v} s t : ¬lt x v ∧ ¬lt v x → s ≠ leaf → (x∈balance1_node s v t) :=
  by 
    intros 
    cases s <;> simp 
    ·
      contradiction 
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp 

theorem mem_balance2_node_of_incomp {x v} s t : ¬lt v x ∧ ¬lt x v → s ≠ leaf → (x∈balance2_node s v t) :=
  by 
    intros 
    cases s <;> simp 
    ·
      contradiction 
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp 

theorem ins_ne_leaf [DecidableRel lt] (t : Rbnode α) (x : α) : t.ins lt x ≠ leaf :=
  by 
    apply ins.induction lt t x 
    any_goals 
      intros 
      simp [ins]
    ·
      intros 
      apply balance1_node_ne_leaf 
      assumption
    ·
      intros 
      apply balance2_node_ne_leaf 
      assumption

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_ne_leaf [decidable_rel lt] (t : rbnode α) (x : α) : «expr ≠ »(insert lt t x, leaf) :=
begin
  simp [] [] [] ["[", expr insert, "]"] [] [],
  cases [expr he, ":", expr ins lt t x] []; cases [expr get_color t] []; simp [] [] [] ["[", expr mk_insert_result, "]"] [] [],
  { have [] [] [":=", expr ins_ne_leaf lt t x],
    contradiction },
  { exact [expr absurd he (ins_ne_leaf _ _ _)] }
end

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_ins_of_incomp
[decidable_rel lt]
(t : rbnode α)
{x y : α} : ∀ h : «expr ∧ »(«expr¬ »(lt x y), «expr¬ »(lt y x)), «expr ∈ »(x, t.ins lt y) :=
begin
  with_cases { apply [expr ins.induction lt t y]; intros []; simp [] [] [] ["[", expr ins, ",", "*", "]"] [] [] },
  case [ident is_black_lt_red] { have [] [] [":=", expr ih h],
    apply [expr mem_balance1_node_of_mem_left],
    assumption },
  case [ident is_black_gt_red] { have [] [] [":=", expr ih h],
    apply [expr mem_balance2_node_of_mem_left],
    assumption }
end

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_ins_of_mem
[decidable_rel lt]
[is_strict_weak_order α lt]
{t : rbnode α}
(z : α) : ∀ {x} (h : «expr ∈ »(x, t)), «expr ∈ »(x, t.ins lt z) :=
begin
  with_cases { apply [expr ins.induction lt t z]; intros []; simp [] [] [] ["[", expr ins, ",", "*", "]"] [] ["at", "*"]; try { contradiction }; blast_disjs },
  case [ident is_red_eq, ident or.inr, ident or.inl] { have [] [] [":=", expr incomp_trans_of lt h ⟨hc.2, hc.1⟩],
    simp [] [] [] ["[", expr this, "]"] [] [] },
  case [ident is_black_lt_red, ident or.inl] { apply [expr mem_balance1_node_of_mem_left],
    apply [expr ih h] },
  case [ident is_black_lt_red, ident or.inr, ident or.inl] { apply [expr mem_balance1_node_of_incomp],
    cases [expr h] [],
    all_goals { simp [] [] [] ["[", "*", ",", expr ins_ne_leaf lt a z, "]"] [] [] } },
  case [ident is_black_lt_red, ident or.inr, ident or.inr] { apply [expr mem_balance1_node_of_mem_right],
    assumption },
  case [ident is_black_eq, ident or.inr, ident or.inl] { have [] [] [":=", expr incomp_trans_of lt hc ⟨h.2, h.1⟩],
    simp [] [] [] ["[", expr this, "]"] [] [] },
  case [ident is_black_gt_red, ident or.inl] { apply [expr mem_balance2_node_of_mem_right],
    assumption },
  case [ident is_black_gt_red, ident or.inr, ident or.inl] { have [] [] [":=", expr ins_ne_leaf lt a z],
    apply [expr mem_balance2_node_of_incomp],
    cases [expr h] [],
    simp [] [] [] ["[", "*", "]"] [] [],
    apply [expr ins_ne_leaf] },
  case [ident is_black_gt_red, ident or.inr, ident or.inr] { apply [expr mem_balance2_node_of_mem_left],
    apply [expr ih h] },
  any_goals { intros [],
    simp [] [] [] ["[", expr h, "]"] [] [],
    done },
  all_goals { intros [],
    simp [] [] [] ["[", expr ih h, "]"] [] [],
    done }
end

theorem mem_mk_insert_result {a t} c : mem lt a t → mem lt a (mk_insert_result c t) :=
  by 
    intros  <;> cases c <;> cases t <;> simp_all [mk_insert_result, mem]

theorem mem_of_mem_mk_insert_result {a t c} : mem lt a (mk_insert_result c t) → mem lt a t :=
  by 
    cases t <;> cases c <;> simp [mk_insert_result, mem] <;> intros  <;> assumption

theorem mem_insert_of_incomp [DecidableRel lt] (t : Rbnode α) {x y : α} : ∀ h : ¬lt x y ∧ ¬lt y x, x∈t.insert lt y :=
  by 
    intros  <;> unfold insert <;> apply mem_mk_insert_result <;> apply mem_ins_of_incomp <;> assumption

theorem mem_insert_of_mem [DecidableRel lt] [IsStrictWeakOrder α lt] {t x} z : (x∈t) → (x∈t.insert lt z) :=
  by 
    intros  <;> apply mem_mk_insert_result <;> apply mem_ins_of_mem <;> assumption

theorem of_mem_balance1_node {x s v t} : (x∈balance1_node s v t) → (x∈s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x∈t) :=
  by 
    cases s <;> simp 
    ·
      intros 
      simp 
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp_all  <;> casesType* or.1 <;> simp 

theorem of_mem_balance2_node {x s v t} : (x∈balance2_node s v t) → (x∈s) ∨ ¬lt x v ∧ ¬lt v x ∨ (x∈t) :=
  by 
    cases s <;> simp 
    ·
      intros 
      simp 
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp_all  <;> casesType* or.1 <;> simp 

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem equiv_or_mem_of_mem_ins
[decidable_rel lt]
[is_strict_weak_order α lt]
{t : rbnode α}
{x z} : ∀ h : «expr ∈ »(x, t.ins lt z), «expr ∨ »(«expr ≈[ ] »(x, lt, z), «expr ∈ »(x, t)) :=
begin
  with_cases { apply [expr ins.induction lt t z]; intros []; simp [] [] [] ["[", expr ins, ",", expr strict_weak_order.equiv, ",", "*", "]"] [] ["at", "*"]; blast_disjs },
  case [ident is_black_lt_red] { have [ident h'] [] [":=", expr of_mem_balance1_node lt h],
    blast_disjs,
    have [] [] [":=", expr ih h'],
    blast_disjs,
    all_goals { simp [] [] [] ["[", expr h, ",", "*", "]"] [] [] } },
  case [ident is_black_gt_red] { have [ident h'] [] [":=", expr of_mem_balance2_node lt h],
    blast_disjs,
    have [] [] [":=", expr ih h'],
    blast_disjs,
    all_goals { simp [] [] [] ["[", expr h, ",", "*", "]"] [] [] } },
  any_goals { intros [],
    simp [] [] [] ["[", expr h, "]"] [] [] },
  all_goals { intros [],
    have [ident ih] [] [":=", expr ih h],
    cases [expr ih] []; simp [] [] [] ["[", "*", "]"] [] [],
    done }
end

theorem equiv_or_mem_of_mem_insert [DecidableRel lt] [IsStrictWeakOrder α lt] {t : Rbnode α} {x z} :
  ∀ h : x∈t.insert lt z, x ≈[lt]z ∨ (x∈t) :=
  by 
    simp [insert]
    intros 
    apply equiv_or_mem_of_mem_ins 
    exact mem_of_mem_mk_insert_result lt h

attribute [local simp] mem_exact

theorem mem_exact_balance1_node_of_mem_exact {x s} v (t : Rbnode α) :
  mem_exact x s → mem_exact x (balance1_node s v t) :=
  by 
    cases s <;> simp [false_implies_iff]
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp_all  <;> casesType* or.1 <;> simp 

theorem mem_exact_balance2_node_of_mem_exact {x s} v (t : Rbnode α) :
  mem_exact x s → mem_exact x (balance2_node s v t) :=
  by 
    cases s <;> simp [false_implies_iff]
    all_goals 
      apply balance.cases s_lchild s_val s_rchild <;> intros  <;> simp_all  <;> casesType* or.1 <;> simp 

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance1_node
[decidable_rel lt]
[is_strict_weak_order α lt]
{x
 y
 z
 t
 s} : ∀
{lo
 hi}, is_searchable lt t lo (some z) → is_searchable lt s (some z) hi → «expr = »(find lt t y, some x) → «expr ≈[ ] »(y, lt, x) → «expr = »(find lt (balance1_node t z s) y, some x) :=
begin
  intros ["_", "_", ident hs₁, ident hs₂, ident heq, ident heqv],
  have [ident hs] [] [":=", expr is_searchable_balance1_node lt hs₁ hs₂],
  have [] [] [":=", expr eq.trans (find_eq_find_of_eqv hs₁ heqv.symm) heq],
  have [] [] [":=", expr iff.mpr (find_correct_exact hs₁) this],
  have [] [] [":=", expr mem_exact_balance1_node_of_mem_exact z s this],
  have [] [] [":=", expr iff.mp (find_correct_exact hs) this],
  exact [expr eq.trans (find_eq_find_of_eqv hs heqv) this]
end

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance2_node
[decidable_rel lt]
[is_strict_weak_order α lt]
{x y z s t}
[is_trans α lt] : ∀
{lo
 hi}, is_searchable lt s lo (some z) → is_searchable lt t (some z) hi → «expr = »(find lt t y, some x) → «expr ≈[ ] »(y, lt, x) → «expr = »(find lt (balance2_node t z s) y, some x) :=
begin
  intros ["_", "_", ident hs₁, ident hs₂, ident heq, ident heqv],
  have [ident hs] [] [":=", expr is_searchable_balance2_node lt hs₁ hs₂],
  have [] [] [":=", expr eq.trans (find_eq_find_of_eqv hs₂ heqv.symm) heq],
  have [] [] [":=", expr iff.mpr (find_correct_exact hs₂) this],
  have [] [] [":=", expr mem_exact_balance2_node_of_mem_exact z s this],
  have [] [] [":=", expr iff.mp (find_correct_exact hs) this],
  exact [expr eq.trans (find_eq_find_of_eqv hs heqv) this]
end

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ite_eq_of_not_lt
[decidable_rel lt]
[is_strict_order α lt]
{a b}
{β : Type v}
(t s : β)
(h : lt b a) : «expr = »(if lt a b then t else s, s) :=
begin
  have [] [] [":=", expr not_lt_of_lt h],
  simp [] [] [] ["[", "*", "]"] [] []
end

attribute [local simp] ite_eq_of_not_lt

private unsafe def simp_fi : tactic Unit :=
  sorry

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_ins_of_eqv
[decidable_rel lt]
[is_strict_weak_order α lt]
{x y : α}
{t : rbnode α}
(he : «expr ≈[ ] »(x, lt, y)) : ∀
{lo hi}
(hs : is_searchable lt t lo hi)
(hlt₁ : lift lt lo (some x))
(hlt₂ : lift lt (some x) hi), «expr = »(find lt (ins lt t x) y, some x) :=
begin
  simp [] [] [] ["[", expr strict_weak_order.equiv, "]"] [] ["at", ident he],
  apply [expr ins.induction lt t x]; intros [],
  { simp_fi },
  all_goals { simp [] [] [] [] [] ["at", ident hc],
    cases [expr hs] [] },
  { have [] [] [":=", expr lt_of_incomp_of_lt he.swap hc],
    have [] [] [":=", expr ih hs_hs₁ hlt₁ hc],
    simp_fi },
  { simp_fi },
  { have [] [] [":=", expr lt_of_lt_of_incomp hc he],
    have [] [] [":=", expr ih hs_hs₂ hc hlt₂],
    simp_fi },
  { simp_fi,
    have [] [] [":=", expr is_searchable_ins lt hs_hs₁ hlt₁ hc],
    apply [expr find_balance1_node lt this hs_hs₂ (ih hs_hs₁ hlt₁ hc) he.symm] },
  { have [] [] [":=", expr lt_of_incomp_of_lt he.swap hc],
    have [] [] [":=", expr ih hs_hs₁ hlt₁ hc],
    simp_fi },
  { simp_fi },
  { simp_fi,
    have [] [] [":=", expr is_searchable_ins lt hs_hs₂ hc hlt₂],
    apply [expr find_balance2_node lt hs_hs₁ this (ih hs_hs₂ hc hlt₂) he.symm] },
  { have [] [] [":=", expr lt_of_lt_of_incomp hc he],
    have [] [] [":=", expr ih hs_hs₂ hc hlt₂],
    simp_fi }
end

theorem find_mk_insert_result [DecidableRel lt] (c : color) (t : Rbnode α) (x : α) :
  find lt (mk_insert_result c t) x = find lt t x :=
  by 
    cases t <;> cases c <;> simp [mk_insert_result]
    ·
      simp [find]
      cases cmpUsing lt x t_val <;> simp [find]

theorem find_insert_of_eqv [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α} {t : Rbnode α} (he : x ≈[lt]y) :
  is_searchable lt t none none → find lt (insert lt t x) y = some x :=
  by 
    intro hs 
    simp [insert, find_mk_insert_result]
    apply find_ins_of_eqv lt he hs <;> simp 

theorem weak_trichotomous x y {p : Prop} (is_lt : ∀ h : lt x y, p) (is_eqv : ∀ h : ¬lt x y ∧ ¬lt y x, p)
  (is_gt : ∀ h : lt y x, p) : p :=
  by 
    byCases' lt x y <;> byCases' lt y x 
    any_goals 
      apply is_lt <;> assumption 
    any_goals 
      apply is_gt <;> assumption 
    any_goals 
      apply is_eqv 
      constructor <;> assumption

section FindInsOfNotEqv

section SimpAuxLemmas

theorem find_black_eq_find_red [DecidableRel lt] {l y r x} :
  find lt (black_node l y r) x = find lt (red_node l y r) x :=
  by 
    simp [find]
    all_goals 
      cases cmpUsing lt x y <;> simp [find]

theorem find_red_of_lt [DecidableRel lt] {l y r x} (h : lt x y) : find lt (red_node l y r) x = find lt l x :=
  by 
    simp [find, cmpUsing]

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_red_of_gt
[decidable_rel lt]
[is_strict_order α lt]
{l y r x}
(h : lt y x) : «expr = »(find lt (red_node l y r) x, find lt r x) :=
begin
  have [] [] [":=", expr not_lt_of_lt h],
  simp [] [] [] ["[", expr find, ",", expr cmp_using, ",", "*", "]"] [] []
end

theorem find_red_of_incomp [DecidableRel lt] {l y r x} (h : ¬lt x y ∧ ¬lt y x) : find lt (red_node l y r) x = some y :=
  by 
    simp [find, cmpUsing]

end SimpAuxLemmas

attribute [local simp] find_black_eq_find_red find_red_of_lt find_red_of_lt find_red_of_gt find_red_of_incomp

variable [IsStrictWeakOrder α lt] [DecidableRel lt]

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance1_lt
{l r t v x y lo hi}
(h : lt x y)
(hl : is_searchable lt l lo (some v))
(hr : is_searchable lt r (some v) (some y))
(ht : is_searchable lt t (some y) hi) : «expr = »(find lt (balance1 l v r y t) x, find lt (red_node l v r) x) :=
begin
  with_cases { revert [ident hl, ident hr, ident ht],
    apply [expr balance.cases l v r]; intros []; simp [] [] [] ["[", "*", "]"] [] []; is_searchable_tactic },
  case [ident red_left, ":", "_", "_", "_", ident z, ident r] { apply [expr weak_trichotomous lt z x]; intros []; simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident red_right, ":", ident l_left, ident l_val, ident l_right, ident z, ident r] { with_cases { apply [expr weak_trichotomous lt z x]; intro [ident h'] },
    case [ident is_lt] { have [] [] [":=", expr trans_of lt (lo_lt_hi hr_hs₁) h'],
      simp [] [] [] ["[", "*", "]"] [] [] },
    case [ident is_eqv] { have [] [":", expr lt l_val x] [":=", expr lt_of_lt_of_incomp (lo_lt_hi hr_hs₁) h'],
      simp [] [] [] ["[", "*", "]"] [] [] },
    case [ident is_gt] { apply [expr weak_trichotomous lt l_val x]; intros []; simp [] [] [] ["[", "*", "]"] [] [] } }
end

unsafe def ins_ne_leaf_tac :=
  sorry

theorem find_balance1_node_lt {t s x y lo hi} (hlt : lt y x) (ht : is_searchable lt t lo (some x))
  (hs : is_searchable lt s (some x) hi)
  (hne : t ≠ leaf :=  by 
    runTac 
      ins_ne_leaf_tac) :
  find lt (balance1_node t x s) y = find lt t y :=
  by 
    cases t <;> simp [balance1_node]
    ·
      contradiction 
    all_goals 
      intros 
      runTac 
        is_searchable_tactic 
      apply find_balance1_lt 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance1_gt
{l r t v x y lo hi}
(h : lt y x)
(hl : is_searchable lt l lo (some v))
(hr : is_searchable lt r (some v) (some y))
(ht : is_searchable lt t (some y) hi) : «expr = »(find lt (balance1 l v r y t) x, find lt t x) :=
begin
  with_cases { revert [ident hl, ident hr, ident ht],
    apply [expr balance.cases l v r]; intros []; simp [] [] [] ["[", "*", "]"] [] []; is_searchable_tactic },
  case [ident red_left, ":", "_", "_", "_", ident z] { have [] [] [":=", expr trans_of lt (lo_lt_hi hr) h],
    simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident red_right, ":", "_", "_", "_", ident z] { have [] [] [":=", expr trans_of lt (lo_lt_hi hr_hs₂) h],
    simp [] [] [] ["[", "*", "]"] [] [] }
end

theorem find_balance1_node_gt {t s x y lo hi} (h : lt x y) (ht : is_searchable lt t lo (some x))
  (hs : is_searchable lt s (some x) hi)
  (hne : t ≠ leaf :=  by 
    runTac 
      ins_ne_leaf_tac) :
  find lt (balance1_node t x s) y = find lt s y :=
  by 
    cases t <;> simp [balance1_node]
    all_goals 
      intros 
      runTac 
        is_searchable_tactic 
      apply find_balance1_gt 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance1_eqv
{l r t v x y lo hi}
(h : «expr ∧ »(«expr¬ »(lt x y), «expr¬ »(lt y x)))
(hl : is_searchable lt l lo (some v))
(hr : is_searchable lt r (some v) (some y))
(ht : is_searchable lt t (some y) hi) : «expr = »(find lt (balance1 l v r y t) x, some y) :=
begin
  with_cases { revert [ident hl, ident hr, ident ht],
    apply [expr balance.cases l v r]; intros []; simp [] [] [] ["[", "*", "]"] [] []; is_searchable_tactic },
  case [ident red_left, ":", "_", "_", "_", ident z] { have [] [":", expr lt z x] [":=", expr lt_of_lt_of_incomp (lo_lt_hi hr) h.swap],
    simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident red_right, ":", "_", "_", "_", ident z] { have [] [":", expr lt z x] [":=", expr lt_of_lt_of_incomp (lo_lt_hi hr_hs₂) h.swap],
    simp [] [] [] ["[", "*", "]"] [] [] }
end

theorem find_balance1_node_eqv {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x) (ht : is_searchable lt t lo (some y))
  (hs : is_searchable lt s (some y) hi)
  (hne : t ≠ leaf :=  by 
    runTac 
      ins_ne_leaf_tac) :
  find lt (balance1_node t y s) x = some y :=
  by 
    cases t <;> simp [balance1_node]
    ·
      contradiction 
    all_goals 
      intros 
      runTac 
        is_searchable_tactic 
      apply find_balance1_eqv 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance2_lt
{l v r t x y lo hi}
(h : lt x y)
(hl : is_searchable lt l (some y) (some v))
(hr : is_searchable lt r (some v) hi)
(ht : is_searchable lt t lo (some y)) : «expr = »(find lt (balance2 l v r y t) x, find lt t x) :=
begin
  with_cases { revert [ident hl, ident hr, ident ht],
    apply [expr balance.cases l v r]; intros []; simp [] [] [] ["[", "*", "]"] [] []; is_searchable_tactic },
  case [ident red_left] { have [] [] [":=", expr trans h (lo_lt_hi hl_hs₁)],
    simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident red_right] { have [] [] [":=", expr trans h (lo_lt_hi hl)],
    simp [] [] [] ["[", "*", "]"] [] [] }
end

theorem find_balance2_node_lt {s t x y lo hi} (h : lt x y) (ht : is_searchable lt t (some y) hi)
  (hs : is_searchable lt s lo (some y))
  (hne : t ≠ leaf :=  by 
    runTac 
      ins_ne_leaf_tac) :
  find lt (balance2_node t y s) x = find lt s x :=
  by 
    cases t <;> simp [balance2_node]
    all_goals 
      intros 
      runTac 
        is_searchable_tactic 
      apply find_balance2_lt 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance2_gt
{l v r t x y lo hi}
(h : lt y x)
(hl : is_searchable lt l (some y) (some v))
(hr : is_searchable lt r (some v) hi)
(ht : is_searchable lt t lo (some y)) : «expr = »(find lt (balance2 l v r y t) x, find lt (red_node l v r) x) :=
begin
  with_cases { revert [ident hl, ident hr, ident ht],
    apply [expr balance.cases l v r]; intros []; simp [] [] [] ["[", "*", "]"] [] []; is_searchable_tactic },
  case [ident red_left, ":", "_", ident val, "_", ident z] { with_cases { apply [expr weak_trichotomous lt val x]; intro [ident h']; simp [] [] [] ["[", "*", "]"] [] [] },
    case [ident is_lt] { apply [expr weak_trichotomous lt z x]; intros []; simp [] [] [] ["[", "*", "]"] [] [] },
    case [ident is_eqv] { have [] [":", expr lt x z] [":=", expr lt_of_incomp_of_lt h'.swap (lo_lt_hi hl_hs₂)],
      simp [] [] [] ["[", "*", "]"] [] [] },
    case [ident is_gt] { have [] [] [":=", expr trans h' (lo_lt_hi hl_hs₂)],
      simp [] [] [] ["[", "*", "]"] [] [] } },
  case [ident red_right, ":", "_", ident val] { apply [expr weak_trichotomous lt val x]; intros []; simp [] [] [] ["[", "*", "]"] [] [] }
end

theorem find_balance2_node_gt {s t x y lo hi} (h : lt y x) (ht : is_searchable lt t (some y) hi)
  (hs : is_searchable lt s lo (some y))
  (hne : t ≠ leaf :=  by 
    runTac 
      ins_ne_leaf_tac) :
  find lt (balance2_node t y s) x = find lt t x :=
  by 
    cases t <;> simp [balance2_node]
    ·
      contradiction 
    all_goals 
      intros 
      runTac 
        is_searchable_tactic 
      apply find_balance2_gt 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_balance2_eqv
{l v r t x y lo hi}
(h : «expr ∧ »(«expr¬ »(lt x y), «expr¬ »(lt y x)))
(hl : is_searchable lt l (some y) (some v))
(hr : is_searchable lt r (some v) hi)
(ht : is_searchable lt t lo (some y)) : «expr = »(find lt (balance2 l v r y t) x, some y) :=
begin
  with_cases { revert [ident hl, ident hr, ident ht],
    apply [expr balance.cases l v r]; intros []; simp [] [] [] ["[", "*", "]"] [] []; is_searchable_tactic },
  case [ident red_left] { have [] [] [":=", expr lt_of_incomp_of_lt h (lo_lt_hi hl_hs₁)],
    simp [] [] [] ["[", "*", "]"] [] [] },
  case [ident red_right] { have [] [] [":=", expr lt_of_incomp_of_lt h (lo_lt_hi hl)],
    simp [] [] [] ["[", "*", "]"] [] [] }
end

theorem find_balance2_node_eqv {t s x y lo hi} (h : ¬lt x y ∧ ¬lt y x) (ht : is_searchable lt t (some y) hi)
  (hs : is_searchable lt s lo (some y))
  (hne : t ≠ leaf :=  by 
    runTac 
      ins_ne_leaf_tac) :
  find lt (balance2_node t y s) x = some y :=
  by 
    cases t <;> simp [balance2_node]
    ·
      contradiction 
    all_goals 
      intros 
      runTac 
        is_searchable_tactic 
      apply find_balance2_eqv 
      assumption'

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_ins_of_disj
{x y : α}
{t : rbnode α}
(hn : «expr ∨ »(lt x y, lt y x)) : ∀
{lo hi}
(hs : is_searchable lt t lo hi)
(hlt₁ : lift lt lo (some x))
(hlt₂ : lift lt (some x) hi), «expr = »(find lt (ins lt t x) y, find lt t y) :=
begin
  apply [expr ins.induction lt t x]; intros [],
  { cases [expr hn] [],
    all_goals { simp [] [] [] ["[", expr find, ",", expr ins, ",", expr cmp_using, ",", "*", "]"] [] [] } },
  all_goals { simp [] [] [] [] [] ["at", ident hc],
    cases [expr hs] [] },
  { have [] [] [":=", expr ih hs_hs₁ hlt₁ hc],
    simp_fi },
  { cases [expr hn] [],
    { have [] [] [":=", expr lt_of_incomp_of_lt hc.symm hn],
      simp_fi },
    { have [] [] [":=", expr lt_of_lt_of_incomp hn hc],
      simp_fi } },
  { have [] [] [":=", expr ih hs_hs₂ hc hlt₂],
    cases [expr hn] [],
    { have [] [] [":=", expr trans hc hn],
      simp_fi },
    { simp_fi } },
  { have [ident ih] [] [":=", expr ih hs_hs₁ hlt₁ hc],
    cases [expr hn] [],
    { cases [expr hc', ":", expr cmp_using lt y y_1] []; simp [] [] [] [] [] ["at", ident hc'],
      { have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₁ hlt₁ (trans_of lt hn hc')],
        have [] [] [":=", expr find_balance1_node_lt lt hc' hsi hs_hs₂],
        simp_fi },
      { have [ident hlt] [] [":=", expr lt_of_lt_of_incomp hn hc'],
        have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₁ hlt₁ hlt],
        have [] [] [":=", expr find_balance1_node_eqv lt hc' hsi hs_hs₂],
        simp_fi },
      { have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₁ hlt₁ hc],
        have [] [] [":=", expr find_balance1_node_gt lt hc' hsi hs_hs₂],
        simp [] [] [] ["[", "*", "]"] [] [],
        simp_fi } },
    { have [ident hlt] [] [":=", expr trans hn hc],
      have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₁ hlt₁ hc],
      have [] [] [":=", expr find_balance1_node_lt lt hlt hsi hs_hs₂],
      simp_fi } },
  { have [] [] [":=", expr ih hs_hs₁ hlt₁ hc],
    simp_fi },
  { cases [expr hn] [],
    { have [] [] [":=", expr lt_of_incomp_of_lt hc.swap hn],
      simp_fi },
    { have [] [] [":=", expr lt_of_lt_of_incomp hn hc],
      simp_fi } },
  { have [ident ih] [] [":=", expr ih hs_hs₂ hc hlt₂],
    cases [expr hn] [],
    { have [ident hlt] [] [":=", expr trans hc hn],
      simp_fi,
      have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₂ hc hlt₂],
      have [] [] [":=", expr find_balance2_node_gt lt hlt hsi hs_hs₁],
      simp_fi },
    { simp_fi,
      cases [expr hc', ":", expr cmp_using lt y y_1] []; simp [] [] [] [] [] ["at", ident hc'],
      { have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₂ hc hlt₂],
        have [] [] [":=", expr find_balance2_node_lt lt hc' hsi hs_hs₁],
        simp_fi },
      { have [ident hlt] [] [":=", expr lt_of_incomp_of_lt hc'.swap hn],
        have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₂ hlt hlt₂],
        have [] [] [":=", expr find_balance2_node_eqv lt hc' hsi hs_hs₁],
        simp_fi },
      { have [ident hsi] [] [":=", expr is_searchable_ins lt hs_hs₂ hc hlt₂],
        have [] [] [":=", expr find_balance2_node_gt lt hc' hsi hs_hs₁],
        simp_fi } } },
  { cases [expr hn] [],
    { have [] [] [":=", expr trans hc hn],
      have [] [] [":=", expr ih hs_hs₂ hc hlt₂],
      simp_fi },
    { have [ident ih] [] [":=", expr ih hs_hs₂ hc hlt₂],
      simp_fi } }
end

end FindInsOfNotEqv

theorem find_insert_of_disj [DecidableRel lt] [IsStrictWeakOrder α lt] {x y : α} {t : Rbnode α} (hd : lt x y ∨ lt y x) :
  is_searchable lt t none none → find lt (insert lt t x) y = find lt t y :=
  by 
    intro hs 
    simp [insert, find_mk_insert_result]
    apply find_ins_of_disj lt hd hs <;> simp 

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_insert_of_not_eqv
[decidable_rel lt]
[is_strict_weak_order α lt]
{x y : α}
{t : rbnode α}
(hn : «expr¬ »(«expr ≈[ ] »(x, lt, y))) : is_searchable lt t none none → «expr = »(find lt (insert lt t x) y, find lt t y) :=
begin
  intro [ident hs],
  simp [] [] [] ["[", expr insert, ",", expr find_mk_insert_result, "]"] [] [],
  have [ident he] [":", expr «expr ∨ »(lt x y, lt y x)] [],
  { simp [] [] [] ["[", expr strict_weak_order.equiv, ",", expr decidable.not_and_iff_or_not, ",", expr decidable.not_not_iff, "]"] [] ["at", ident hn],
    assumption },
  apply [expr find_ins_of_disj lt he hs]; simp [] [] [] [] [] []
end

end MembershipLemmas

section IsRedBlack

variable {α : Type u}

open Nat Color

inductive is_bad_red_black : Rbnode α → Nat → Prop
  | bad_red {c₁ c₂ n l r v} (rb_l : is_red_black l c₁ n) (rb_r : is_red_black r c₂ n) :
  is_bad_red_black (red_node l v r) n

theorem balance1_rb {l r t : Rbnode α} {y v : α} {c_l c_r c_t n} :
  is_red_black l c_l n →
    is_red_black r c_r n → is_red_black t c_t n → ∃ c, is_red_black (balance1 l y r v t) c (succ n) :=
  by 
    intro h₁ h₂ _ <;>
      cases h₁ <;>
        cases h₂ <;>
          repeat' 
            first |
              assumption|
              constructor

theorem balance2_rb {l r t : Rbnode α} {y v : α} {c_l c_r c_t n} :
  is_red_black l c_l n →
    is_red_black r c_r n → is_red_black t c_t n → ∃ c, is_red_black (balance2 l y r v t) c (succ n) :=
  by 
    intro h₁ h₂ _ <;>
      cases h₁ <;>
        cases h₂ <;>
          repeat' 
            first |
              assumption|
              constructor

theorem balance1_node_rb {t s : Rbnode α} {y : α} {c n} :
  is_bad_red_black t n → is_red_black s c n → ∃ c, is_red_black (balance1_node t y s) c (succ n) :=
  by 
    intro h _ <;> cases h <;> simp [balance1_node] <;> apply balance1_rb <;> assumption'

theorem balance2_node_rb {t s : Rbnode α} {y : α} {c n} :
  is_bad_red_black t n → is_red_black s c n → ∃ c, is_red_black (balance2_node t y s) c (succ n) :=
  by 
    intro h _ <;> cases h <;> simp [balance2_node] <;> apply balance2_rb <;> assumption'

def ins_rb_result : Rbnode α → color → Nat → Prop
| t, red, n => is_bad_red_black t n
| t, black, n => ∃ c, is_red_black t c n

variable {lt : α → α → Prop} [DecidableRel lt]

theorem of_get_color_eq_red {t : Rbnode α} {c n} : get_color t = red → is_red_black t c n → c = red :=
  by 
    intro h₁ h₂ 
    cases h₂ <;> simp [get_color] at h₁ <;> contradiction

theorem of_get_color_ne_red {t : Rbnode α} {c n} : get_color t ≠ red → is_red_black t c n → c = black :=
  by 
    intro h₁ h₂ 
    cases h₂ <;> simp [get_color] at h₁ <;> contradiction

variable (lt)

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ins_rb {t : rbnode α} (x) : ∀ {c n} (h : is_red_black t c n), ins_rb_result (ins lt t x) c n :=
begin
  apply [expr ins.induction lt t x]; intros []; cases [expr h] []; simp [] [] [] ["[", expr ins, ",", "*", ",", expr ins_rb_result, "]"] [] [],
  { repeat { constructor } },
  { specialize [expr ih h_rb_l],
    cases [expr ih] [],
    constructor; assumption },
  { constructor; assumption },
  { specialize [expr ih h_rb_r],
    cases [expr ih] [],
    constructor; assumption },
  { specialize [expr ih h_rb_l],
    have [] [] [":=", expr of_get_color_eq_red hr h_rb_l],
    subst [expr h_c₁],
    simp [] [] [] ["[", expr ins_rb_result, "]"] [] ["at", ident ih],
    apply [expr balance1_node_rb]; assumption },
  { specialize [expr ih h_rb_l],
    have [] [] [":=", expr of_get_color_ne_red hnr h_rb_l],
    subst [expr h_c₁],
    simp [] [] [] ["[", expr ins_rb_result, "]"] [] ["at", ident ih],
    cases [expr ih] [],
    constructor,
    constructor; assumption },
  { constructor,
    constructor; assumption },
  { specialize [expr ih h_rb_r],
    have [] [] [":=", expr of_get_color_eq_red hr h_rb_r],
    subst [expr h_c₂],
    simp [] [] [] ["[", expr ins_rb_result, "]"] [] ["at", ident ih],
    apply [expr balance2_node_rb]; assumption },
  { specialize [expr ih h_rb_r],
    have [] [] [":=", expr of_get_color_ne_red hnr h_rb_r],
    subst [expr h_c₂],
    simp [] [] [] ["[", expr ins_rb_result, "]"] [] ["at", ident ih],
    cases [expr ih] [],
    constructor,
    constructor; assumption }
end

def insert_rb_result : Rbnode α → color → Nat → Prop
| t, red, n => is_red_black t black (succ n)
| t, black, n => ∃ c, is_red_black t c n

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_rb {t : rbnode α} (x) {c n} (h : is_red_black t c n) : insert_rb_result (insert lt t x) c n :=
begin
  simp [] [] [] ["[", expr insert, "]"] [] [],
  have [ident hi] [] [":=", expr ins_rb lt x h],
  generalize [ident he] [":"] [expr «expr = »(ins lt t x, r)],
  simp [] [] [] ["[", expr he, "]"] [] ["at", ident hi],
  cases [expr h] []; simp [] [] [] ["[", expr get_color, ",", expr ins_rb_result, ",", expr insert_rb_result, ",", expr mk_insert_result, "]"] [] ["at", "*"],
  assumption',
  { cases [expr hi] [],
    simp [] [] [] ["[", expr mk_insert_result, "]"] [] [],
    constructor; assumption }
end

-- error in Data.Rbtree.Insert: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_is_red_black
{t : rbnode α}
{c n}
(x) : is_red_black t c n → «expr∃ , »((c n), is_red_black (insert lt t x) c n) :=
begin
  intro [ident h],
  have [] [] [":=", expr insert_rb lt x h],
  cases [expr c] []; simp [] [] [] ["[", expr insert_rb_result, "]"] [] ["at", ident this],
  { constructor,
    constructor,
    assumption },
  { cases [expr this] [],
    constructor,
    constructor,
    assumption }
end

end IsRedBlack

end Rbnode

