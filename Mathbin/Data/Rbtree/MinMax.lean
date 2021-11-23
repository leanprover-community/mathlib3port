import Mathbin.Data.Rbtree.Basic

universe u

namespace Rbnode

variable{α : Type u}{lt : α → α → Prop}

theorem mem_of_min_eq (lt : α → α → Prop) [IsIrrefl α lt] {a : α} {t : Rbnode α} : t.min = some a → mem lt a t :=
  by 
    induction t
    ·
      intros 
      contradiction 
    all_goals 
      cases t_lchild <;> simp [Rbnode.min] <;> intro h
      ·
        subst t_val 
        simp [mem, irrefl_of lt a]
      all_goals 
        rw [mem]
        simp [t_ih_lchild h]

theorem mem_of_max_eq (lt : α → α → Prop) [IsIrrefl α lt] {a : α} {t : Rbnode α} : t.max = some a → mem lt a t :=
  by 
    induction t
    ·
      intros 
      contradiction 
    all_goals 
      cases t_rchild <;> simp [Rbnode.max] <;> intro h
      ·
        subst t_val 
        simp [mem, irrefl_of lt a]
      all_goals 
        rw [mem]
        simp [t_ih_rchild h]

variable[IsStrictWeakOrder α lt]

-- error in Data.Rbtree.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_leaf_of_min_eq_none {t : rbnode α} : «expr = »(t.min, none) → «expr = »(t, leaf) :=
begin
  induction [expr t] [] [] [],
  { intros [],
    refl },
  all_goals { cases [expr t_lchild] []; simp [] [] [] ["[", expr rbnode.min, ",", expr false_implies_iff, "]"] [] []; intro [ident h],
    all_goals { have [] [] [":=", expr t_ih_lchild h],
      contradiction } }
end

-- error in Data.Rbtree.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_leaf_of_max_eq_none {t : rbnode α} : «expr = »(t.max, none) → «expr = »(t, leaf) :=
begin
  induction [expr t] [] [] [],
  { intros [],
    refl },
  all_goals { cases [expr t_rchild] []; simp [] [] [] ["[", expr rbnode.max, ",", expr false_implies_iff, "]"] [] []; intro [ident h],
    all_goals { have [] [] [":=", expr t_ih_rchild h],
      contradiction } }
end

-- error in Data.Rbtree.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem min_is_minimal
{a : α}
{t : rbnode α} : ∀
{lo
 hi}, is_searchable lt t lo hi → «expr = »(t.min, some a) → ∀
{b}, mem lt b t → «expr ∨ »(«expr ≈[ ] »(a, lt, b), lt a b) :=
begin
  classical,
  induction [expr t] [] [] [],
  { simp [] [] [] ["[", expr strict_weak_order.equiv, "]"] [] [],
    intros ["_", "_", ident hs, ident hmin, ident b],
    contradiction },
  all_goals { cases [expr t_lchild] []; intros [ident lo, ident hi, ident hs, ident hmin, ident b, ident hmem],
    { simp [] [] [] ["[", expr rbnode.min, "]"] [] ["at", ident hmin],
      subst [expr t_val],
      simp [] [] [] ["[", expr mem, "]"] [] ["at", ident hmem],
      cases [expr hmem] ["with", ident heqv, ident hmem],
      { left,
        exact [expr heqv.swap] },
      { have [] [] [":=", expr lt_of_mem_right hs (by constructor) hmem],
        right,
        assumption } },
    all_goals { have [ident hs'] [] [":=", expr hs],
      cases [expr hs] [],
      simp [] [] [] ["[", expr rbnode.min, "]"] [] ["at", ident hmin],
      rw ["[", expr mem, "]"] ["at", ident hmem],
      blast_disjs,
      { exact [expr t_ih_lchild hs_hs₁ hmin hmem] },
      { have [ident hmm] [] [":=", expr mem_of_min_eq lt hmin],
        have [ident a_lt_val] [] [":=", expr lt_of_mem_left hs' (by constructor) hmm],
        have [ident a_lt_b] [] [":=", expr lt_of_lt_of_incomp a_lt_val hmem.swap],
        right,
        assumption },
      { have [ident hmm] [] [":=", expr mem_of_min_eq lt hmin],
        have [ident a_lt_b] [] [":=", expr lt_of_mem_left_right hs' (by constructor) hmm hmem],
        right,
        assumption } } }
end

-- error in Data.Rbtree.MinMax: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem max_is_maximal
{a : α}
{t : rbnode α} : ∀
{lo
 hi}, is_searchable lt t lo hi → «expr = »(t.max, some a) → ∀
{b}, mem lt b t → «expr ∨ »(«expr ≈[ ] »(a, lt, b), lt b a) :=
begin
  classical,
  induction [expr t] [] [] [],
  { simp [] [] [] ["[", expr strict_weak_order.equiv, "]"] [] [],
    intros ["_", "_", ident hs, ident hmax, ident b],
    contradiction },
  all_goals { cases [expr t_rchild] []; intros [ident lo, ident hi, ident hs, ident hmax, ident b, ident hmem],
    { simp [] [] [] ["[", expr rbnode.max, "]"] [] ["at", ident hmax],
      subst [expr t_val],
      simp [] [] [] ["[", expr mem, "]"] [] ["at", ident hmem],
      cases [expr hmem] ["with", ident hmem, ident heqv],
      { have [] [] [":=", expr lt_of_mem_left hs (by constructor) hmem],
        right,
        assumption },
      { left,
        exact [expr heqv.swap] } },
    all_goals { have [ident hs'] [] [":=", expr hs],
      cases [expr hs] [],
      simp [] [] [] ["[", expr rbnode.max, "]"] [] ["at", ident hmax],
      rw ["[", expr mem, "]"] ["at", ident hmem],
      blast_disjs,
      { have [ident hmm] [] [":=", expr mem_of_max_eq lt hmax],
        have [ident a_lt_b] [] [":=", expr lt_of_mem_left_right hs' (by constructor) hmem hmm],
        right,
        assumption },
      { have [ident hmm] [] [":=", expr mem_of_max_eq lt hmax],
        have [ident val_lt_a] [] [":=", expr lt_of_mem_right hs' (by constructor) hmm],
        have [ident a_lt_b] [] [":=", expr lt_of_incomp_of_lt hmem val_lt_a],
        right,
        assumption },
      { exact [expr t_ih_rchild hs_hs₂ hmax hmem] } } }
end

end Rbnode

