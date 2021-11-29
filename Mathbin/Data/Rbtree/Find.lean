import Mathbin.Data.Rbtree.Basic

universe u

namespace Rbnode

variable{α : Type u}

@[elabWithoutExpectedType]
theorem find.induction {p : Rbnode α → Prop} lt [DecidableRel lt] t x (h₁ : p leaf)
  (h₂ : ∀ l y r (h : cmpUsing lt x y = Ordering.lt) (ih : p l), p (red_node l y r))
  (h₃ : ∀ l y r (h : cmpUsing lt x y = Ordering.eq), p (red_node l y r))
  (h₄ : ∀ l y r (h : cmpUsing lt x y = Ordering.gt) (ih : p r), p (red_node l y r))
  (h₅ : ∀ l y r (h : cmpUsing lt x y = Ordering.lt) (ih : p l), p (black_node l y r))
  (h₆ : ∀ l y r (h : cmpUsing lt x y = Ordering.eq), p (black_node l y r))
  (h₇ : ∀ l y r (h : cmpUsing lt x y = Ordering.gt) (ih : p r), p (black_node l y r)) : p t :=
  by 
    induction t 
    case leaf => 
      assumption 
    case red_node l y r => 
      cases h : cmpUsing lt x y 
      case ordering.lt => 
        apply h₂ 
        assumption 
        assumption 
      case ordering.eq => 
        apply h₃ 
        assumption 
      case ordering.gt => 
        apply h₄ 
        assumption 
        assumption 
    case black_node l y r => 
      cases h : cmpUsing lt x y 
      case ordering.lt => 
        apply h₅ 
        assumption 
        assumption 
      case ordering.eq => 
        apply h₆ 
        assumption 
      case ordering.gt => 
        apply h₇ 
        assumption 
        assumption

-- error in Data.Rbtree.Find: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_correct
{t : rbnode α}
{lt x}
[decidable_rel lt]
[is_strict_weak_order α lt] : ∀
{lo hi}
(hs : is_searchable lt t lo hi), «expr ↔ »(mem lt x t, «expr∃ , »((y), «expr ∧ »(«expr = »(find lt t x, some y), «expr ≈[ ] »(x, lt, y)))) :=
begin
  apply [expr find.induction lt t x]; intros []; simp [] [] ["only"] ["[", expr mem, ",", expr find, ",", "*", "]"] [] [],
  { simp [] [] [] [] [] [] },
  iterate [2] { { cases [expr hs] [],
      apply [expr iff.intro],
      { intro [ident hm],
        blast_disjs,
        { exact [expr iff.mp (ih hs_hs₁) hm] },
        { simp [] [] [] [] [] ["at", ident h],
          cases [expr hm] [],
          contradiction },
        { have [ident hyx] [":", expr lift lt (some y) (some x)] [":=", expr (range hs_hs₂ hm).1],
          simp [] [] [] ["[", expr lift, "]"] [] ["at", ident hyx],
          have [ident hxy] [":", expr lt x y] [],
          { simp [] [] [] ["[", expr cmp_using, "]"] [] ["at", ident h],
            assumption },
          exact [expr absurd (trans_of lt hxy hyx) (irrefl_of lt x)] } },
      { intro [ident hc],
        left,
        exact [expr iff.mpr (ih hs_hs₁) hc] } },
    { simp [] [] [] [] [] ["at", ident h],
      simp [] [] [] ["[", expr h, ",", expr strict_weak_order.equiv, "]"] [] [] },
    { cases [expr hs] [],
      apply [expr iff.intro],
      { intro [ident hm],
        blast_disjs,
        { have [ident hxy] [":", expr lift lt (some x) (some y)] [":=", expr (range hs_hs₁ hm).2],
          simp [] [] [] ["[", expr lift, "]"] [] ["at", ident hxy],
          have [ident hyx] [":", expr lt y x] [],
          { simp [] [] [] ["[", expr cmp_using, "]"] [] ["at", ident h],
            exact [expr h.2] },
          exact [expr absurd (trans_of lt hxy hyx) (irrefl_of lt x)] },
        { simp [] [] [] [] [] ["at", ident h],
          cases [expr hm] [],
          contradiction },
        { exact [expr iff.mp (ih hs_hs₂) hm] } },
      { intro [ident hc],
        right,
        right,
        exact [expr iff.mpr (ih hs_hs₂) hc] } } }
end

theorem mem_of_mem_exact {lt} [IsIrrefl α lt] {x t} : mem_exact x t → mem lt x t :=
  by 
    induction t <;> simp [mem_exact, mem, false_implies_iff] <;> intro h 
    all_goals 
      casesType* or.1
      simp [t_ih_lchild h]
      simp [h, irrefl_of lt t_val]
      simp [t_ih_rchild h]

-- error in Data.Rbtree.Find: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_correct_exact
{t : rbnode α}
{lt x}
[decidable_rel lt]
[is_strict_weak_order α lt] : ∀
{lo hi}
(hs : is_searchable lt t lo hi), «expr ↔ »(mem_exact x t, «expr = »(find lt t x, some x)) :=
begin
  apply [expr find.induction lt t x]; intros []; simp [] [] ["only"] ["[", expr mem_exact, ",", expr find, ",", "*", "]"] [] [],
  iterate [2] { { cases [expr hs] [],
      apply [expr iff.intro],
      { intro [ident hm],
        blast_disjs,
        { exact [expr iff.mp (ih hs_hs₁) hm] },
        { simp [] [] [] [] [] ["at", ident h],
          subst [expr x],
          exact [expr absurd h (irrefl y)] },
        { have [ident hyx] [":", expr lift lt (some y) (some x)] [":=", expr (range hs_hs₂ (mem_of_mem_exact hm)).1],
          simp [] [] [] ["[", expr lift, "]"] [] ["at", ident hyx],
          have [ident hxy] [":", expr lt x y] [],
          { simp [] [] [] ["[", expr cmp_using, "]"] [] ["at", ident h],
            assumption },
          exact [expr absurd (trans_of lt hxy hyx) (irrefl_of lt x)] } },
      { intro [ident hc],
        left,
        exact [expr iff.mpr (ih hs_hs₁) hc] } },
    { simp [] [] [] [] [] ["at", ident h],
      cases [expr hs] [],
      apply [expr iff.intro],
      { intro [ident hm],
        blast_disjs,
        { have [ident hxy] [":", expr lift lt (some x) (some y)] [":=", expr (range hs_hs₁ (mem_of_mem_exact hm)).2],
          simp [] [] [] ["[", expr lift, "]"] [] ["at", ident hxy],
          exact [expr absurd hxy h.1] },
        { subst [expr hm] },
        { have [ident hyx] [":", expr lift lt (some y) (some x)] [":=", expr (range hs_hs₂ (mem_of_mem_exact hm)).1],
          simp [] [] [] ["[", expr lift, "]"] [] ["at", ident hyx],
          exact [expr absurd hyx h.2] } },
      { intro [ident hm],
        simp [] [] [] ["[", "*", "]"] [] [] } },
    { cases [expr hs] [],
      apply [expr iff.intro],
      { intro [ident hm],
        blast_disjs,
        { have [ident hxy] [":", expr lift lt (some x) (some y)] [":=", expr (range hs_hs₁ (mem_of_mem_exact hm)).2],
          simp [] [] [] ["[", expr lift, "]"] [] ["at", ident hxy],
          have [ident hyx] [":", expr lt y x] [],
          { simp [] [] [] ["[", expr cmp_using, "]"] [] ["at", ident h],
            exact [expr h.2] },
          exact [expr absurd (trans_of lt hxy hyx) (irrefl_of lt x)] },
        { simp [] [] [] [] [] ["at", ident h],
          subst [expr x],
          exact [expr absurd h (irrefl y)] },
        { exact [expr iff.mp (ih hs_hs₂) hm] } },
      { intro [ident hc],
        right,
        right,
        exact [expr iff.mpr (ih hs_hs₂) hc] } } }
end

theorem eqv_of_find_some {t : Rbnode α} {lt x y} [DecidableRel lt] :
  ∀ {lo hi} (hs : is_searchable lt t lo hi) (he : find lt t x = some y), x ≈[lt]y :=
  by 
    apply find.induction lt t x <;> intros  <;> simp_all only [mem, find]
    iterate 2
      ·
        cases hs 
        exact ih hs_hs₁ rfl
      ·
        subst y 
        simp  at h 
        exact h
      ·
        cases hs 
        exact ih hs_hs₂ rfl

-- error in Data.Rbtree.Find: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_eq_find_of_eqv
{lt a b}
[decidable_rel lt]
[is_strict_weak_order α lt]
{t : rbnode α} : ∀
{lo hi}
(hs : is_searchable lt t lo hi)
(heqv : «expr ≈[ ] »(a, lt, b)), «expr = »(find lt t a, find lt t b) :=
begin
  apply [expr find.induction lt t a]; intros []; simp [] [] [] ["[", expr mem, ",", expr find, ",", expr strict_weak_order.equiv, ",", "*", ",", expr true_implies_iff, "]"] [] ["at", "*"],
  iterate [2] { { have [] [":", expr lt b y] [":=", expr lt_of_incomp_of_lt heqv.swap h],
      simp [] [] [] ["[", expr cmp_using, ",", expr find, ",", "*", "]"] [] [],
      cases [expr hs] [],
      apply [expr ih hs_hs₁] },
    { have [] [] [":=", expr incomp_trans_of lt heqv.swap h],
      simp [] [] [] ["[", expr cmp_using, ",", expr find, ",", "*", "]"] [] [] },
    { have [] [] [":=", expr lt_of_lt_of_incomp h heqv],
      have [] [] [":=", expr not_lt_of_lt this],
      simp [] [] [] ["[", expr cmp_using, ",", expr find, ",", "*", "]"] [] [],
      cases [expr hs] [],
      apply [expr ih hs_hs₂] } }
end

end Rbnode

