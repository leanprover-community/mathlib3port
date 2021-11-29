import Mathbin.Tactic.Interactive 
import Mathbin.Data.Rbtree.Init

universe u

unsafe def tactic.interactive.blast_disjs : tactic Unit :=
  sorry

namespace Rbnode

variable {α : Type u}

open Color Nat

inductive is_node_of : Rbnode α → Rbnode α → α → Rbnode α → Prop
  | of_red l v r : is_node_of (red_node l v r) l v r
  | of_black l v r : is_node_of (black_node l v r) l v r

def lift (lt : α → α → Prop) : Option α → Option α → Prop
| some a, some b => lt a b
| _, _ => True

inductive is_searchable (lt : α → α → Prop) : Rbnode α → Option α → Option α → Prop
  | leaf_s {lo hi} (hlt : lift lt lo hi) : is_searchable leaf lo hi
  | red_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) :
  is_searchable (red_node l v r) lo hi
  | black_s {l r v lo hi} (hs₁ : is_searchable l lo (some v)) (hs₂ : is_searchable r (some v) hi) :
  is_searchable (black_node l v r) lo hi

unsafe def is_searchable_tactic : tactic Unit :=
  sorry

open rbnode(Mem)

open IsSearchable

section IsSearchableLemmas

variable {lt : α → α → Prop}

-- error in Data.Rbtree.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lo_lt_hi {t : rbnode α} {lt} [is_trans α lt] : ∀ {lo hi}, is_searchable lt t lo hi → lift lt lo hi :=
begin
  induction [expr t] [] [] []; intros [ident lo, ident hi, ident hs],
  case [ident leaf] { cases [expr hs] [],
    assumption },
  all_goals { cases [expr hs] [],
    have [ident h₁] [] [":=", expr t_ih_lchild hs_hs₁],
    have [ident h₂] [] [":=", expr t_ih_rchild hs_hs₂],
    cases [expr lo] []; cases [expr hi] []; simp [] [] [] ["[", expr lift, "]"] [] ["at", "*"],
    apply [expr trans_of lt h₁ h₂] }
end

theorem is_searchable_of_is_searchable_of_incomp [IsStrictWeakOrder α lt] {t} :
  ∀ {lo hi hi'} hc : ¬lt hi' hi ∧ ¬lt hi hi' hs : is_searchable lt t lo (some hi), is_searchable lt t lo (some hi') :=
  by 
    classical 
    induction t <;>
      intros  <;>
        runTac 
          is_searchable_tactic
    ·
      cases lo <;> simp_all [lift]
      apply lt_of_lt_of_incomp 
      assumption 
      exact ⟨hc.2, hc.1⟩
    all_goals 
      apply t_ih_rchild hc hs_hs₂

theorem is_searchable_of_incomp_of_is_searchable [IsStrictWeakOrder α lt] {t} :
  ∀ {lo lo' hi} hc : ¬lt lo' lo ∧ ¬lt lo lo' hs : is_searchable lt t (some lo) hi, is_searchable lt t (some lo') hi :=
  by 
    classical 
    induction t <;>
      intros  <;>
        runTac 
          is_searchable_tactic
    ·
      cases hi <;> simp_all [lift]
      apply lt_of_incomp_of_lt 
      assumption 
      assumption 
    all_goals 
      apply t_ih_lchild hc hs_hs₁

theorem is_searchable_some_low_of_is_searchable_of_lt {t} [IsTrans α lt] :
  ∀ {lo hi lo'} hlt : lt lo' lo hs : is_searchable lt t (some lo) hi, is_searchable lt t (some lo') hi :=
  by 
    induction t <;>
      intros  <;>
        runTac 
          is_searchable_tactic
    ·
      cases hi <;> simp_all [lift]
      apply trans_of lt hlt 
      assumption 
    all_goals 
      apply t_ih_lchild hlt hs_hs₁

theorem is_searchable_none_low_of_is_searchable_some_low {t} :
  ∀ {y hi} hlt : is_searchable lt t (some y) hi, is_searchable lt t none hi :=
  by 
    induction t <;>
      intros  <;>
        runTac 
          is_searchable_tactic
    ·
      simp [lift]
    all_goals 
      apply t_ih_lchild hlt_hs₁

theorem is_searchable_some_high_of_is_searchable_of_lt {t} [IsTrans α lt] :
  ∀ {lo hi hi'} hlt : lt hi hi' hs : is_searchable lt t lo (some hi), is_searchable lt t lo (some hi') :=
  by 
    induction t <;>
      intros  <;>
        runTac 
          is_searchable_tactic
    ·
      cases lo <;> simp_all [lift]
      apply trans_of lt 
      assumption 
      assumption 
    all_goals 
      apply t_ih_rchild hlt hs_hs₂

theorem is_searchable_none_high_of_is_searchable_some_high {t} :
  ∀ {lo y} hlt : is_searchable lt t lo (some y), is_searchable lt t lo none :=
  by 
    induction t <;>
      intros  <;>
        runTac 
          is_searchable_tactic
    ·
      cases lo <;> simp [lift]
    all_goals 
      apply t_ih_rchild hlt_hs₂

-- error in Data.Rbtree.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem range
[is_strict_weak_order α lt]
{t : rbnode α}
{x} : ∀ {lo hi}, is_searchable lt t lo hi → mem lt x t → «expr ∧ »(lift lt lo (some x), lift lt (some x) hi) :=
begin
  classical,
  induction [expr t] [] [] [],
  case [ident leaf] { simp [] [] [] ["[", expr mem, "]"] [] [] },
  all_goals { intros [ident lo, ident hi, ident h₁, ident h₂],
    cases [expr h₁] [],
    simp [] [] ["only"] ["[", expr mem, "]"] [] ["at", ident h₂],
    have [ident val_hi] [":", expr lift lt (some t_val) hi] [],
    { apply [expr lo_lt_hi],
      assumption },
    have [ident lo_val] [":", expr lift lt lo (some t_val)] [],
    { apply [expr lo_lt_hi],
      assumption },
    blast_disjs,
    { have [ident h₃] [":", expr «expr ∧ »(lift lt lo (some x), lift lt (some x) (some t_val))] [],
      { apply [expr t_ih_lchild],
        assumption,
        assumption },
      cases [expr h₃] ["with", ident lo_x, ident x_val],
      split,
      show [expr lift lt lo (some x)],
      { assumption },
      show [expr lift lt (some x) hi],
      { cases [expr hi] ["with", ident hi]; simp [] [] [] ["[", expr lift, "]"] [] ["at", "*"],
        apply [expr trans_of lt x_val val_hi] } },
    { cases [expr h₂] [],
      cases [expr lo] ["with", ident lo]; cases [expr hi] ["with", ident hi]; simp [] [] [] ["[", expr lift, "]"] [] ["at", "*"],
      { apply [expr lt_of_incomp_of_lt _ val_hi],
        simp [] [] [] ["[", "*", "]"] [] [] },
      { apply [expr lt_of_lt_of_incomp lo_val],
        simp [] [] [] ["[", "*", "]"] [] [] },
      split,
      { apply [expr lt_of_lt_of_incomp lo_val],
        simp [] [] [] ["[", "*", "]"] [] [] },
      { apply [expr lt_of_incomp_of_lt _ val_hi],
        simp [] [] [] ["[", "*", "]"] [] [] } },
    { have [ident h₃] [":", expr «expr ∧ »(lift lt (some t_val) (some x), lift lt (some x) hi)] [],
      { apply [expr t_ih_rchild],
        assumption,
        assumption },
      cases [expr h₃] ["with", ident val_x, ident x_hi],
      cases [expr lo] ["with", ident lo]; cases [expr hi] ["with", ident hi]; simp [] [] [] ["[", expr lift, "]"] [] ["at", "*"],
      { assumption },
      { apply [expr trans_of lt lo_val val_x] },
      split,
      { apply [expr trans_of lt lo_val val_x] },
      { assumption } } }
end

theorem lt_of_mem_left [IsStrictWeakOrder α lt] {y : α} {t l r : Rbnode α} :
  ∀ {lo hi}, is_searchable lt t lo hi → is_node_of t l y r → ∀ {x}, mem lt x l → lt x y :=
  by 
    intro _ _ hs hn x hm 
    cases hn <;> cases hs 
    all_goals 
      exact (range hs_hs₁ hm).2

theorem lt_of_mem_right [IsStrictWeakOrder α lt] {y : α} {t l r : Rbnode α} :
  ∀ {lo hi}, is_searchable lt t lo hi → is_node_of t l y r → ∀ {z}, mem lt z r → lt y z :=
  by 
    intro _ _ hs hn z hm 
    cases hn <;> cases hs 
    all_goals 
      exact (range hs_hs₂ hm).1

-- error in Data.Rbtree.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_of_mem_left_right
[is_strict_weak_order α lt]
{y : α}
{t
 l
 r : rbnode α} : ∀ {lo hi}, is_searchable lt t lo hi → is_node_of t l y r → ∀ {x z}, mem lt x l → mem lt z r → lt x z :=
begin
  intros ["_", "_", ident hs, ident hn, ident x, ident z, ident hm₁, ident hm₂],
  cases [expr hn] []; cases [expr hs] [],
  all_goals { have [ident h₁] [] [":=", expr range hs_hs₁ hm₁],
    have [ident h₂] [] [":=", expr range hs_hs₂ hm₂],
    exact [expr trans_of lt h₁.2 h₂.1] }
end

end IsSearchableLemmas

inductive is_red_black : Rbnode α → color → Nat → Prop
  | leaf_rb : is_red_black leaf black 0
  | red_rb {v l r n} (rb_l : is_red_black l black n) (rb_r : is_red_black r black n) :
  is_red_black (red_node l v r) red n
  | black_rb {v l r n c₁ c₂} (rb_l : is_red_black l c₁ n) (rb_r : is_red_black r c₂ n) :
  is_red_black (black_node l v r) black (succ n)

open IsRedBlack

-- error in Data.Rbtree.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem depth_min : ∀ {c n} {t : rbnode α}, is_red_black t c n → «expr ≤ »(n, depth min t) :=
begin
  intros [ident c, ident n', ident t, ident h],
  induction [expr h] [] [] [],
  case [ident leaf_rb] { apply [expr le_refl] },
  case [ident red_rb] { simp [] [] [] ["[", expr depth, "]"] [] [],
    have [] [":", expr «expr ≥ »(min (depth min h_l) (depth min h_r), h_n)] [],
    { apply [expr le_min]; assumption },
    apply [expr le_succ_of_le],
    assumption },
  case [ident black_rb] { simp [] [] [] ["[", expr depth, "]"] [] [],
    apply [expr succ_le_succ],
    apply [expr le_min]; assumption }
end

private def upper : color → Nat → Nat
| red, n => (2*n)+1
| black, n => 2*n

private theorem upper_le : ∀ c n, upper c n ≤ (2*n)+1
| red, n =>
  by 
    apply le_reflₓ
| black, n =>
  by 
    apply le_succ

-- error in Data.Rbtree.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem depth_max' : ∀ {c n} {t : rbnode α}, is_red_black t c n → «expr ≤ »(depth max t, upper c n) :=
begin
  intros [ident c, ident n', ident t, ident h],
  induction [expr h] [] [] [],
  case [ident leaf_rb] { simp [] [] [] ["[", expr max, ",", expr depth, ",", expr upper, ",", expr nat.mul_zero, "]"] [] [] },
  case [ident red_rb] { suffices [] [":", expr «expr ≤ »(succ (max (depth max h_l) (depth max h_r)), «expr + »(«expr * »(2, h_n), 1))],
    { simp [] [] [] ["[", expr depth, ",", expr upper, ",", "*", "]"] [] ["at", "*"] },
    apply [expr succ_le_succ],
    apply [expr max_le]; assumption },
  case [ident black_rb] { have [] [":", expr «expr ≤ »(depth max h_l, «expr + »(«expr * »(2, h_n), 1))] [],
    from [expr le_trans h_ih_rb_l (upper_le _ _)],
    have [] [":", expr «expr ≤ »(depth max h_r, «expr + »(«expr * »(2, h_n), 1))] [],
    from [expr le_trans h_ih_rb_r (upper_le _ _)],
    suffices [ident new] [":", expr «expr ≤ »(«expr + »(max (depth max h_l) (depth max h_r), 1), «expr + »(«expr * »(2, h_n), «expr * »(2, 1)))],
    { simp [] [] [] ["[", expr depth, ",", expr upper, ",", expr succ_eq_add_one, ",", expr nat.left_distrib, ",", "*", "]"] [] ["at", "*"] },
    apply [expr succ_le_succ],
    apply [expr max_le]; assumption }
end

theorem depth_max {c n} {t : Rbnode α} (h : is_red_black t c n) : depth max t ≤ (2*n)+1 :=
  le_transₓ (depth_max' h) (upper_le _ _)

-- error in Data.Rbtree.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem balanced
{c n}
{t : rbnode α}
(h : is_red_black t c n) : «expr ≤ »(depth max t, «expr + »(«expr * »(2, depth min t), 1)) :=
begin
  have [] [":", expr «expr ≥ »(«expr + »(«expr * »(2, depth min t), 1), «expr + »(«expr * »(2, n), 1))] [],
  { apply [expr succ_le_succ],
    apply [expr nat.mul_le_mul_left],
    apply [expr depth_min h] },
  apply [expr le_trans],
  apply [expr depth_max h],
  apply [expr this]
end

end Rbnode

