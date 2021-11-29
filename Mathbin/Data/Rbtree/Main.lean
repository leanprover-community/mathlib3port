import Mathbin.Data.Rbtree.Find 
import Mathbin.Data.Rbtree.Insert 
import Mathbin.Data.Rbtree.MinMax

universe u

namespace Rbnode

variable {α : Type u} {lt : α → α → Prop}

theorem is_searchable_of_well_formed {t : Rbnode α} [IsStrictWeakOrder α lt] :
  t.well_formed lt → is_searchable lt t none none :=
  by 
    intro h 
    induction h
    ·
      constructor 
      simp [lift]
    ·
      subst h_n' 
      apply is_searchable_insert 
      assumption

open Color

theorem is_red_black_of_well_formed {t : Rbnode α} : t.well_formed lt → ∃ c n, is_red_black t c n :=
  by 
    intro h 
    induction h
    ·
      exists black 
      exists 0
      constructor
    ·
      cases' h_ih with c ih 
      cases' ih with n ih 
      subst h_n' 
      apply insert_is_red_black 
      assumption

end Rbnode

namespace Rbtree

variable {α : Type u} {lt : α → α → Prop}

-- error in Data.Rbtree.Main: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem balanced (t : rbtree α lt) : «expr ≤ »(t.depth max, «expr + »(«expr * »(2, t.depth min), 1)) :=
begin
  cases [expr t] ["with", ident n, ident p],
  simp [] [] ["only"] ["[", expr depth, "]"] [] [],
  have [] [] [":=", expr rbnode.is_red_black_of_well_formed p],
  cases [expr this] ["with", "_", ident this],
  cases [expr this] ["with", "_", ident this],
  apply [expr rbnode.balanced],
  assumption
end

theorem not_mem_mk_rbtree : ∀ a : α, a ∉ mkRbtree α lt :=
  by 
    simp [HasMem.Mem, Rbtree.Mem, Rbnode.Mem, mkRbtree]

theorem not_mem_of_empty {t : Rbtree α lt} (a : α) : t.empty = tt → a ∉ t :=
  by 
    cases' t with n p <;> cases n <;> simp [Empty, HasMem.Mem, Rbtree.Mem, Rbnode.Mem, false_implies_iff]

-- error in Data.Rbtree.Main: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_of_mem_of_eqv
[is_strict_weak_order α lt]
{t : rbtree α lt}
{a b : α} : «expr ∈ »(a, t) → «expr ≈[ ] »(a, lt, b) → «expr ∈ »(b, t) :=
begin
  cases [expr t] ["with", ident n, ident p]; simp [] [] [] ["[", expr has_mem.mem, ",", expr rbtree.mem, "]"] [] []; clear [ident p]; induction [expr n] [] [] []; simp [] [] ["only"] ["[", expr rbnode.mem, ",", expr strict_weak_order.equiv, ",", expr false_implies_iff, "]"] [] []; intros [ident h₁, ident h₂]; blast_disjs,
  iterate [2] { { have [] [":", expr rbnode.mem lt b n_lchild] [":=", expr n_ih_lchild h₁ h₂],
      simp [] [] [] ["[", expr this, "]"] [] [] },
    { simp [] [] [] ["[", expr incomp_trans_of lt h₂.swap h₁, "]"] [] [] },
    { have [] [":", expr rbnode.mem lt b n_rchild] [":=", expr n_ih_rchild h₁ h₂],
      simp [] [] [] ["[", expr this, "]"] [] [] } }
end

section Dec

variable [DecidableRel lt]

theorem insert_ne_mk_rbtree (t : Rbtree α lt) (a : α) : t.insert a ≠ mkRbtree α lt :=
  by 
    cases' t with n p 
    simp [insert, mkRbtree]
    intro h 
    injection h with h' 
    apply Rbnode.insert_ne_leaf lt n a h'

theorem find_correct [IsStrictWeakOrder α lt] (a : α) (t : Rbtree α lt) : (a∈t) ↔ ∃ b, t.find a = some b ∧ a ≈[lt]b :=
  by 
    cases t 
    apply Rbnode.find_correct 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

theorem find_correct_of_total [IsStrictTotalOrder α lt] (a : α) (t : Rbtree α lt) : (a∈t) ↔ t.find a = some a :=
  Iff.intro
    (fun h =>
      match Iff.mp (find_correct a t) h with 
      | ⟨b, HEq, heqv⟩ =>
        by 
          simp [HEq, (eq_of_eqv_lt heqv).symm])
    fun h => Iff.mpr (find_correct a t) ⟨a, ⟨h, refl a⟩⟩

theorem find_correct_exact [IsStrictTotalOrder α lt] (a : α) (t : Rbtree α lt) : mem_exact a t ↔ t.find a = some a :=
  by 
    cases t 
    apply Rbnode.find_correct_exact 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

theorem find_insert_of_eqv [IsStrictWeakOrder α lt] (t : Rbtree α lt) {x y} : x ≈[lt]y → (t.insert x).find y = some x :=
  by 
    cases t 
    intro h 
    apply Rbnode.find_insert_of_eqv lt h 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

theorem find_insert [IsStrictWeakOrder α lt] (t : Rbtree α lt) x : (t.insert x).find x = some x :=
  find_insert_of_eqv t (refl x)

theorem find_insert_of_disj [IsStrictWeakOrder α lt] {x y : α} (t : Rbtree α lt) :
  lt x y ∨ lt y x → (t.insert x).find y = t.find y :=
  by 
    cases t 
    intro h 
    apply Rbnode.find_insert_of_disj lt h 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

theorem find_insert_of_not_eqv [IsStrictWeakOrder α lt] {x y : α} (t : Rbtree α lt) :
  ¬x ≈[lt]y → (t.insert x).find y = t.find y :=
  by 
    cases t 
    intro h 
    apply Rbnode.find_insert_of_not_eqv lt h 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

-- error in Data.Rbtree.Main: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem find_insert_of_ne
[is_strict_total_order α lt]
{x y : α}
(t : rbtree α lt) : «expr ≠ »(x, y) → «expr = »((t.insert x).find y, t.find y) :=
begin
  cases [expr t] [],
  intro [ident h],
  have [] [":", expr «expr¬ »(«expr ≈[ ] »(x, lt, y))] [":=", expr λ h', h (eq_of_eqv_lt h')],
  apply [expr rbnode.find_insert_of_not_eqv lt this],
  apply [expr rbnode.is_searchable_of_well_formed],
  assumption
end

theorem not_mem_of_find_none [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} : t.find a = none → a ∉ t :=
  fun h =>
    Iff.mpr (not_iff_not_of_iff (find_correct a t))$
      by 
        intro h 
        cases' h with _ h 
        cases' h with h₁ h₂ 
        rw [h] at h₁ 
        contradiction

theorem eqv_of_find_some [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} : t.find a = some b → a ≈[lt]b :=
  by 
    cases t 
    apply Rbnode.eqv_of_find_some 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

theorem eq_of_find_some [IsStrictTotalOrder α lt] {a b : α} {t : Rbtree α lt} : t.find a = some b → a = b :=
  fun h =>
    suffices a ≈[lt]b from eq_of_eqv_lt this 
    eqv_of_find_some h

theorem mem_of_find_some [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} : t.find a = some b → (a∈t) :=
  fun h => Iff.mpr (find_correct a t) ⟨b, ⟨h, eqv_of_find_some h⟩⟩

theorem find_eq_find_of_eqv [IsStrictWeakOrder α lt] {a b : α} (t : Rbtree α lt) : a ≈[lt]b → t.find a = t.find b :=
  by 
    cases t 
    apply Rbnode.find_eq_find_of_eqv 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

-- error in Data.Rbtree.Main: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem contains_correct
[is_strict_weak_order α lt]
(a : α)
(t : rbtree α lt) : «expr ↔ »(«expr ∈ »(a, t), «expr = »(t.contains a, tt)) :=
begin
  have [ident h] [] [":=", expr find_correct a t],
  simp [] [] [] ["[", expr h, ",", expr contains, "]"] [] [],
  apply [expr iff.intro],
  { intro [ident h'],
    cases [expr h'] ["with", "_", ident h'],
    cases [expr h'] [],
    simp [] [] [] ["[", "*", "]"] [] [],
    simp [] [] [] ["[", expr option.is_some, "]"] [] [] },
  { intro [ident h'],
    cases [expr heq, ":", expr find t a] ["with", ident v],
    simp [] [] [] ["[", expr heq, ",", expr option.is_some, "]"] [] ["at", ident h'],
    contradiction,
    existsi [expr v],
    simp [] [] [] [] [] [],
    apply [expr eqv_of_find_some heq] }
end

theorem mem_insert_of_incomp {a b : α} (t : Rbtree α lt) : ¬lt a b ∧ ¬lt b a → (a∈t.insert b) :=
  by 
    cases t 
    apply Rbnode.mem_insert_of_incomp

theorem mem_insert [IsIrrefl α lt] : ∀ a : α t : Rbtree α lt, a∈t.insert a :=
  by 
    intros 
    apply mem_insert_of_incomp 
    split  <;> apply irrefl_of lt

theorem mem_insert_of_equiv {a b : α} (t : Rbtree α lt) : a ≈[lt]b → (a∈t.insert b) :=
  by 
    cases t 
    apply Rbnode.mem_insert_of_incomp

theorem mem_insert_of_mem [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} (b : α) : (a∈t) → (a∈t.insert b) :=
  by 
    cases t 
    apply Rbnode.mem_insert_of_mem

theorem equiv_or_mem_of_mem_insert [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} :
  (a∈t.insert b) → a ≈[lt]b ∨ (a∈t) :=
  by 
    cases t 
    apply Rbnode.equiv_or_mem_of_mem_insert

theorem incomp_or_mem_of_mem_ins [IsStrictWeakOrder α lt] {a b : α} {t : Rbtree α lt} :
  (a∈t.insert b) → ¬lt a b ∧ ¬lt b a ∨ (a∈t) :=
  equiv_or_mem_of_mem_insert

theorem eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {a b : α} {t : Rbtree α lt} : (a∈t.insert b) → a = b ∨ (a∈t) :=
  fun h =>
    suffices a ≈[lt]b ∨ (a∈t)by 
      simp [eqv_lt_iff_eq] at this <;> assumption 
    incomp_or_mem_of_mem_ins h

end Dec

theorem mem_of_min_eq [IsIrrefl α lt] {a : α} {t : Rbtree α lt} : t.min = some a → (a∈t) :=
  by 
    cases t 
    apply Rbnode.mem_of_min_eq

theorem mem_of_max_eq [IsIrrefl α lt] {a : α} {t : Rbtree α lt} : t.max = some a → (a∈t) :=
  by 
    cases t 
    apply Rbnode.mem_of_max_eq

theorem eq_leaf_of_min_eq_none {t : Rbtree α lt} : t.min = none → t = mkRbtree α lt :=
  by 
    cases t 
    intro h 
    congr 
    apply Rbnode.eq_leaf_of_min_eq_none h

theorem eq_leaf_of_max_eq_none {t : Rbtree α lt} : t.max = none → t = mkRbtree α lt :=
  by 
    cases t 
    intro h 
    congr 
    apply Rbnode.eq_leaf_of_max_eq_none h

theorem min_is_minimal [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
  t.min = some a → ∀ {b}, (b∈t) → a ≈[lt]b ∨ lt a b :=
  by 
    classical 
    cases t 
    apply Rbnode.min_is_minimal 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

theorem max_is_maximal [IsStrictWeakOrder α lt] {a : α} {t : Rbtree α lt} :
  t.max = some a → ∀ {b}, (b∈t) → a ≈[lt]b ∨ lt b a :=
  by 
    cases t 
    apply Rbnode.max_is_maximal 
    apply Rbnode.is_searchable_of_well_formed 
    assumption

end Rbtree

