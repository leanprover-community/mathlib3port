/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.rbtree.find
! leanprover-community/mathlib commit 8f6fd1b69096c6a587f745d354306c0d46396915
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rbtree.Basic

universe u

namespace Std.RBNode

variable {α : Type u}

@[elab_without_expected_type]
theorem Std.RBNode.find?.induction {p : Std.RBNode α → Prop} (lt) [DecidableRel lt] (t x)
    (h₁ : p Std.RBNode.nil)
    (h₂ : ∀ (l y r) (h : cmpUsing lt x y = Ordering.lt) (ih : p l), p (Std.RBNode.node l y r))
    (h₃ : ∀ (l y r) (h : cmpUsing lt x y = Ordering.eq), p (Std.RBNode.node l y r))
    (h₄ : ∀ (l y r) (h : cmpUsing lt x y = Ordering.gt) (ih : p r), p (Std.RBNode.node l y r))
    (h₅ : ∀ (l y r) (h : cmpUsing lt x y = Ordering.lt) (ih : p l), p (black_node l y r))
    (h₆ : ∀ (l y r) (h : cmpUsing lt x y = Ordering.eq), p (black_node l y r))
    (h₇ : ∀ (l y r) (h : cmpUsing lt x y = Ordering.gt) (ih : p r), p (black_node l y r)) : p t :=
  by
  induction t
  case leaf => assumption
  case red_node l y r =>
    cases h : cmpUsing lt x y
    case lt => apply h₂; assumption; assumption
    case eq => apply h₃; assumption
    case gt => apply h₄; assumption; assumption
  case black_node l y r =>
    cases h : cmpUsing lt x y
    case lt => apply h₅; assumption; assumption
    case eq => apply h₆; assumption
    case gt => apply h₇; assumption; assumption
#align rbnode.find.induction Std.RBNode.find?.induction

theorem Std.RBNode.find?_correct {t : Std.RBNode α} {lt x} [DecidableRel lt]
    [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (hs : Std.RBNode.IsSearchable lt t lo hi),
      Std.RBNode.Mem lt x t ↔ ∃ y, Std.RBNode.find? lt t x = some y ∧ x ≈[lt]y :=
  by
  apply find.induction lt t x <;> intros <;> simp only [mem, find, *]
  · simp
  iterate 2
    
    -- red and black cases are identical
    · cases hs
      apply Iff.intro
      · intro hm; cases_type* or.1
        · exact Iff.mp (ih hs_hs₁) hm
        · simp at h ; cases hm; contradiction
        · have hyx : lift lt (some y) (some x) := (range hs_hs₂ hm).1
          simp [lift] at hyx 
          have hxy : lt x y := by simp [cmpUsing] at h ; assumption
          exact absurd (trans_of lt hxy hyx) (irrefl_of lt x)
      · intro hc; left; exact Iff.mpr (ih hs_hs₁) hc
    · simp at h ; simp [h, StrictWeakOrder.Equiv]
    · cases hs
      apply Iff.intro
      · intro hm; cases_type* or.1
        · have hxy : lift lt (some x) (some y) := (range hs_hs₁ hm).2
          simp [lift] at hxy 
          have hyx : lt y x := by simp [cmpUsing] at h ; exact h.2
          exact absurd (trans_of lt hxy hyx) (irrefl_of lt x)
        · simp at h ; cases hm; contradiction
        · exact Iff.mp (ih hs_hs₂) hm
      · intro hc; right; right; exact Iff.mpr (ih hs_hs₂) hc
#align rbnode.find_correct Std.RBNode.find?_correct

theorem Std.RBNode.mem_of_memExact {lt} [IsIrrefl α lt] {x t} :
    Std.RBNode.MemExact x t → Std.RBNode.Mem lt x t :=
  by
  induction t <;> simp [mem_exact, mem, false_imp_iff] <;> intro h
  all_goals
    cases_type* or.1; simp [t_ih_lchild h]; simp [h, irrefl_of lt t_val]
    simp [t_ih_rchild h]
#align rbnode.mem_of_mem_exact Std.RBNode.mem_of_memExact

theorem Std.RBNode.find?_correct_exact {t : Std.RBNode α} {lt x} [DecidableRel lt]
    [IsStrictWeakOrder α lt] :
    ∀ {lo hi} (hs : Std.RBNode.IsSearchable lt t lo hi),
      Std.RBNode.MemExact x t ↔ Std.RBNode.find? lt t x = some x :=
  by
  apply find.induction lt t x <;> intros <;> simp only [mem_exact, find, *]
  iterate 2
    
    · cases hs
      apply Iff.intro
      · intro hm; cases_type* or.1
        · exact Iff.mp (ih hs_hs₁) hm
        · simp at h ; subst x; exact absurd h (irrefl y)
        · have hyx : lift lt (some y) (some x) := (range hs_hs₂ (mem_of_mem_exact hm)).1
          simp [lift] at hyx 
          have hxy : lt x y := by simp [cmpUsing] at h ; assumption
          exact absurd (trans_of lt hxy hyx) (irrefl_of lt x)
      · intro hc; left; exact Iff.mpr (ih hs_hs₁) hc
    · simp at h 
      cases hs
      apply Iff.intro
      · intro hm; cases_type* or.1
        · have hxy : lift lt (some x) (some y) := (range hs_hs₁ (mem_of_mem_exact hm)).2
          simp [lift] at hxy 
          exact absurd hxy h.1
        · subst hm
        · have hyx : lift lt (some y) (some x) := (range hs_hs₂ (mem_of_mem_exact hm)).1
          simp [lift] at hyx 
          exact absurd hyx h.2
      · intro hm; simp [*]
    · cases hs
      apply Iff.intro
      · intro hm; cases_type* or.1
        · have hxy : lift lt (some x) (some y) := (range hs_hs₁ (mem_of_mem_exact hm)).2
          simp [lift] at hxy 
          have hyx : lt y x := by simp [cmpUsing] at h ; exact h.2
          exact absurd (trans_of lt hxy hyx) (irrefl_of lt x)
        · simp at h ; subst x; exact absurd h (irrefl y)
        · exact Iff.mp (ih hs_hs₂) hm
      · intro hc; right; right; exact Iff.mpr (ih hs_hs₂) hc
#align rbnode.find_correct_exact Std.RBNode.find?_correct_exact

theorem Std.RBNode.eqv_of_find?_some {t : Std.RBNode α} {lt x y} [DecidableRel lt] :
    ∀ {lo hi} (hs : Std.RBNode.IsSearchable lt t lo hi) (he : Std.RBNode.find? lt t x = some y),
      x ≈[lt]y :=
  by
  apply find.induction lt t x <;> intros <;> simp_all only [mem, find]
  iterate 2 
    · cases hs; exact ih hs_hs₁ rfl
    · subst y; simp at h ; exact h
    · cases hs; exact ih hs_hs₂ rfl
#align rbnode.eqv_of_find_some Std.RBNode.eqv_of_find?_some

theorem Std.RBNode.find?_eq_find?_of_eqv {lt a b} [DecidableRel lt] [IsStrictWeakOrder α lt]
    {t : Std.RBNode α} :
    ∀ {lo hi} (hs : Std.RBNode.IsSearchable lt t lo hi) (heqv : a ≈[lt]b),
      Std.RBNode.find? lt t a = Std.RBNode.find? lt t b :=
  by
  apply find.induction lt t a <;> intros <;>
    simp_all [mem, find, StrictWeakOrder.Equiv, true_imp_iff]
  iterate 2
    
    · have : lt b y := lt_of_incomp_of_lt heqv.swap h
      simp [cmpUsing, find, *]; cases hs; apply ih hs_hs₁
    · have := incomp_trans_of lt heqv.swap h; simp [cmpUsing, find, *]
    · have := lt_of_lt_of_incomp h heqv
      have := not_lt_of_lt this
      simp [cmpUsing, find, *]; cases hs; apply ih hs_hs₂
#align rbnode.find_eq_find_of_eqv Std.RBNode.find?_eq_find?_of_eqv

end Std.RBNode

