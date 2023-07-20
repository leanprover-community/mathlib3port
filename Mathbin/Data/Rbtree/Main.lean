/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathbin.Data.Rbtree.Find
import Mathbin.Data.Rbtree.Insert
import Mathbin.Data.Rbtree.MinMax
import Mathbin.Order.RelClasses

#align_import data.rbtree.main from "leanprover-community/mathlib"@"4d4167104581a21259f7f448e1972a63a4546be7"

universe u

namespace Std.RBNode

variable {α : Type u} {lt : α → α → Prop}

theorem Std.RBNode.isSearchableOfWellFormed {t : Std.RBNode α} [IsStrictWeakOrder α lt] :
    t.WF lt → Std.RBNode.IsSearchable lt t none none :=
  by
  intro h; induction h
  · constructor; simp [lift]
  · subst h_n'; apply is_searchable_insert; assumption
#align rbnode.is_searchable_of_well_formed Std.RBNode.isSearchableOfWellFormed

open Color

theorem Std.RBNode.isRedBlack_of_wF {t : Std.RBNode α} :
    t.WF lt → ∃ c n, Std.RBNode.IsRedBlack t c n :=
  by
  intro h; induction h
  · exists black; exists 0; constructor
  · cases' h_ih with c ih; cases' ih with n ih; subst h_n'; apply insert_is_red_black; assumption
#align rbnode.is_red_black_of_well_formed Std.RBNode.isRedBlack_of_wF

end Std.RBNode

namespace Std.RBSet

variable {α : Type u} {lt : α → α → Prop}

theorem Std.RBSet.balanced (t : Std.RBSet α lt) : t.depth max ≤ 2 * t.depth min + 1 :=
  by
  cases' t with n p; simp only [depth]
  have := Std.RBNode.isRedBlack_of_wF p
  cases' this with _ this; cases' this with _ this
  apply Std.RBNode.balanced; assumption
#align rbtree.balanced Std.RBSet.balanced

theorem Std.RBSet.not_mem_mkRBSet : ∀ a : α, a ∉ Std.mkRBSet α lt := by
  simp [Membership.Mem, Std.RBSet.Mem, Std.RBNode.Mem, Std.mkRBSet]
#align rbtree.not_mem_mk_rbtree Std.RBSet.not_mem_mkRBSet

theorem Std.RBSet.not_mem_of_empty {t : Std.RBSet α lt} (a : α) : t.Empty = true → a ∉ t := by
  cases' t with n p <;> cases n <;>
    simp [Empty, Membership.Mem, Std.RBSet.Mem, Std.RBNode.Mem, false_imp_iff]
#align rbtree.not_mem_of_empty Std.RBSet.not_mem_of_empty

theorem Std.RBSet.mem_of_mem_of_eqv [IsStrictWeakOrder α lt] {t : Std.RBSet α lt} {a b : α} :
    a ∈ t → a ≈[lt]b → b ∈ t :=
  by
  cases' t with n p <;> simp [Membership.Mem, Std.RBSet.Mem] <;> clear p <;> induction n <;>
        simp only [Std.RBNode.Mem, StrictWeakOrder.Equiv, false_imp_iff] <;>
      intro h₁ h₂ <;>
    cases_type* or.1
  iterate 2 
    · have : Std.RBNode.Mem lt b n_lchild := n_ih_lchild h₁ h₂; simp [this]
    · simp [incomp_trans_of lt h₂.swap h₁]
    · have : Std.RBNode.Mem lt b n_rchild := n_ih_rchild h₁ h₂; simp [this]
#align rbtree.mem_of_mem_of_eqv Std.RBSet.mem_of_mem_of_eqv

section Dec

variable [DecidableRel lt]

theorem Std.RBSet.insert_ne_mkRBSet (t : Std.RBSet α lt) (a : α) : t.insert a ≠ Std.mkRBSet α lt :=
  by
  cases' t with n p
  simpa [insert, Std.mkRBSet] using Std.RBNode.insert_ne_nil lt n a
#align rbtree.insert_ne_mk_rbtree Std.RBSet.insert_ne_mkRBSet

theorem Std.RBSet.find?_correct [IsStrictWeakOrder α lt] (a : α) (t : Std.RBSet α lt) :
    a ∈ t ↔ ∃ b, t.find a = some b ∧ a ≈[lt]b := by cases t; apply Std.RBNode.find?_correct;
  apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_correct Std.RBSet.find?_correct

theorem Std.RBSet.find?_correct_of_total [IsStrictTotalOrder α lt] (a : α) (t : Std.RBSet α lt) :
    a ∈ t ↔ t.find a = some a :=
  Iff.intro
    (fun h =>
      match Iff.mp (Std.RBSet.find?_correct a t) h with
      | ⟨b, HEq, heqv⟩ => by simp [HEq, (eq_of_eqv_lt heqv).symm])
    fun h => Iff.mpr (Std.RBSet.find?_correct a t) ⟨a, ⟨h, refl a⟩⟩
#align rbtree.find_correct_of_total Std.RBSet.find?_correct_of_total

theorem Std.RBSet.find?_correct_exact [IsStrictTotalOrder α lt] (a : α) (t : Std.RBSet α lt) :
    Std.RBSet.MemExact a t ↔ t.find a = some a := by cases t; apply Std.RBNode.find?_correct_exact;
  apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_correct_exact Std.RBSet.find?_correct_exact

theorem Std.RBSet.find?_insert_of_eqv [IsStrictWeakOrder α lt] (t : Std.RBSet α lt) {x y} :
    x ≈[lt]y → (t.insert x).find y = some x :=
  by
  cases t; intro h; apply Std.RBNode.find?_insert_of_eqv lt h;
  apply Std.RBNode.isSearchableOfWellFormed
  assumption
#align rbtree.find_insert_of_eqv Std.RBSet.find?_insert_of_eqv

#print Std.RBSet.find?_insert /-
theorem Std.RBSet.find?_insert [IsStrictWeakOrder α lt] (t : Std.RBSet α lt) (x) :
    (t.insert x).find x = some x :=
  Std.RBSet.find?_insert_of_eqv t (refl x)
#align rbtree.find_insert Std.RBSet.find?_insert
-/

theorem Std.RBSet.find?_insert_of_disj [IsStrictWeakOrder α lt] {x y : α} (t : Std.RBSet α lt) :
    lt x y ∨ lt y x → (t.insert x).find y = t.find y :=
  by
  cases t; intro h; apply Std.RBNode.find?_insert_of_disj lt h
  apply Std.RBNode.isSearchableOfWellFormed
  assumption
#align rbtree.find_insert_of_disj Std.RBSet.find?_insert_of_disj

theorem Std.RBSet.find?_insert_of_not_eqv [IsStrictWeakOrder α lt] {x y : α} (t : Std.RBSet α lt) :
    ¬x ≈[lt]y → (t.insert x).find y = t.find y :=
  by
  cases t; intro h; apply Std.RBNode.find?_insert_of_not_eqv lt h
  apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_insert_of_not_eqv Std.RBSet.find?_insert_of_not_eqv

#print Std.RBSet.find?_insert_of_ne /-
theorem Std.RBSet.find?_insert_of_ne [IsStrictTotalOrder α lt] {x y : α} (t : Std.RBSet α lt) :
    x ≠ y → (t.insert x).find y = t.find y :=
  by
  cases t; intro h
  have : ¬x ≈[lt]y := fun h' => h (eq_of_eqv_lt h')
  apply Std.RBNode.find?_insert_of_not_eqv lt this
  apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_insert_of_ne Std.RBSet.find?_insert_of_ne
-/

theorem Std.RBSet.not_mem_of_find?_none [IsStrictWeakOrder α lt] {a : α} {t : Std.RBSet α lt} :
    t.find a = none → a ∉ t := fun h =>
  Iff.mpr (not_congr (Std.RBSet.find?_correct a t)) <|
    by
    intro h
    cases' h with _ h; cases' h with h₁ h₂
    rw [h] at h₁ ; contradiction
#align rbtree.not_mem_of_find_none Std.RBSet.not_mem_of_find?_none

theorem Std.RBSet.eqv_of_find?_some [IsStrictWeakOrder α lt] {a b : α} {t : Std.RBSet α lt} :
    t.find a = some b → a ≈[lt]b := by cases t; apply Std.RBNode.eqv_of_find?_some;
  apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.eqv_of_find_some Std.RBSet.eqv_of_find?_some

theorem Std.RBSet.eq_of_find?_some [IsStrictTotalOrder α lt] {a b : α} {t : Std.RBSet α lt} :
    t.find a = some b → a = b := fun h =>
  suffices a ≈[lt]b from eq_of_eqv_lt this
  Std.RBSet.eqv_of_find?_some h
#align rbtree.eq_of_find_some Std.RBSet.eq_of_find?_some

theorem Std.RBSet.mem_of_find?_some [IsStrictWeakOrder α lt] {a b : α} {t : Std.RBSet α lt} :
    t.find a = some b → a ∈ t := fun h =>
  Iff.mpr (Std.RBSet.find?_correct a t) ⟨b, ⟨h, Std.RBSet.eqv_of_find?_some h⟩⟩
#align rbtree.mem_of_find_some Std.RBSet.mem_of_find?_some

theorem Std.RBSet.find?_eq_find?_of_eqv [IsStrictWeakOrder α lt] {a b : α} (t : Std.RBSet α lt) :
    a ≈[lt]b → t.find a = t.find b := by
  cases t; apply Std.RBNode.find?_eq_find?_of_eqv
  apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_eq_find_of_eqv Std.RBSet.find?_eq_find?_of_eqv

theorem Std.RBSet.contains_correct [IsStrictWeakOrder α lt] (a : α) (t : Std.RBSet α lt) :
    a ∈ t ↔ t.contains a = true := by
  have h := find_correct a t
  simp [h, contains]; apply Iff.intro
  · intro h'; cases' h' with _ h'; cases h'; simp [*]; simp [Option.isSome]
  · intro h'
    cases' heq : find t a with v; simp [HEq, Option.isSome] at h' ; contradiction
    exists v; simp; apply eqv_of_find_some HEq
#align rbtree.contains_correct Std.RBSet.contains_correct

theorem Std.RBSet.mem_insert_of_incomp {a b : α} (t : Std.RBSet α lt) :
    ¬lt a b ∧ ¬lt b a → a ∈ t.insert b := by cases t; apply Std.RBNode.mem_insert_of_incomp
#align rbtree.mem_insert_of_incomp Std.RBSet.mem_insert_of_incomp

#print Std.RBSet.mem_insert /-
theorem Std.RBSet.mem_insert [IsIrrefl α lt] : ∀ (a : α) (t : Std.RBSet α lt), a ∈ t.insert a := by
  intros; apply mem_insert_of_incomp; constructor <;> apply irrefl_of lt
#align rbtree.mem_insert Std.RBSet.mem_insert
-/

theorem Std.RBSet.mem_insert_of_equiv {a b : α} (t : Std.RBSet α lt) : a ≈[lt]b → a ∈ t.insert b :=
  by cases t; apply Std.RBNode.mem_insert_of_incomp
#align rbtree.mem_insert_of_equiv Std.RBSet.mem_insert_of_equiv

#print Std.RBSet.mem_insert_of_mem /-
theorem Std.RBSet.mem_insert_of_mem [IsStrictWeakOrder α lt] {a : α} {t : Std.RBSet α lt} (b : α) :
    a ∈ t → a ∈ t.insert b := by cases t; apply Std.RBNode.mem_insert_of_mem
#align rbtree.mem_insert_of_mem Std.RBSet.mem_insert_of_mem
-/

theorem Std.RBSet.equiv_or_mem_of_mem_insert {a b : α} {t : Std.RBSet α lt} :
    a ∈ t.insert b → a ≈[lt]b ∨ a ∈ t := by cases t; apply Std.RBNode.equiv_or_mem_of_mem_insert
#align rbtree.equiv_or_mem_of_mem_insert Std.RBSet.equiv_or_mem_of_mem_insert

theorem Std.RBSet.incomp_or_mem_of_mem_ins {a b : α} {t : Std.RBSet α lt} :
    a ∈ t.insert b → ¬lt a b ∧ ¬lt b a ∨ a ∈ t :=
  Std.RBSet.equiv_or_mem_of_mem_insert
#align rbtree.incomp_or_mem_of_mem_ins Std.RBSet.incomp_or_mem_of_mem_ins

theorem Std.RBSet.eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {a b : α} {t : Std.RBSet α lt} :
    a ∈ t.insert b → a = b ∨ a ∈ t := fun h =>
  suffices a ≈[lt]b ∨ a ∈ t by simp [eqv_lt_iff_eq] at this  <;> assumption
  Std.RBSet.incomp_or_mem_of_mem_ins h
#align rbtree.eq_or_mem_of_mem_ins Std.RBSet.eq_or_mem_of_mem_ins

end Dec

theorem Std.RBSet.mem_of_min_eq [IsIrrefl α lt] {a : α} {t : Std.RBSet α lt} :
    t.min = some a → a ∈ t := by cases t; apply Std.RBNode.mem_of_min_eq
#align rbtree.mem_of_min_eq Std.RBSet.mem_of_min_eq

theorem Std.RBSet.mem_of_max_eq [IsIrrefl α lt] {a : α} {t : Std.RBSet α lt} :
    t.max = some a → a ∈ t := by cases t; apply Std.RBNode.mem_of_max_eq
#align rbtree.mem_of_max_eq Std.RBSet.mem_of_max_eq

theorem Std.RBSet.eq_leaf_of_min_eq_none {t : Std.RBSet α lt} :
    t.min = none → t = Std.mkRBSet α lt := by cases t; intro h; congr;
  apply Std.RBNode.eq_nil_of_min_eq_none h
#align rbtree.eq_leaf_of_min_eq_none Std.RBSet.eq_leaf_of_min_eq_none

theorem Std.RBSet.eq_leaf_of_max_eq_none {t : Std.RBSet α lt} :
    t.max = none → t = Std.mkRBSet α lt := by cases t; intro h; congr;
  apply Std.RBNode.eq_nil_of_max_eq_none h
#align rbtree.eq_leaf_of_max_eq_none Std.RBSet.eq_leaf_of_max_eq_none

theorem Std.RBSet.min_is_minimal [IsStrictWeakOrder α lt] {a : α} {t : Std.RBSet α lt} :
    t.min = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt a b := by
  classical
  cases t
  apply Std.RBNode.min_is_minimal
  apply Std.RBNode.isSearchableOfWellFormed
  assumption
#align rbtree.min_is_minimal Std.RBSet.min_is_minimal

theorem Std.RBSet.max_is_maximal [IsStrictWeakOrder α lt] {a : α} {t : Std.RBSet α lt} :
    t.max = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt b a := by cases t;
  apply Std.RBNode.max_is_maximal; apply Std.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.max_is_maximal Std.RBSet.max_is_maximal

end Std.RBSet

