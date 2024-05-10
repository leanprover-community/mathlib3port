/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Data.Rbtree.Find
import Data.Rbtree.Insert
import Data.Rbtree.MinMax
import Order.RelClasses

#align_import data.rbtree.main from "leanprover-community/mathlib"@"4d4167104581a21259f7f448e1972a63a4546be7"

universe u

namespace Batteries.RBNode

variable {α : Type u} {lt : α → α → Prop}

theorem Batteries.RBNode.isSearchableOfWellFormed {t : Batteries.RBNode α}
    [IsStrictWeakOrder α lt] : t.WF lt → Batteries.RBNode.IsSearchable lt t none none :=
  by
  intro h; induction h
  · constructor; simp [lift]
  · subst h_n'; apply is_searchable_insert; assumption
#align rbnode.is_searchable_of_well_formed Batteries.RBNode.isSearchableOfWellFormed

open Color

theorem Batteries.RBNode.isRedBlack_of_wF {t : Batteries.RBNode α} :
    t.WF lt → ∃ c n, Batteries.RBNode.IsRedBlack t c n :=
  by
  intro h; induction h
  · exists black; exists 0; constructor
  · cases' h_ih with c ih; cases' ih with n ih; subst h_n'; apply insert_is_red_black; assumption
#align rbnode.is_red_black_of_well_formed Batteries.RBNode.isRedBlack_of_wF

end Batteries.RBNode

namespace Batteries.RBSet

variable {α : Type u} {lt : α → α → Prop}

theorem Batteries.RBSet.balanced (t : Batteries.RBSet α lt) : t.depth max ≤ 2 * t.depth min + 1 :=
  by
  cases' t with n p; simp only [depth]
  have := Batteries.RBNode.isRedBlack_of_wF p
  cases' this with _ this; cases' this with _ this
  apply Batteries.RBNode.balanced; assumption
#align rbtree.balanced Batteries.RBSet.balanced

theorem Batteries.RBSet.not_mem_mkRBSet : ∀ a : α, a ∉ Batteries.mkRBSet α lt := by
  simp [Membership.Mem, Batteries.RBSet.Mem, Batteries.RBNode.Mem, Batteries.mkRBSet]
#align rbtree.not_mem_mk_rbtree Batteries.RBSet.not_mem_mkRBSet

theorem Batteries.RBSet.not_mem_of_empty {t : Batteries.RBSet α lt} (a : α) :
    t.Empty = true → a ∉ t := by
  cases' t with n p <;> cases n <;>
    simp [Empty, Membership.Mem, Batteries.RBSet.Mem, Batteries.RBNode.Mem, false_imp_iff]
#align rbtree.not_mem_of_empty Batteries.RBSet.not_mem_of_empty

theorem Batteries.RBSet.mem_of_mem_of_eqv [IsStrictWeakOrder α lt] {t : Batteries.RBSet α lt}
    {a b : α} : a ∈ t → a ≈[lt]b → b ∈ t :=
  by
  cases' t with n p <;> simp [Membership.Mem, Batteries.RBSet.Mem] <;> clear p <;> induction n <;>
        simp only [Batteries.RBNode.Mem, StrictWeakOrder.Equiv, false_imp_iff] <;>
      intro h₁ h₂ <;>
    cases_type* or.1
  iterate 2 
    · have : Batteries.RBNode.Mem lt b n_lchild := n_ih_lchild h₁ h₂; simp [this]
    · simp [incomp_trans_of lt h₂.swap h₁]
    · have : Batteries.RBNode.Mem lt b n_rchild := n_ih_rchild h₁ h₂; simp [this]
#align rbtree.mem_of_mem_of_eqv Batteries.RBSet.mem_of_mem_of_eqv

section Dec

variable [DecidableRel lt]

theorem Batteries.RBSet.insert_ne_mkRBSet (t : Batteries.RBSet α lt) (a : α) :
    t.insert a ≠ Batteries.mkRBSet α lt :=
  by
  cases' t with n p
  simpa [insert, Batteries.mkRBSet] using Batteries.RBNode.insert_ne_nil lt n a
#align rbtree.insert_ne_mk_rbtree Batteries.RBSet.insert_ne_mkRBSet

theorem Batteries.RBSet.find?_correct [IsStrictWeakOrder α lt] (a : α) (t : Batteries.RBSet α lt) :
    a ∈ t ↔ ∃ b, t.find a = some b ∧ a ≈[lt]b := by cases t; apply Batteries.RBNode.find?_correct;
  apply Batteries.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_correct Batteries.RBSet.find?_correct

theorem Batteries.RBSet.find?_correct_of_total [IsStrictTotalOrder α lt] (a : α)
    (t : Batteries.RBSet α lt) : a ∈ t ↔ t.find a = some a :=
  Iff.intro
    (fun h =>
      match Iff.mp (Batteries.RBSet.find?_correct a t) h with
      | ⟨b, HEq, heqv⟩ => by simp [HEq, (eq_of_eqv_lt heqv).symm])
    fun h => Iff.mpr (Batteries.RBSet.find?_correct a t) ⟨a, ⟨h, refl a⟩⟩
#align rbtree.find_correct_of_total Batteries.RBSet.find?_correct_of_total

theorem Batteries.RBSet.find?_correct_exact [IsStrictTotalOrder α lt] (a : α)
    (t : Batteries.RBSet α lt) : Batteries.RBSet.MemExact a t ↔ t.find a = some a := by cases t;
  apply Batteries.RBNode.find?_correct_exact; apply Batteries.RBNode.isSearchableOfWellFormed;
  assumption
#align rbtree.find_correct_exact Batteries.RBSet.find?_correct_exact

theorem Batteries.RBSet.find?_insert_of_eqv [IsStrictWeakOrder α lt] (t : Batteries.RBSet α lt)
    {x y} : x ≈[lt]y → (t.insert x).find y = some x :=
  by
  cases t; intro h; apply Batteries.RBNode.find?_insert_of_eqv lt h;
  apply Batteries.RBNode.isSearchableOfWellFormed
  assumption
#align rbtree.find_insert_of_eqv Batteries.RBSet.find?_insert_of_eqv

#print Batteries.RBSet.find?_insert /-
theorem Batteries.RBSet.find?_insert [IsStrictWeakOrder α lt] (t : Batteries.RBSet α lt) (x) :
    (t.insert x).find x = some x :=
  Batteries.RBSet.find?_insert_of_eqv t (refl x)
#align rbtree.find_insert Batteries.RBSet.find?_insert
-/

theorem Batteries.RBSet.find?_insert_of_disj [IsStrictWeakOrder α lt] {x y : α}
    (t : Batteries.RBSet α lt) : lt x y ∨ lt y x → (t.insert x).find y = t.find y :=
  by
  cases t; intro h; apply Batteries.RBNode.find?_insert_of_disj lt h
  apply Batteries.RBNode.isSearchableOfWellFormed
  assumption
#align rbtree.find_insert_of_disj Batteries.RBSet.find?_insert_of_disj

theorem Batteries.RBSet.find?_insert_of_not_eqv [IsStrictWeakOrder α lt] {x y : α}
    (t : Batteries.RBSet α lt) : ¬x ≈[lt]y → (t.insert x).find y = t.find y :=
  by
  cases t; intro h; apply Batteries.RBNode.find?_insert_of_not_eqv lt h
  apply Batteries.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_insert_of_not_eqv Batteries.RBSet.find?_insert_of_not_eqv

#print Batteries.RBSet.find?_insert_of_ne /-
theorem Batteries.RBSet.find?_insert_of_ne [IsStrictTotalOrder α lt] {x y : α}
    (t : Batteries.RBSet α lt) : x ≠ y → (t.insert x).find y = t.find y :=
  by
  cases t; intro h
  have : ¬x ≈[lt]y := fun h' => h (eq_of_eqv_lt h')
  apply Batteries.RBNode.find?_insert_of_not_eqv lt this
  apply Batteries.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_insert_of_ne Batteries.RBSet.find?_insert_of_ne
-/

theorem Batteries.RBSet.not_mem_of_find?_none [IsStrictWeakOrder α lt] {a : α}
    {t : Batteries.RBSet α lt} : t.find a = none → a ∉ t := fun h =>
  Iff.mpr (not_congr (Batteries.RBSet.find?_correct a t)) <|
    by
    intro h
    cases' h with _ h; cases' h with h₁ h₂
    rw [h] at h₁; contradiction
#align rbtree.not_mem_of_find_none Batteries.RBSet.not_mem_of_find?_none

theorem Batteries.RBSet.eqv_of_find?_some [IsStrictWeakOrder α lt] {a b : α}
    {t : Batteries.RBSet α lt} : t.find a = some b → a ≈[lt]b := by cases t;
  apply Batteries.RBNode.eqv_of_find?_some; apply Batteries.RBNode.isSearchableOfWellFormed;
  assumption
#align rbtree.eqv_of_find_some Batteries.RBSet.eqv_of_find?_some

theorem Batteries.RBSet.eq_of_find?_some [IsStrictTotalOrder α lt] {a b : α}
    {t : Batteries.RBSet α lt} : t.find a = some b → a = b := fun h =>
  suffices a ≈[lt]b from eq_of_eqv_lt this
  Batteries.RBSet.eqv_of_find?_some h
#align rbtree.eq_of_find_some Batteries.RBSet.eq_of_find?_some

theorem Batteries.RBSet.mem_of_find?_some [IsStrictWeakOrder α lt] {a b : α}
    {t : Batteries.RBSet α lt} : t.find a = some b → a ∈ t := fun h =>
  Iff.mpr (Batteries.RBSet.find?_correct a t) ⟨b, ⟨h, Batteries.RBSet.eqv_of_find?_some h⟩⟩
#align rbtree.mem_of_find_some Batteries.RBSet.mem_of_find?_some

theorem Batteries.RBSet.find?_eq_find?_of_eqv [IsStrictWeakOrder α lt] {a b : α}
    (t : Batteries.RBSet α lt) : a ≈[lt]b → t.find a = t.find b :=
  by
  cases t; apply Batteries.RBNode.find?_eq_find?_of_eqv
  apply Batteries.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.find_eq_find_of_eqv Batteries.RBSet.find?_eq_find?_of_eqv

theorem Batteries.RBSet.contains_correct [IsStrictWeakOrder α lt] (a : α)
    (t : Batteries.RBSet α lt) : a ∈ t ↔ t.contains a = true :=
  by
  have h := find_correct a t
  simp [h, contains]; apply Iff.intro
  · intro h'; cases' h' with _ h'; cases h'; simp [*]; simp [Option.isSome]
  · intro h'
    cases' heq : find t a with v; simp [HEq, Option.isSome] at h'; contradiction
    exists v; simp; apply eqv_of_find_some HEq
#align rbtree.contains_correct Batteries.RBSet.contains_correct

theorem Batteries.RBSet.mem_insert_of_incomp {a b : α} (t : Batteries.RBSet α lt) :
    ¬lt a b ∧ ¬lt b a → a ∈ t.insert b := by cases t; apply Batteries.RBNode.mem_insert_of_incomp
#align rbtree.mem_insert_of_incomp Batteries.RBSet.mem_insert_of_incomp

#print Batteries.RBSet.mem_insert /-
theorem Batteries.RBSet.mem_insert [IsIrrefl α lt] :
    ∀ (a : α) (t : Batteries.RBSet α lt), a ∈ t.insert a := by intros; apply mem_insert_of_incomp;
  constructor <;> apply irrefl_of lt
#align rbtree.mem_insert Batteries.RBSet.mem_insert
-/

theorem Batteries.RBSet.mem_insert_of_equiv {a b : α} (t : Batteries.RBSet α lt) :
    a ≈[lt]b → a ∈ t.insert b := by cases t; apply Batteries.RBNode.mem_insert_of_incomp
#align rbtree.mem_insert_of_equiv Batteries.RBSet.mem_insert_of_equiv

#print Batteries.RBSet.mem_insert_of_mem /-
theorem Batteries.RBSet.mem_insert_of_mem [IsStrictWeakOrder α lt] {a : α}
    {t : Batteries.RBSet α lt} (b : α) : a ∈ t → a ∈ t.insert b := by cases t;
  apply Batteries.RBNode.mem_insert_of_mem
#align rbtree.mem_insert_of_mem Batteries.RBSet.mem_insert_of_mem
-/

theorem Batteries.RBSet.equiv_or_mem_of_mem_insert {a b : α} {t : Batteries.RBSet α lt} :
    a ∈ t.insert b → a ≈[lt]b ∨ a ∈ t := by cases t;
  apply Batteries.RBNode.equiv_or_mem_of_mem_insert
#align rbtree.equiv_or_mem_of_mem_insert Batteries.RBSet.equiv_or_mem_of_mem_insert

theorem Batteries.RBSet.incomp_or_mem_of_mem_ins {a b : α} {t : Batteries.RBSet α lt} :
    a ∈ t.insert b → ¬lt a b ∧ ¬lt b a ∨ a ∈ t :=
  Batteries.RBSet.equiv_or_mem_of_mem_insert
#align rbtree.incomp_or_mem_of_mem_ins Batteries.RBSet.incomp_or_mem_of_mem_ins

theorem Batteries.RBSet.eq_or_mem_of_mem_ins [IsStrictTotalOrder α lt] {a b : α}
    {t : Batteries.RBSet α lt} : a ∈ t.insert b → a = b ∨ a ∈ t := fun h =>
  suffices a ≈[lt]b ∨ a ∈ t by simp [eqv_lt_iff_eq] at this <;> assumption
  Batteries.RBSet.incomp_or_mem_of_mem_ins h
#align rbtree.eq_or_mem_of_mem_ins Batteries.RBSet.eq_or_mem_of_mem_ins

end Dec

theorem Batteries.RBSet.mem_of_min_eq [IsIrrefl α lt] {a : α} {t : Batteries.RBSet α lt} :
    t.min = some a → a ∈ t := by cases t; apply Batteries.RBNode.mem_of_min_eq
#align rbtree.mem_of_min_eq Batteries.RBSet.mem_of_min_eq

theorem Batteries.RBSet.mem_of_max_eq [IsIrrefl α lt] {a : α} {t : Batteries.RBSet α lt} :
    t.max = some a → a ∈ t := by cases t; apply Batteries.RBNode.mem_of_max_eq
#align rbtree.mem_of_max_eq Batteries.RBSet.mem_of_max_eq

theorem Batteries.RBSet.eq_leaf_of_min_eq_none {t : Batteries.RBSet α lt} :
    t.min = none → t = Batteries.mkRBSet α lt := by cases t; intro h; congr;
  apply Batteries.RBNode.eq_nil_of_min_eq_none h
#align rbtree.eq_leaf_of_min_eq_none Batteries.RBSet.eq_leaf_of_min_eq_none

theorem Batteries.RBSet.eq_leaf_of_max_eq_none {t : Batteries.RBSet α lt} :
    t.max = none → t = Batteries.mkRBSet α lt := by cases t; intro h; congr;
  apply Batteries.RBNode.eq_nil_of_max_eq_none h
#align rbtree.eq_leaf_of_max_eq_none Batteries.RBSet.eq_leaf_of_max_eq_none

theorem Batteries.RBSet.min_is_minimal [IsStrictWeakOrder α lt] {a : α} {t : Batteries.RBSet α lt} :
    t.min = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt a b := by
  classical
  cases t
  apply Batteries.RBNode.min_is_minimal
  apply Batteries.RBNode.isSearchableOfWellFormed
  assumption
#align rbtree.min_is_minimal Batteries.RBSet.min_is_minimal

theorem Batteries.RBSet.max_is_maximal [IsStrictWeakOrder α lt] {a : α} {t : Batteries.RBSet α lt} :
    t.max = some a → ∀ {b}, b ∈ t → a ≈[lt]b ∨ lt b a := by cases t;
  apply Batteries.RBNode.max_is_maximal; apply Batteries.RBNode.isSearchableOfWellFormed; assumption
#align rbtree.max_is_maximal Batteries.RBSet.max_is_maximal

end Batteries.RBSet

