import Mathbin.Data.Multiset.EraseDup 
import Mathbin.Data.List.MinMax

/-!
# The fold operation for a commutative associative operation over a multiset.
-/


namespace Multiset

variable{α β : Type _}

/-! ### fold -/


section Fold

variable(op : α → α → α)[hc : IsCommutative α op][ha : IsAssociative α op]

local notation a "*" b => op a b

include hc ha

/-- `fold op b s` folds a commutative associative operation `op` over
  the multiset `s`. -/
def fold : α → Multiset α → α :=
  foldr op (left_comm _ hc.comm ha.assoc)

theorem fold_eq_foldr (b : α) (s : Multiset α) : fold op b s = foldr op (left_comm _ hc.comm ha.assoc) b s :=
  rfl

@[simp]
theorem coe_fold_r (b : α) (l : List α) : fold op b l = l.foldr op b :=
  rfl

theorem coe_fold_l (b : α) (l : List α) : fold op b l = l.foldl op b :=
  (coe_foldr_swap op _ b l).trans$
    by 
      simp [hc.comm]

theorem fold_eq_foldl (b : α) (s : Multiset α) : fold op b s = foldl op (right_comm _ hc.comm ha.assoc) b s :=
  Quot.induction_on s$ fun l => coe_fold_l _ _ _

@[simp]
theorem fold_zero (b : α) : (0 : Multiset α).fold op b = b :=
  rfl

@[simp]
theorem fold_cons_left : ∀ b a : α s : Multiset α, (a ::ₘ s).fold op b = a*s.fold op b :=
  foldr_cons _ _

theorem fold_cons_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op b*a :=
  by 
    simp [hc.comm]

theorem fold_cons'_right (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (b*a) :=
  by 
    rw [fold_eq_foldl, foldl_cons, ←fold_eq_foldl]

theorem fold_cons'_left (b a : α) (s : Multiset α) : (a ::ₘ s).fold op b = s.fold op (a*b) :=
  by 
    rw [fold_cons'_right, hc.comm]

-- error in Data.Multiset.Fold: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fold_add
(b₁ b₂ : α)
(s₁
 s₂ : multiset α) : «expr = »(«expr + »(s₁, s₂).fold op «expr * »(b₁, b₂), «expr * »(s₁.fold op b₁, s₂.fold op b₂)) :=
multiset.induction_on s₂ (by rw ["[", expr add_zero, ",", expr fold_zero, ",", "<-", expr fold_cons'_right, ",", "<-", expr fold_cons_right op, "]"] []) (by simp [] [] [] [] [] [] { contextual := tt }; cc)

theorem fold_singleton (b a : α) : ({a} : Multiset α).fold op b = a*b :=
  foldr_singleton _ _ _ _

-- error in Data.Multiset.Fold: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fold_distrib
{f g : β → α}
(u₁ u₂ : α)
(s : multiset β) : «expr = »((s.map (λ
   x, «expr * »(f x, g x))).fold op «expr * »(u₁, u₂), «expr * »((s.map f).fold op u₁, (s.map g).fold op u₂)) :=
multiset.induction_on s (by simp [] [] [] [] [] []) (by simp [] [] [] [] [] [] { contextual := tt }; cc)

-- error in Data.Multiset.Fold: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fold_hom
{op' : β → β → β}
[is_commutative β op']
[is_associative β op']
{m : α → β}
(hm : ∀ x y, «expr = »(m (op x y), op' (m x) (m y)))
(b : α)
(s : multiset α) : «expr = »((s.map m).fold op' (m b), m (s.fold op b)) :=
multiset.induction_on s (by simp [] [] [] [] [] []) (by simp [] [] [] ["[", expr hm, "]"] [] [] { contextual := tt })

theorem fold_union_inter [DecidableEq α] (s₁ s₂ : Multiset α) (b₁ b₂ : α) :
  ((s₁ ∪ s₂).fold op b₁*(s₁ ∩ s₂).fold op b₂) = s₁.fold op b₁*s₂.fold op b₂ :=
  by 
    rw [←fold_add op, union_add_inter, fold_add op]

@[simp]
theorem fold_erase_dup_idem [DecidableEq α] [hi : IsIdempotent α op] (s : Multiset α) (b : α) :
  (erase_dup s).fold op b = s.fold op b :=
  Multiset.induction_on s
      (by 
        simp )$
    fun a s IH =>
      by 
        byCases' a ∈ s <;> simp [IH, h]
        show fold op b s = op a (fold op b s)
        rw [←cons_erase h, fold_cons_left, ←ha.assoc, hi.idempotent]

end Fold

section Order

theorem max_le_of_forall_le {α : Type _} [CanonicallyLinearOrderedAddMonoid α] (l : Multiset α) (n : α)
  (h : ∀ x _ : x ∈ l, x ≤ n) : l.fold max ⊥ ≤ n :=
  by 
    induction l using Quotientₓ.induction_on 
    simpa using List.max_le_of_forall_le _ _ h

theorem max_nat_le_of_forall_le (l : Multiset ℕ) (n : ℕ) (h : ∀ x _ : x ∈ l, x ≤ n) : l.fold max 0 ≤ n :=
  max_le_of_forall_le l n h

end Order

open Nat

theorem le_smul_erase_dup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • erase_dup s :=
  ⟨(s.map fun a => count a s).fold max 0,
    le_iff_count.2$
      fun a =>
        by 
          rw [count_nsmul]
          byCases' a ∈ s
          ·
            refine' le_transₓ _ (Nat.mul_le_mul_leftₓ _$ count_pos.2$ mem_erase_dup.2 h)
            have  : count a s ≤ fold max 0 (map (fun a => count a s) (a ::ₘ erase s a)) <;> [simp [le_max_leftₓ],
              simpa [cons_erase h]]
          ·
            simp [count_eq_zero.2 h, Nat.zero_leₓ]⟩

end Multiset

