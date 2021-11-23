import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Nat.Interval 
import Mathbin.Tactic.Linarith.Default

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/


universe u v w

open_locale BigOperators Nat

namespace Finset

variable{α : Type u}{β : Type v}{γ : Type w}{s₂ s₁ s : Finset α}{a : α}{g f : α → β}

theorem sum_Ico_add [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] [LocallyFiniteOrder α] [AddCommMonoidₓ β]
  (f : α → β) (a b c : α) : (∑x in Ico a b, f (c+x)) = ∑x in Ico (a+c) (b+c), f x :=
  by 
    classical 
    rw [←image_add_right_Ico, sum_image fun x hx y hy h => add_right_cancelₓ h]
    simpRw [add_commₓ]

@[toAdditive]
theorem prod_Ico_add [OrderedCancelAddCommMonoid α] [HasExistsAddOfLe α] [LocallyFiniteOrder α] [CommMonoidₓ β]
  (f : α → β) (a b c : α) : (∏x in Ico a b, f (c+x)) = ∏x in Ico (a+c) (b+c), f x :=
  @sum_Ico_add _ (Additive β) _ _ _ _ f a b c

variable[CommMonoidₓ β]

theorem sum_Ico_succ_top {δ : Type _} [AddCommMonoidₓ δ] {a b : ℕ} (hab : a ≤ b) (f : ℕ → δ) :
  (∑k in Ico a (b+1), f k) = (∑k in Ico a b, f k)+f b :=
  by 
    rw [Nat.Ico_succ_right_eq_insert_Ico hab, sum_insert right_not_mem_Ico, add_commₓ]

@[toAdditive]
theorem prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) : (∏k in Ico a (b+1), f k) = (∏k in Ico a b, f k)*f b :=
  @sum_Ico_succ_top (Additive β) _ _ _ hab _

theorem sum_eq_sum_Ico_succ_bot {δ : Type _} [AddCommMonoidₓ δ] {a b : ℕ} (hab : a < b) (f : ℕ → δ) :
  (∑k in Ico a b, f k) = f a+∑k in Ico (a+1) b, f k :=
  have ha : a ∉ Ico (a+1) b :=
    by 
      simp 
  by 
    rw [←sum_insert ha, Nat.Ico_insert_succ_left hab]

@[toAdditive]
theorem prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
  (∏k in Ico a b, f k) = f a*∏k in Ico (a+1) b, f k :=
  @sum_eq_sum_Ico_succ_bot (Additive β) _ _ _ hab _

@[toAdditive]
theorem prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
  ((∏i in Ico m n, f i)*∏i in Ico n k, f i) = ∏i in Ico m k, f i :=
  Ico_union_Ico_eq_Ico hmn hnk ▸ Eq.symm$ prod_union$ Ico_disjoint_Ico_consecutive m n k

@[toAdditive]
theorem prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
  ((∏k in range m, f k)*∏k in Ico m n, f k) = ∏k in range n, f k :=
  Nat.Ico_zero_eq_range ▸ Nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h

@[toAdditive]
theorem prod_Ico_eq_mul_inv {δ : Type _} [CommGroupₓ δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∏k in Ico m n, f k) = (∏k in range n, f k)*(∏k in range m, f k)⁻¹ :=
  eq_mul_inv_iff_mul_eq.2$
    by 
      rw [mul_commₓ] <;> exact prod_range_mul_prod_Ico f h

theorem sum_Ico_eq_sub {δ : Type _} [AddCommGroupₓ δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∑k in Ico m n, f k) = (∑k in range n, f k) - ∑k in range m, f k :=
  by 
    simpa only [sub_eq_add_neg] using sum_Ico_eq_add_neg f h

/-- The two ways of summing over `(i,j)` in the range `a<=i<=j<b` are equal. -/
theorem sum_Ico_Ico_comm {M : Type _} [AddCommMonoidₓ M] (a b : ℕ) (f : ℕ → ℕ → M) :
  (∑i in Finset.ico a b, ∑j in Finset.ico i b, f i j) = ∑j in Finset.ico a b, ∑i in Finset.ico a (j+1), f i j :=
  by 
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine'
        Finset.sum_bij' (fun x : Σi : ℕ, ℕ _ => (⟨x.2, x.1⟩ : Σi : ℕ, ℕ)) _ (fun _ _ => rfl)
          (fun x : Σi : ℕ, ℕ _ => (⟨x.2, x.1⟩ : Σi : ℕ, ℕ)) _
          (by 
            rintro ⟨⟩ _ <;> rfl)
          (by 
            rintro ⟨⟩ _ <;> rfl) <;>
      simp only [Finset.mem_Ico, Sigma.forall, Finset.mem_sigma] <;>
        rintro a b ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;> refine' ⟨⟨_, _⟩, ⟨_, _⟩⟩ <;> linarith

@[toAdditive]
theorem prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) : (∏k in Ico m n, f k) = ∏k in range (n - m), f (m+k) :=
  by 
    byCases' h : m ≤ n
    ·
      rw [←Nat.Ico_zero_eq_range, prod_Ico_add, zero_addₓ, tsub_add_cancel_of_le h]
    ·
      replace h : n ≤ m := le_of_not_geₓ h 
      rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty]

-- error in Algebra.BigOperators.Intervals: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_Ico_reflect
(f : exprℕ() → β)
(k : exprℕ())
{m n : exprℕ()}
(h : «expr ≤ »(m, «expr + »(n, 1))) : «expr = »(«expr∏ in , »((j), Ico k m, f «expr - »(n, j)), «expr∏ in , »((j), Ico «expr - »(«expr + »(n, 1), m) «expr - »(«expr + »(n, 1), k), f j)) :=
begin
  have [] [":", expr ∀ i «expr < » m, «expr ≤ »(i, n)] [],
  { intros [ident i, ident hi],
    exact [expr (add_le_add_iff_right 1).1 (le_trans (nat.lt_iff_add_one_le.1 hi) h)] },
  cases [expr lt_or_le k m] ["with", ident hkm, ident hkm],
  { rw ["[", "<-", expr nat.Ico_image_const_sub_eq_Ico (this _ hkm), "]"] [],
    refine [expr (prod_image _).symm],
    simp [] [] ["only"] ["[", expr mem_Ico, "]"] [] [],
    rintros [ident i, "⟨", ident ki, ",", ident im, "⟩", ident j, "⟨", ident kj, ",", ident jm, "⟩", ident Hij],
    rw ["[", "<-", expr tsub_tsub_cancel_of_le (this _ im), ",", expr Hij, ",", expr tsub_tsub_cancel_of_le (this _ jm), "]"] [] },
  { simp [] [] [] ["[", expr Ico_eq_empty_of_le, ",", expr tsub_le_tsub_left, ",", expr hkm, "]"] [] [] }
end

theorem sum_Ico_reflect {δ : Type _} [AddCommMonoidₓ δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ} (h : m ≤ n+1) :
  (∑j in Ico k m, f (n - j)) = ∑j in Ico ((n+1) - m) ((n+1) - k), f j :=
  @prod_Ico_reflect (Multiplicative δ) _ f k m n h

theorem prod_range_reflect (f : ℕ → β) (n : ℕ) : (∏j in range n, f (n - 1 - j)) = ∏j in range n, f j :=
  by 
    cases n
    ·
      simp 
    ·
      simp only [←Nat.Ico_zero_eq_range, Nat.succ_sub_succ_eq_sub, tsub_zero]
      rw [prod_Ico_reflect _ _ le_rfl]
      simp 

theorem sum_range_reflect {δ : Type _} [AddCommMonoidₓ δ] (f : ℕ → δ) (n : ℕ) :
  (∑j in range n, f (n - 1 - j)) = ∑j in range n, f j :=
  @prod_range_reflect (Multiplicative δ) _ f n

@[simp]
theorem prod_Ico_id_eq_factorial : ∀ n : ℕ, (∏x in Ico 1 (n+1), x) = n !
| 0 => rfl
| n+1 =>
  by 
    rw [prod_Ico_succ_top$ Nat.succ_le_succₓ$ zero_le n, Nat.factorial_succ, prod_Ico_id_eq_factorial n,
      Nat.succ_eq_add_one, mul_commₓ]

@[simp]
theorem prod_range_add_one_eq_factorial : ∀ n : ℕ, (∏x in range n, x+1) = n !
| 0 => rfl
| n+1 =>
  by 
    simp [Finset.range_succ, prod_range_add_one_eq_factorial n]

section GaussSum

/-- Gauss' summation formula -/
theorem sum_range_id_mul_two (n : ℕ) : ((∑i in range n, i)*2) = n*n - 1 :=
  calc ((∑i in range n, i)*2) = (∑i in range n, i)+∑i in range n, n - 1 - i :=
    by 
      rw [sum_range_reflect (fun i => i) n, mul_two]
    _ = ∑i in range n, i+n - 1 - i := sum_add_distrib.symm 
    _ = ∑i in range n, n - 1 := sum_congr rfl$ fun i hi => add_tsub_cancel_of_le$ Nat.le_pred_of_lt$ mem_range.1 hi 
    _ = n*n - 1 :=
    by 
      rw [sum_const, card_range, Nat.nsmul_eq_mul]
    

/-- Gauss' summation formula -/
theorem sum_range_id (n : ℕ) : (∑i in range n, i) = (n*n - 1) / 2 :=
  by 
    rw [←sum_range_id_mul_two n, Nat.mul_div_cancelₓ] <;>
      exact
        by 
          decide

end GaussSum

end Finset

