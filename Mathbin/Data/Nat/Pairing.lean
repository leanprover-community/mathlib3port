import Mathbin.Data.Nat.Sqrt 
import Mathbin.Data.Set.Lattice

/-!
#  Naturals pairing function

This file defines a pairing function for the naturals as follows:
```text
 0  1  4  9 16
 2  3  5 10 17
 6  7  8 11 18
12 13 14 15 19
20 21 22 23 24
```

It has the advantage of being monotone in both directions and sending `⟦0, n^2 - 1⟧` to
`⟦0, n - 1⟧²`.
-/


open Prod Decidable Function

namespace Nat

/-- Pairing function for the natural numbers. -/
@[pp_nodot]
def mkpair (a b : ℕ) : ℕ :=
  if a < b then (b*b)+a else ((a*a)+a)+b

/-- Unpairing function for the natural numbers. -/
@[pp_nodot]
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n 
  if (n - s*s) < s then (n - s*s, s) else (s, (n - s*s) - s)

-- error in Data.Nat.Pairing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem mkpair_unpair (n : exprℕ()) : «expr = »(mkpair (unpair n).1 (unpair n).2, n) :=
begin
  dsimp ["only"] ["[", expr unpair, "]"] [] [],
  set [] [ident s] [] [":="] [expr sqrt n] [],
  have [ident sm] [":", expr «expr = »(«expr + »(«expr * »(s, s), «expr - »(n, «expr * »(s, s))), n)] [":=", expr add_tsub_cancel_of_le (sqrt_le _)],
  split_ifs [] [],
  { simp [] [] [] ["[", expr mkpair, ",", expr h, ",", expr sm, "]"] [] [] },
  { have [ident hl] [":", expr «expr ≤ »(«expr - »(«expr - »(n, «expr * »(s, s)), s), s)] [":=", expr tsub_le_iff_left.mpr «expr $ »(tsub_le_iff_left.mpr, by rw ["<-", expr add_assoc] []; apply [expr sqrt_le_add])],
    simp [] [] [] ["[", expr mkpair, ",", expr hl.not_lt, ",", expr add_assoc, ",", expr add_tsub_cancel_of_le (le_of_not_gt h), ",", expr sm, "]"] [] [] }
end

theorem mkpair_unpair' {n a b} (H : unpair n = (a, b)) : mkpair a b = n :=
  by 
    simpa [H] using mkpair_unpair n

-- error in Data.Nat.Pairing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem unpair_mkpair (a b : exprℕ()) : «expr = »(unpair (mkpair a b), (a, b)) :=
begin
  dunfold [ident mkpair] [],
  split_ifs [] [],
  { show [expr «expr = »(unpair «expr + »(«expr * »(b, b), a), (a, b))],
    have [ident be] [":", expr «expr = »(sqrt «expr + »(«expr * »(b, b), a), b)] [],
    from [expr sqrt_add_eq _ (le_trans (le_of_lt h) (nat.le_add_left _ _))],
    simp [] [] [] ["[", expr unpair, ",", expr be, ",", expr add_tsub_cancel_right, ",", expr h, "]"] [] [] },
  { show [expr «expr = »(unpair «expr + »(«expr + »(«expr * »(a, a), a), b), (a, b))],
    have [ident ae] [":", expr «expr = »(sqrt «expr + »(«expr * »(a, a), «expr + »(a, b)), a)] [],
    { rw [expr sqrt_add_eq] [],
      exact [expr add_le_add_left (le_of_not_gt h) _] },
    simp [] [] [] ["[", expr unpair, ",", expr ae, ",", expr nat.not_lt_zero, ",", expr add_assoc, "]"] [] [] }
end

theorem surjective_unpair : surjective unpair :=
  fun ⟨m, n⟩ => ⟨mkpair m n, unpair_mkpair m n⟩

-- error in Data.Nat.Pairing: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unpair_lt {n : exprℕ()} (n1 : «expr ≤ »(1, n)) : «expr < »((unpair n).1, n) :=
let s := sqrt n in
begin
  simp [] [] [] ["[", expr unpair, "]"] [] [],
  change [expr sqrt n] ["with", expr s] [],
  by_cases [expr h, ":", expr «expr < »(«expr - »(n, «expr * »(s, s)), s)]; simp [] [] [] ["[", expr h, "]"] [] [],
  { exact [expr lt_of_lt_of_le h (sqrt_le_self _)] },
  { simp [] [] [] [] [] ["at", ident h],
    have [ident s0] [":", expr «expr < »(0, s)] [":=", expr sqrt_pos.2 n1],
    exact [expr lt_of_le_of_lt h (tsub_lt_self n1 (mul_pos s0 s0))] }
end

@[simp]
theorem unpair_zero : unpair 0 = 0 :=
  by 
    rw [unpair]
    simp 

theorem unpair_left_le : ∀ n : ℕ, (unpair n).1 ≤ n
| 0 =>
  by 
    simp 
| n+1 => le_of_ltₓ (unpair_lt (Nat.succ_posₓ _))

theorem left_le_mkpair (a b : ℕ) : a ≤ mkpair a b :=
  by 
    simpa using unpair_left_le (mkpair a b)

theorem right_le_mkpair (a b : ℕ) : b ≤ mkpair a b :=
  by 
    byCases' h : a < b <;> simp [mkpair, h]
    exact le_transₓ (le_mul_self _) (Nat.le_add_rightₓ _ _)

theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n :=
  by 
    simpa using right_le_mkpair n.unpair.1 n.unpair.2

theorem mkpair_lt_mkpair_left {a₁ a₂} b (h : a₁ < a₂) : mkpair a₁ b < mkpair a₂ b :=
  by 
    byCases' h₁ : a₁ < b <;> simp [mkpair, h₁, add_assocₓ]
    ·
      byCases' h₂ : a₂ < b <;> simp [mkpair, h₂, h]
      simp  at h₂ 
      apply add_lt_add_of_le_of_lt 
      exact mul_self_le_mul_self h₂ 
      exact lt_add_right _ _ _ h
    ·
      simp  at h₁ 
      simp [not_lt_of_gtₓ (lt_of_le_of_ltₓ h₁ h)]
      apply add_lt_add 
      exact mul_self_lt_mul_self h 
      apply add_lt_add_right <;> assumption

theorem mkpair_lt_mkpair_right a {b₁ b₂} (h : b₁ < b₂) : mkpair a b₁ < mkpair a b₂ :=
  by 
    byCases' h₁ : a < b₁ <;> simp [mkpair, h₁, add_assocₓ]
    ·
      simp [mkpair, lt_transₓ h₁ h, h]
      exact mul_self_lt_mul_self h
    ·
      byCases' h₂ : a < b₂ <;> simp [mkpair, h₂, h]
      simp  at h₁ 
      rw [add_commₓ, add_commₓ _ a, add_assocₓ, add_lt_add_iff_left]
      rwa [add_commₓ, ←sqrt_lt, sqrt_add_eq]
      exact le_transₓ h₁ (Nat.le_add_leftₓ _ _)

end Nat

open Nat

section CompleteLattice

theorem supr_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) : (⨆n : ℕ, f n.unpair.1 n.unpair.2) = ⨆i j : ℕ, f i j :=
  by 
    rw [←(supr_prod : (⨆i : ℕ × ℕ, f i.1 i.2) = _), ←nat.surjective_unpair.supr_comp]

theorem infi_unpair {α} [CompleteLattice α] (f : ℕ → ℕ → α) : (⨅n : ℕ, f n.unpair.1 n.unpair.2) = ⨅i j : ℕ, f i j :=
  supr_unpair (show ℕ → ℕ → OrderDual α from f)

end CompleteLattice

namespace Set

theorem Union_unpair_prod {α β} {s : ℕ → Set α} {t : ℕ → Set β} :
  (⋃n : ℕ, (s n.unpair.fst).Prod (t n.unpair.snd)) = (⋃n, s n).Prod (⋃n, t n) :=
  by 
    rw [←Union_prod]
    convert surjective_unpair.Union_comp _ 
    rfl

theorem Union_unpair {α} (f : ℕ → ℕ → Set α) : (⋃n : ℕ, f n.unpair.1 n.unpair.2) = ⋃i j : ℕ, f i j :=
  supr_unpair f

theorem Inter_unpair {α} (f : ℕ → ℕ → Set α) : (⋂n : ℕ, f n.unpair.1 n.unpair.2) = ⋂i j : ℕ, f i j :=
  infi_unpair f

end Set

