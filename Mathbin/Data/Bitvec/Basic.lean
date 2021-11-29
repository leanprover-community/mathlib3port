import Mathbin.Data.Bitvec.Core 
import Mathbin.Data.Fin.Basic 
import Mathbin.Tactic.NormNum 
import Mathbin.Tactic.Monotonicity.Default

namespace Bitvec

instance  (n : ℕ) : Preorderₓ (Bitvec n) :=
  Preorderₓ.lift Bitvec.toNat

/-- convert `fin` to `bitvec` -/
def of_fin {n : ℕ} (i : Finₓ$ 2 ^ n) : Bitvec n :=
  Bitvec.ofNat _ i.val

theorem of_fin_val {n : ℕ} (i : Finₓ$ 2 ^ n) : (of_fin i).toNat = i.val :=
  by 
    rw [of_fin, to_nat_of_nat, Nat.mod_eq_of_ltₓ] <;> apply i.is_lt

/-- convert `bitvec` to `fin` -/
def to_fin {n : ℕ} (i : Bitvec n) : Finₓ$ 2 ^ n :=
  @Finₓ.ofNat' _
    ⟨pow_pos
        (by 
          normNum)
        _⟩
    i.to_nat

theorem add_lsb_eq_twice_add_one {x b} : add_lsb x b = (2*x)+cond b 1 0 :=
  by 
    simp [add_lsb, two_mul]

theorem to_nat_eq_foldr_reverse {n : ℕ} (v : Bitvec n) : v.to_nat = v.to_list.reverse.foldr (flip add_lsb) 0 :=
  by 
    rw [List.foldr_reverse, flip] <;> rfl

-- error in Data.Bitvec.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem to_nat_lt {n : exprℕ()} (v : bitvec n) : «expr < »(v.to_nat, «expr ^ »(2, n)) :=
begin
  suffices [] [":", expr «expr ≤ »(«expr + »(v.to_nat, 1), «expr ^ »(2, n))],
  { simpa [] [] [] [] [] [] },
  rw [expr to_nat_eq_foldr_reverse] [],
  cases [expr v] ["with", ident xs, ident h],
  dsimp [] ["[", expr bitvec.to_nat, ",", expr bits_to_nat, "]"] [] [],
  rw ["<-", expr list.length_reverse] ["at", ident h],
  generalize_hyp [] [":"] [expr «expr = »(xs.reverse, ys)] ["at", "⊢", ident h],
  clear [ident xs],
  induction [expr ys] [] [] ["generalizing", ident n],
  { simp [] [] [] ["[", "<-", expr h, "]"] [] [] },
  { simp [] [] ["only"] ["[", "<-", expr h, ",", expr pow_add, ",", expr flip, ",", expr list.length, ",", expr list.foldr, ",", expr pow_one, "]"] [] [],
    rw ["[", expr add_lsb_eq_twice_add_one, "]"] [],
    transitivity [expr «expr + »(«expr * »(2, list.foldr (λ
        (x : bool)
        (y : exprℕ()), add_lsb y x) 0 ys_tl), «expr * »(2, 1))],
    { ac_mono [] [],
      rw [expr two_mul] [],
      mono [] [] [] [],
      cases [expr ys_hd] []; simp [] [] [] [] [] [] },
    { rw ["<-", expr left_distrib] [],
      ac_mono [] [],
      norm_num [] [],
      apply [expr ys_ih],
      refl } }
end

theorem add_lsb_div_two {x b} : add_lsb x b / 2 = x :=
  by 
    cases b <;>
      simp only [Nat.add_mul_div_leftₓ, add_lsb, ←two_mul, add_commₓ, Nat.succ_pos', Nat.mul_div_rightₓ, gt_iff_lt,
          zero_addₓ, cond] <;>
        normNum

theorem to_bool_add_lsb_mod_two {x b} : to_bool (add_lsb x b % 2 = 1) = b :=
  by 
    cases b <;>
      simp only [to_bool_iff, Nat.add_mul_mod_self_leftₓ, add_lsb, ←two_mul, add_commₓ, Bool.to_bool_false,
          Nat.mul_mod_rightₓ, zero_addₓ, cond, zero_ne_one] <;>
        normNum

theorem of_nat_to_nat {n : ℕ} (v : Bitvec n) : Bitvec.ofNat _ v.to_nat = v :=
  by 
    cases' v with xs h 
    ext1 
    change Vector.toList _ = xs 
    dsimp [Bitvec.toNat, bits_to_nat]
    rw [←List.length_reverse] at h 
    rw [←List.reverse_reverse xs, List.foldl_reverse]
    generalize xs.reverse = ys  at h⊢
    clear xs 
    induction ys generalizing n
    ·
      cases h 
      simp [Bitvec.ofNat]
    ·
      simp only [←Nat.succ_eq_add_one, List.length] at h 
      subst n 
      simp only [Bitvec.ofNat, Vector.to_list_cons, Vector.to_list_nil, List.reverse_cons, Vector.to_list_append,
        List.foldr]
      erw [add_lsb_div_two, to_bool_add_lsb_mod_two]
      congr 
      apply ys_ih 
      rfl

theorem to_fin_val {n : ℕ} (v : Bitvec n) : (to_fin v : ℕ) = v.to_nat :=
  by 
    rw [to_fin, Finₓ.coe_of_nat_eq_mod', Nat.mod_eq_of_ltₓ] <;> apply to_nat_lt

theorem to_fin_le_to_fin_of_le {n} {v₀ v₁ : Bitvec n} (h : v₀ ≤ v₁) : v₀.to_fin ≤ v₁.to_fin :=
  show (v₀.to_fin : ℕ) ≤ v₁.to_fin by 
    rw [to_fin_val, to_fin_val] <;> exact h

theorem of_fin_le_of_fin_of_le {n : ℕ} {i j : Finₓ (2 ^ n)} (h : i ≤ j) : of_fin i ≤ of_fin j :=
  show (Bitvec.ofNat n i).toNat ≤ (Bitvec.ofNat n j).toNat by 
    simp only [to_nat_of_nat, Nat.mod_eq_of_ltₓ, Finₓ.is_lt]
    exact h

theorem to_fin_of_fin {n} (i : Finₓ$ 2 ^ n) : (of_fin i).toFin = i :=
  Finₓ.eq_of_veq
    (by 
      simp [to_fin_val, of_fin, to_nat_of_nat, Nat.mod_eq_of_ltₓ, i.is_lt])

theorem of_fin_to_fin {n} (v : Bitvec n) : of_fin (to_fin v) = v :=
  by 
    dsimp [of_fin] <;> rw [to_fin_val, of_nat_to_nat]

end Bitvec

