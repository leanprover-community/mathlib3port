import Mathbin.Algebra.BigOperators.Basic 
import Mathbin.Data.Nat.Prime 
import Mathbin.Data.Zmod.Basic

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/


open Finset

open_locale BigOperators

namespace Nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ :=
  ((range n).filter (Nat.Coprime n)).card

localized [Nat] notation "φ" => Nat.totient

@[simp]
theorem totient_zero : φ 0 = 0 :=
  rfl

@[simp]
theorem totient_one : φ 1 = 1 :=
  by 
    simp [totient]

theorem totient_eq_card_coprime (n : ℕ) : φ n = ((range n).filter (Nat.Coprime n)).card :=
  rfl

theorem totient_le (n : ℕ) : φ n ≤ n :=
  calc totient n ≤ (range n).card := card_filter_le _ _ 
    _ = n := card_range _
    

theorem totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
  calc totient n ≤ ((range n).filter (· ≠ 0)).card :=
    by 
      apply card_le_of_subset (monotone_filter_right _ _)
      intro n1 hn1 hn1' 
      simpa only [hn1', coprime_zero_right, hn.ne'] using hn1 
    _ = n - 1 :=
    by 
      simp only [filter_ne' (range n) 0, card_erase_of_mem, n.pred_eq_sub_one, card_range, pos_of_gt hn, mem_range]
    _ < n := Nat.sub_ltₓ (pos_of_gt hn) zero_lt_one
    

theorem totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
| 0 =>
  by 
    decide
| 1 =>
  by 
    simp [totient]
| n+2 =>
  fun h =>
    card_pos.2
      ⟨1,
        mem_filter.2
          ⟨mem_range.2
              (by 
                decide),
            coprime_one_right _⟩⟩

open Zmod

-- error in Data.Nat.Totient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Note this takes an explicit `fintype (units (zmod n))` argument to avoid trouble with instance
diamonds. -/
@[simp]
theorem _root_.zmod.card_units_eq_totient
(n : exprℕ())
[fact «expr < »(0, n)]
[fintype (units (zmod n))] : «expr = »(fintype.card (units (zmod n)), exprφ() n) :=
calc
  «expr = »(fintype.card (units (zmod n)), fintype.card {x : zmod n // x.val.coprime n}) : fintype.card_congr zmod.units_equiv_coprime
  «expr = »(..., exprφ() n) : begin
    apply [expr finset.card_congr (λ (a : {x : zmod n // x.val.coprime n}) (_), a.1.val)],
    { intro [ident a],
      simp [] [] [] ["[", expr (a : zmod n).val_lt, ",", expr a.prop.symm, "]"] [] [] { contextual := tt } },
    { intros ["_", "_", "_", "_", ident h],
      rw [expr subtype.ext_iff_val] [],
      apply [expr val_injective],
      exact [expr h] },
    { intros [ident b, ident hb],
      rw ["[", expr finset.mem_filter, ",", expr finset.mem_range, "]"] ["at", ident hb],
      refine [expr ⟨⟨b, _⟩, finset.mem_univ _, _⟩],
      { let [ident u] [] [":=", expr unit_of_coprime b hb.2.symm],
        exact [expr val_coe_unit_coprime u] },
      { show [expr «expr = »(zmod.val (b : zmod n), b)],
        rw ["[", expr val_nat_cast, ",", expr nat.mod_eq_of_lt hb.1, "]"] [] } }
  end

-- error in Data.Nat.Totient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem totient_mul
{m n : exprℕ()}
(h : m.coprime n) : «expr = »(exprφ() «expr * »(m, n), «expr * »(exprφ() m, exprφ() n)) :=
if hmn0 : «expr = »(«expr * »(m, n), 0) then by cases [expr nat.mul_eq_zero.1 hmn0] ["with", ident h, ident h]; simp [] [] ["only"] ["[", expr totient_zero, ",", expr mul_zero, ",", expr zero_mul, ",", expr h, "]"] [] [] else begin
  haveI [] [":", expr fact «expr < »(0, «expr * »(m, n))] [":=", expr ⟨nat.pos_of_ne_zero hmn0⟩],
  haveI [] [":", expr fact «expr < »(0, m)] [":=", expr ⟨«expr $ »(nat.pos_of_ne_zero, left_ne_zero_of_mul hmn0)⟩],
  haveI [] [":", expr fact «expr < »(0, n)] [":=", expr ⟨«expr $ »(nat.pos_of_ne_zero, right_ne_zero_of_mul hmn0)⟩],
  rw ["[", "<-", expr zmod.card_units_eq_totient, ",", "<-", expr zmod.card_units_eq_totient, ",", "<-", expr zmod.card_units_eq_totient, ",", expr fintype.card_congr (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv).to_equiv, ",", expr fintype.card_congr (@mul_equiv.prod_units (zmod m) (zmod n) _ _).to_equiv, ",", expr fintype.card_prod, "]"] []
end

theorem sum_totient (n : ℕ) : (∑m in (range n.succ).filter (· ∣ n), φ m) = n :=
  if hn0 : n = 0 then
    by 
      simp [hn0]
  else
    calc
      (∑m in (range n.succ).filter (· ∣ n), φ m) =
        ∑d in (range n.succ).filter (· ∣ n), ((range (n / d)).filter fun m => gcd (n / d) m = 1).card :=
      Eq.symm$
        sum_bij (fun d _ => n / d)
          (fun d hd =>
            mem_filter.2
              ⟨mem_range.2$ lt_succ_of_le$ Nat.div_le_selfₓ _ _,
                by 
                  conv  => toRHS rw [←Nat.mul_div_cancel'ₓ (mem_filter.1 hd).2] <;> simp ⟩)
          (fun _ _ => rfl)
          (fun a b ha hb h =>
            have ha : (a*n / a) = n := Nat.mul_div_cancel'ₓ (mem_filter.1 ha).2
            have  : 0 < n / a :=
              Nat.pos_of_ne_zeroₓ
                fun h =>
                  by 
                    simp_all [lt_irreflₓ]
            by 
              rw [←Nat.mul_left_inj this, ha, h, Nat.mul_div_cancel'ₓ (mem_filter.1 hb).2])
          fun b hb =>
            have hb : b < n.succ ∧ b ∣ n :=
              by 
                simpa [-range_succ] using hb 
            have hbn : n / b ∣ n :=
              ⟨b,
                by 
                  rw [Nat.div_mul_cancelₓ hb.2]⟩
            have hnb0 : n / b ≠ 0 :=
              fun h =>
                by 
                  simpa [h, Ne.symm hn0] using Nat.div_mul_cancelₓ hbn
            ⟨n / b, mem_filter.2 ⟨mem_range.2$ lt_succ_of_le$ Nat.div_le_selfₓ _ _, hbn⟩,
              by 
                rw [←Nat.mul_left_inj (Nat.pos_of_ne_zeroₓ hnb0), Nat.mul_div_cancel'ₓ hb.2, Nat.div_mul_cancelₓ hbn]⟩
      _ = ∑d in (range n.succ).filter (· ∣ n), ((range n).filter fun m => gcd n m = d).card :=
      sum_congr rfl
        fun d hd =>
          have hd : d ∣ n := (mem_filter.1 hd).2
          have hd0 : 0 < d := Nat.pos_of_ne_zeroₓ fun h => hn0 (eq_zero_of_zero_dvd$ h ▸ hd)
          card_congr (fun m hm => d*m)
            (fun m hm =>
              have hm : m < n / d ∧ gcd (n / d) m = 1 :=
                by 
                  simpa using hm 
              mem_filter.2
                ⟨mem_range.2$ Nat.mul_div_cancel'ₓ hd ▸ (mul_lt_mul_left hd0).2 hm.1,
                  by 
                    rw [←Nat.mul_div_cancel'ₓ hd, gcd_mul_left, hm.2, mul_oneₓ]⟩)
            (fun a b ha hb h => (Nat.mul_right_inj hd0).1 h)
            fun b hb =>
              have hb : b < n ∧ gcd n b = d :=
                by 
                  simpa using hb
              ⟨b / d,
                mem_filter.2
                  ⟨mem_range.2
                      ((mul_lt_mul_left (show 0 < d from hb.2 ▸ hb.2.symm ▸ hd0)).1
                        (by 
                          rw [←hb.2, Nat.mul_div_cancel'ₓ (gcd_dvd_left _ _),
                              Nat.mul_div_cancel'ₓ (gcd_dvd_right _ _)] <;>
                            exact hb.1)),
                    hb.2 ▸ coprime_div_gcd_div_gcd (hb.2.symm ▸ hd0)⟩,
                hb.2 ▸ Nat.mul_div_cancel'ₓ (gcd_dvd_right _ _)⟩
      _ = ((filter (· ∣ n) (range n.succ)).bUnion fun d => (range n).filter fun m => gcd n m = d).card :=
      (card_bUnion
          (by 
            intros  <;> apply disjoint_filter.2 <;> cc)).symm
        
      _ = (range n).card :=
      congr_argₓ card
        (Finset.ext
          fun m =>
            ⟨by 
                finish,
              fun hm =>
                have h : m < n := mem_range.1 hm 
                mem_bUnion.2
                  ⟨gcd n m,
                    mem_filter.2
                      ⟨mem_range.2 (lt_succ_of_le (le_of_dvd (lt_of_le_of_ltₓ (zero_le _) h) (gcd_dvd_left _ _))),
                        gcd_dvd_left _ _⟩,
                    mem_filter.2 ⟨hm, rfl⟩⟩⟩)
      _ = n := card_range _
      

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
theorem totient_prime_pow_succ {p : ℕ} (hp : p.prime) (n : ℕ) : φ (p ^ n+1) = (p ^ n)*p - 1 :=
  calc φ (p ^ n+1) = ((range (p ^ n+1)).filter (coprime (p ^ n+1))).card := totient_eq_card_coprime _ 
    _ = (range (p ^ n+1) \ (range (p ^ n)).Image (·*p)).card :=
    congr_argₓ card
      (by 
        rw [sdiff_eq_filter]
        apply filter_congr 
        simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
          hp.coprime_iff_not_dvd]
        intro a ha 
        split 
        ·
          rintro hap b _ rfl 
          exact hap (dvd_mul_left _ _)
        ·
          rintro h ⟨b, rfl⟩
          rw [pow_succₓ] at ha 
          exact h b (lt_of_mul_lt_mul_left ha (zero_le _)) (mul_commₓ _ _))
    _ = _ :=
    have h1 : Set.InjOn (·*p) (range (p ^ n)) := fun x _ y _ => (Nat.mul_left_inj hp.pos).1
    have h2 : (range (p ^ n)).Image (·*p) ⊆ range (p ^ n+1) :=
      fun a =>
        by 
          simp only [mem_image, mem_range, exists_imp_distrib]
          rintro b h rfl 
          rw [pow_succ'ₓ]
          exact (mul_lt_mul_right hp.pos).2 h 
    by 
      rw [card_sdiff h2, card_image_of_inj_on h1, card_range, card_range, ←one_mulₓ (p ^ n), pow_succₓ, ←tsub_mul,
        one_mulₓ, mul_commₓ]
    

/-- When `p` is prime, then the totient of `p ^ ` is `p ^ (n - 1) * (p - 1)` -/
theorem totient_prime_pow {p : ℕ} (hp : p.prime) {n : ℕ} (hn : 0 < n) : φ (p ^ n) = (p ^ (n - 1))*p - 1 :=
  by 
    rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩ <;> exact totient_prime_pow_succ hp _

theorem totient_prime {p : ℕ} (hp : p.prime) : φ p = p - 1 :=
  by 
    rw [←pow_oneₓ p, totient_prime_pow hp] <;> simp 

theorem totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.prime :=
  by 
    refine' ⟨fun h => _, totient_prime⟩
    replace hp : 1 < p
    ·
      apply lt_of_le_of_neₓ
      ·
        rwa [succ_le_iff]
      ·
        rintro rfl 
        rw [totient_one, tsub_self] at h 
        exact one_ne_zero h 
    rw [totient_eq_card_coprime, range_eq_Ico, ←Ico_insert_succ_left hp.le, Finset.filter_insert,
      if_neg (Tactic.NormNum.nat_coprime_helper_zero_right p hp), ←Nat.card_Ico 1 p] at h 
    refine' p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n$ finset.mem_Ico.mpr ⟨_, hn⟩
    rwa [succ_le_iff, pos_iff_ne_zero]

-- error in Data.Nat.Totient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_units_zmod_lt_sub_one
{p : exprℕ()}
(hp : «expr < »(1, p))
[fintype (units (zmod p))] : «expr ≤ »(fintype.card (units (zmod p)), «expr - »(p, 1)) :=
begin
  haveI [] [":", expr fact «expr < »(0, p)] [":=", expr ⟨zero_lt_one.trans hp⟩],
  rw [expr zmod.card_units_eq_totient p] [],
  exact [expr nat.le_pred_of_lt (nat.totient_lt p hp)]
end

-- error in Data.Nat.Totient: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prime_iff_card_units
(p : exprℕ())
[fintype (units (zmod p))] : «expr ↔ »(p.prime, «expr = »(fintype.card (units (zmod p)), «expr - »(p, 1))) :=
begin
  by_cases [expr hp, ":", expr «expr = »(p, 0)],
  { substI [expr hp],
    simp [] [] ["only"] ["[", expr zmod, ",", expr not_prime_zero, ",", expr false_iff, ",", expr zero_tsub, "]"] [] [],
    suffices [] [":", expr «expr ≠ »(fintype.card (units exprℤ()), 0)],
    { convert [] [expr this] [] },
    simp [] [] [] [] [] [] },
  haveI [] [":", expr fact «expr < »(0, p)] [":=", expr ⟨nat.pos_of_ne_zero hp⟩],
  rw ["[", expr zmod.card_units_eq_totient, ",", expr nat.totient_eq_iff_prime (fact.out «expr < »(0, p)), "]"] []
end

@[simp]
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans
    (by 
      normNum)

end Nat

