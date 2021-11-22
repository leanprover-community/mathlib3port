import Mathbin.Algebra.GroupPower.Identities 
import Mathbin.Data.Zmod.Basic 
import Mathbin.FieldTheory.Finite.Basic 
import Mathbin.Data.Int.Parity 
import Mathbin.Data.Fintype.Card

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/


open Finset Polynomial FiniteField Equiv

open_locale BigOperators

namespace Int

theorem sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : (2*m) = (x^2)+y^2) : m = ((x - y) / 2^2)+(x+y) / 2^2 :=
  have  : Even ((x^2)+y^2) :=
    by 
      simp [h.symm, even_mul]
  have hxaddy : Even (x+y) :=
    by 
      simpa [sq] with parity_simps 
  have hxsuby : Even (x - y) :=
    by 
      simpa [sq] with parity_simps
  (mul_right_inj'
        (show (2*2 : ℤ) ≠ 0 from
          by 
            decide)).1$
    calc ((2*2)*m) = (x - y^2)+(x+y)^2 :=
      by 
        rw [mul_assocₓ, h] <;> ring 
      _ = ((2*(x - y) / 2)^2)+(2*(x+y) / 2)^2 :=
      by 
        rw [Int.mul_div_cancel' hxsuby, Int.mul_div_cancel' hxaddy]
      _ = (2*2)*((x - y) / 2^2)+(x+y) / 2^2 :=
      by 
        simp [mul_addₓ, pow_succₓ, mul_commₓ, mul_assocₓ, mul_left_commₓ]
      

theorem exists_sq_add_sq_add_one_eq_k (p : ℕ) [hp : Fact p.prime] :
  ∃ (a b : ℤ)(k : ℕ), ((((a^2)+b^2)+1) = k*p) ∧ k < p :=
  (hp.1.eq_two_or_odd.elim
      fun hp2 =>
        hp2.symm ▸
          ⟨1, 0, 1, rfl,
            by 
              decide⟩)$
    fun hp1 =>
      let ⟨a, b, hab⟩ := Zmod.sq_add_sq p (-1)
      have hab' : (p : ℤ) ∣ ((a.val_min_abs^2)+b.val_min_abs^2)+1 :=
        (CharP.int_cast_eq_zero_iff (Zmod p) p _).1$
          by 
            simpa [eq_neg_iff_add_eq_zero] using hab 
      let ⟨k, hk⟩ := hab' 
      have hk0 : 0 ≤ k :=
        nonneg_of_mul_nonneg_left
          (by 
            rw [←hk] <;> exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one)
          (Int.coe_nat_pos.2 hp.1.Pos)
      ⟨a.val_min_abs, b.val_min_abs, k.nat_abs,
        by 
          rw [hk, Int.nat_abs_of_nonneg hk0, mul_commₓ],
        lt_of_mul_lt_mul_left
          (calc (p*k.nat_abs) = ((a.val_min_abs.nat_abs^2)+b.val_min_abs.nat_abs^2)+1 :=
            by 
              rw [←Int.coe_nat_inj', Int.coe_nat_add, Int.coe_nat_add, Int.coe_nat_pow, Int.coe_nat_pow, Int.nat_abs_sq,
                Int.nat_abs_sq, Int.coe_nat_one, hk, Int.coe_nat_mul, Int.nat_abs_of_nonneg hk0]
            _ ≤ ((p / 2^2)+p / 2^2)+1 :=
            add_le_add
              (add_le_add (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _)
                (Nat.pow_le_pow_of_le_leftₓ (Zmod.nat_abs_val_min_abs_le _) _))
              (le_reflₓ _)
            _ < (((p / 2^2)+p / 2^2)+p % 2^2)+(2*p / 2^2)+(4*p / 2)*p % 2 :=
            by 
              rw [hp1, one_pow, mul_oneₓ] <;>
                exact
                  (lt_add_iff_pos_right _).2
                    (add_pos_of_nonneg_of_pos (Nat.zero_leₓ _)
                      (mul_pos
                        (by 
                          decide)
                        (Nat.div_pos hp.1.two_le
                          (by 
                            decide))))
            _ = p*p :=
            by 
              convRHS => rw [←Nat.mod_add_divₓ p 2]
              ring
            )
          (show 0 ≤ p from Nat.zero_leₓ _)⟩

end Int

namespace Nat

open Int

open_locale Classical

private theorem sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ} (h : ((((a^2)+b^2)+c^2)+d^2) = 2*m) :
  ∃ w x y z : ℤ, ((((w^2)+x^2)+y^2)+z^2) = m :=
  have  :
    ∀ f : Finₓ 4 → Zmod 2,
      ((((f 0^2)+f 1^2)+f 2^2)+f 3^2) = 0 →
        ∃ i : Finₓ 4, ((f i^2)+f (swap i 0 1)^2) = 0 ∧ ((f (swap i 0 2)^2)+f (swap i 0 3)^2) = 0 :=
    by 
      decide 
  let f : Finₓ 4 → ℤ := Vector.nth (a::ᵥb::ᵥc::ᵥd::ᵥVector.nil)
  let ⟨i, hσ⟩ :=
    this (coeₓ ∘ f)
      (by 
        rw [←@zero_mul (Zmod 2) _ m, ←show ((2 : ℤ) : Zmod 2) = 0 from rfl, ←Int.cast_mul, ←h] <;>
          simp only [Int.cast_add, Int.cast_pow] <;> rfl)
  let σ := swap i 0
  have h01 : 2 ∣ (f (σ 0)^2)+f (σ 1)^2 :=
    (CharP.int_cast_eq_zero_iff (Zmod 2) 2 _).1$
      by 
        simpa [σ] using hσ.1
  have h23 : 2 ∣ (f (σ 2)^2)+f (σ 3)^2 :=
    (CharP.int_cast_eq_zero_iff (Zmod 2) 2 _).1$
      by 
        simpa using hσ.2
  let ⟨x, hx⟩ := h01 
  let ⟨y, hy⟩ := h23
  ⟨(f (σ 0) - f (σ 1)) / 2, (f (σ 0)+f (σ 1)) / 2, (f (σ 2) - f (σ 3)) / 2, (f (σ 2)+f (σ 3)) / 2,
    by 
      rw [←Int.sq_add_sq_of_two_mul_sq_add_sq hx.symm, add_assocₓ, ←Int.sq_add_sq_of_two_mul_sq_add_sq hy.symm,
        ←mul_right_inj'
          (show (2 : ℤ) ≠ 0 from
            by 
              decide),
        ←h, mul_addₓ, ←hx, ←hy]
      have  : (∑x, f (σ x)^2) = ∑x, f x^2
      ·
        convRHS => rw [←σ.sum_comp]
      have fin4univ : (univ : Finset (Finₓ 4)).1 = 0 ::ₘ 1 ::ₘ 2 ::ₘ 3 ::ₘ 0 
      exact
        by 
          decide 
      simpa [Finset.sum_eq_multiset_sum, fin4univ, Multiset.sum_cons, f, add_assocₓ]⟩

-- error in NumberTheory.SumFourSquares: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exact: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
private
theorem prime_sum_four_squares
(p : exprℕ())
[hp : _root_.fact p.prime] : «expr∃ , »((a
  b
  c
  d : exprℤ()), «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), «expr ^ »(c, 2)), «expr ^ »(d, 2)), p)) :=
have hm : «expr∃ , »((m «expr < » p), «expr ∧ »(«expr < »(0, m), «expr∃ , »((a
    b
    c
    d : exprℤ()), «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), «expr ^ »(c, 2)), «expr ^ »(d, 2)), «expr * »(m, p))))), from let ⟨a, b, k, hk⟩ := exists_sq_add_sq_add_one_eq_k p in
⟨k, hk.2, «expr $ »(nat.pos_of_ne_zero, λ
  hk0, by { rw ["[", expr hk0, ",", expr int.coe_nat_zero, ",", expr zero_mul, "]"] ["at", ident hk],
    exact [expr ne_of_gt (show «expr > »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), 1), 0), from add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_lt_one) hk.1] }), a, b, 1, 0, by simpa [] [] [] ["[", expr sq, "]"] [] ["using", expr hk.1]⟩,
let m := nat.find hm in
let ⟨a, b, c, d, (habcd : «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), «expr ^ »(c, 2)), «expr ^ »(d, 2)), «expr * »(m, p)))⟩ := (nat.find_spec hm).snd.2 in
by haveI [ident hm0] [":", expr _root_.fact «expr < »(0, m)] [":=", expr ⟨(nat.find_spec hm).snd.1⟩]; exact [expr have hmp : «expr < »(m, p), from (nat.find_spec hm).fst,
 m.mod_two_eq_zero_or_one.elim (λ
  hm2 : «expr = »(«expr % »(m, 2), 0), let ⟨k, hk⟩ := (nat.dvd_iff_mod_eq_zero _ _).2 hm2 in
  have hk0 : «expr < »(0, k), from «expr $ »(nat.pos_of_ne_zero, λ
   _, by { simp [] [] [] ["[", "*", ",", expr lt_irrefl, "]"] [] ["at", "*"] }),
  have hkm : «expr < »(k, m), { rw ["[", expr hk, ",", expr two_mul, "]"] [],
    exact [expr (lt_add_iff_pos_left _).2 hk0] },
  «expr $ »(false.elim, nat.find_min hm hkm ⟨lt_trans hkm hmp, hk0, sum_four_squares_of_two_mul_sum_four_squares (show «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), «expr ^ »(c, 2)), «expr ^ »(d, 2)), «expr * »(2, «expr * »(k, p))), by { rw ["[", expr habcd, ",", expr hk, ",", expr int.coe_nat_mul, ",", expr mul_assoc, "]"] [],
       simp [] [] [] [] [] [] })⟩)) (λ
  hm2 : «expr = »(«expr % »(m, 2), 1), if hm1 : «expr = »(m, 1) then ⟨a, b, c, d, by simp [] [] ["only"] ["[", expr hm1, ",", expr habcd, ",", expr int.coe_nat_one, ",", expr one_mul, "]"] [] []⟩ else let w := (a : zmod m).val_min_abs,
      x := (b : zmod m).val_min_abs,
      y := (c : zmod m).val_min_abs,
      z := (d : zmod m).val_min_abs in
  have hnat_abs : «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(w, 2), «expr ^ »(x, 2)), «expr ^ »(y, 2)), «expr ^ »(z, 2)), («expr + »(«expr + »(«expr + »(«expr ^ »(w.nat_abs, 2), «expr ^ »(x.nat_abs, 2)), «expr ^ »(y.nat_abs, 2)), «expr ^ »(z.nat_abs, 2)) : exprℕ())), by simp [] [] [] ["[", expr sq, "]"] [] [],
  have hwxyzlt : «expr < »(«expr + »(«expr + »(«expr + »(«expr ^ »(w, 2), «expr ^ »(x, 2)), «expr ^ »(y, 2)), «expr ^ »(z, 2)), «expr ^ »(m, 2)), from calc
    «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(w, 2), «expr ^ »(x, 2)), «expr ^ »(y, 2)), «expr ^ »(z, 2)), («expr + »(«expr + »(«expr + »(«expr ^ »(w.nat_abs, 2), «expr ^ »(x.nat_abs, 2)), «expr ^ »(y.nat_abs, 2)), «expr ^ »(z.nat_abs, 2)) : exprℕ())) : hnat_abs
    «expr ≤ »(..., («expr + »(«expr + »(«expr + »(«expr ^ »(«expr / »(m, 2), 2), «expr ^ »(«expr / »(m, 2), 2)), «expr ^ »(«expr / »(m, 2), 2)), «expr ^ »(«expr / »(m, 2), 2)) : exprℕ())) : «expr $ »(int.coe_nat_le.2, add_le_add (add_le_add (add_le_add (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _) (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)) (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _)) (nat.pow_le_pow_of_le_left (zmod.nat_abs_val_min_abs_le _) _))
    «expr = »(..., «expr * »(4, «expr ^ »((«expr / »(m, 2) : exprℕ()), 2))) : by simp [] [] [] ["[", expr sq, ",", expr bit0, ",", expr bit1, ",", expr mul_add, ",", expr add_mul, ",", expr add_assoc, "]"] [] []
    «expr < »(..., «expr + »(«expr * »(4, «expr ^ »((«expr / »(m, 2) : exprℕ()), 2)), «expr + »(«expr * »((«expr * »(4, «expr / »(m, 2)) : exprℕ()), («expr % »(m, 2) : exprℕ())), «expr ^ »((«expr % »(m, 2) : exprℕ()), 2)))) : (lt_add_iff_pos_right _).2 (by { rw ["[", expr hm2, ",", expr int.coe_nat_one, ",", expr one_pow, ",", expr mul_one, "]"] [],
       exact [expr add_pos_of_nonneg_of_pos (int.coe_nat_nonneg _) zero_lt_one] })
    «expr = »(..., «expr ^ »(m, 2)) : by { conv_rhs [] [] { rw ["[", "<-", expr nat.mod_add_div m 2, "]"] },
      simp [] [] [] ["[", "-", ident nat.mod_add_div, ",", expr mul_add, ",", expr add_mul, ",", expr bit0, ",", expr bit1, ",", expr mul_comm, ",", expr mul_assoc, ",", expr mul_left_comm, ",", expr pow_add, ",", expr add_comm, ",", expr add_left_comm, "]"] [] [] },
  have hwxyzabcd : «expr = »(((«expr + »(«expr + »(«expr + »(«expr ^ »(w, 2), «expr ^ »(x, 2)), «expr ^ »(y, 2)), «expr ^ »(z, 2)) : exprℤ()) : zmod m), ((«expr + »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), «expr ^ »(c, 2)), «expr ^ »(d, 2)) : exprℤ()) : zmod m)), by simp [] [] [] ["[", expr w, ",", expr x, ",", expr y, ",", expr z, ",", expr sq, "]"] [] [],
  have hwxyz0 : «expr = »(((«expr + »(«expr + »(«expr + »(«expr ^ »(w, 2), «expr ^ »(x, 2)), «expr ^ »(y, 2)), «expr ^ »(z, 2)) : exprℤ()) : zmod m), 0), by rw ["[", expr hwxyzabcd, ",", expr habcd, ",", expr int.cast_mul, ",", expr cast_coe_nat, ",", expr zmod.nat_cast_self, ",", expr zero_mul, "]"] [],
  let ⟨n, hn⟩ := (char_p.int_cast_eq_zero_iff _ m _).1 hwxyz0 in
  have hn0 : «expr < »(0, n.nat_abs), from int.nat_abs_pos_of_ne_zero (λ
   hn0, have hwxyz0 : «expr = »((«expr + »(«expr + »(«expr + »(«expr ^ »(w.nat_abs, 2), «expr ^ »(x.nat_abs, 2)), «expr ^ »(y.nat_abs, 2)), «expr ^ »(z.nat_abs, 2)) : exprℕ()), 0), by { rw ["[", "<-", expr int.coe_nat_eq_zero, ",", "<-", expr hnat_abs, "]"] [],
     rwa ["[", expr hn0, ",", expr mul_zero, "]"] ["at", ident hn] },
   have habcd0 : «expr ∧ »(«expr ∣ »((m : exprℤ()), a), «expr ∧ »(«expr ∣ »((m : exprℤ()), b), «expr ∧ »(«expr ∣ »((m : exprℤ()), c), «expr ∣ »((m : exprℤ()), d)))), by simpa [] [] [] ["[", expr add_eq_zero_iff' (sq_nonneg (_ : exprℤ())) (sq_nonneg _), ",", expr pow_two, ",", expr w, ",", expr x, ",", expr y, ",", expr z, ",", expr char_p.int_cast_eq_zero_iff _ m _, ",", expr and.assoc, "]"] [] ["using", expr hwxyz0],
   let ⟨ma, hma⟩ := habcd0.1, ⟨mb, hmb⟩ := habcd0.2.1, ⟨mc, hmc⟩ := habcd0.2.2.1, ⟨md, hmd⟩ := habcd0.2.2.2 in
   have hmdvdp : «expr ∣ »(m, p), from int.coe_nat_dvd.1 ⟨«expr + »(«expr + »(«expr + »(«expr ^ »(ma, 2), «expr ^ »(mb, 2)), «expr ^ »(mc, 2)), «expr ^ »(md, 2)), «expr $ »((mul_right_inj' (show «expr ≠ »((m : exprℤ()), 0), from int.coe_nat_ne_zero_iff_pos.2 hm0.1)).1, by { rw ["[", "<-", expr habcd, ",", expr hma, ",", expr hmb, ",", expr hmc, ",", expr hmd, "]"] [],
       ring [] })⟩,
   (hp.1.2 _ hmdvdp).elim hm1 (λ
    hmeqp, by simpa [] [] [] ["[", expr lt_irrefl, ",", expr hmeqp, "]"] [] ["using", expr hmp])),
  have hawbxcydz : «expr ∣ »(((m : exprℕ()) : exprℤ()), «expr + »(«expr + »(«expr + »(«expr * »(a, w), «expr * »(b, x)), «expr * »(c, y)), «expr * »(d, z))), from «expr $ »((char_p.int_cast_eq_zero_iff (zmod m) m _).1, by { rw ["[", "<-", expr hwxyz0, "]"] [],
     simp [] [] [] [] [] [],
     ring [] }),
  have haxbwczdy : «expr ∣ »(((m : exprℕ()) : exprℤ()), «expr + »(«expr - »(«expr - »(«expr * »(a, x), «expr * »(b, w)), «expr * »(c, z)), «expr * »(d, y))), from «expr $ »((char_p.int_cast_eq_zero_iff (zmod m) m _).1, by { simp [] [] [] ["[", expr sub_eq_add_neg, "]"] [] [],
     ring [] }),
  have haybzcwdx : «expr ∣ »(((m : exprℕ()) : exprℤ()), «expr - »(«expr - »(«expr + »(«expr * »(a, y), «expr * »(b, z)), «expr * »(c, w)), «expr * »(d, x))), from «expr $ »((char_p.int_cast_eq_zero_iff (zmod m) m _).1, by { simp [] [] [] ["[", expr sub_eq_add_neg, "]"] [] [],
     ring [] }),
  have hazbycxdw : «expr ∣ »(((m : exprℕ()) : exprℤ()), «expr - »(«expr + »(«expr - »(«expr * »(a, z), «expr * »(b, y)), «expr * »(c, x)), «expr * »(d, w))), from «expr $ »((char_p.int_cast_eq_zero_iff (zmod m) m _).1, by { simp [] [] [] ["[", expr sub_eq_add_neg, "]"] [] [],
     ring [] }),
  let ⟨s, hs⟩ := hawbxcydz, ⟨t, ht⟩ := haxbwczdy, ⟨u, hu⟩ := haybzcwdx, ⟨v, hv⟩ := hazbycxdw in
  have hn_nonneg : «expr ≤ »(0, n), from nonneg_of_mul_nonneg_left (by { erw ["[", "<-", expr hn, "]"] [],
     repeat { try { refine [expr add_nonneg _ _] },
       try { exact [expr sq_nonneg _] } } }) (int.coe_nat_pos.2 hm0.1),
  have hnm : «expr < »(n.nat_abs, m), from int.coe_nat_lt.1 (lt_of_mul_lt_mul_left (by { rw ["[", expr int.nat_abs_of_nonneg hn_nonneg, ",", "<-", expr hn, ",", "<-", expr sq, "]"] [],
      exact [expr hwxyzlt] }) (int.coe_nat_nonneg m)),
  have hstuv : «expr = »(«expr + »(«expr + »(«expr + »(«expr ^ »(s, 2), «expr ^ »(t, 2)), «expr ^ »(u, 2)), «expr ^ »(v, 2)), «expr * »(n.nat_abs, p)), from «expr $ »((mul_right_inj' (show «expr ≠ »((«expr ^ »(m, 2) : exprℤ()), 0), from pow_ne_zero 2 (int.coe_nat_ne_zero_iff_pos.2 hm0.1))).1, calc
     «expr = »(«expr * »(«expr ^ »((m : exprℤ()), 2), «expr + »(«expr + »(«expr + »(«expr ^ »(s, 2), «expr ^ »(t, 2)), «expr ^ »(u, 2)), «expr ^ »(v, 2))), «expr + »(«expr + »(«expr + »(«expr ^ »(«expr * »((m : exprℕ()), s), 2), «expr ^ »(«expr * »((m : exprℕ()), t), 2)), «expr ^ »(«expr * »((m : exprℕ()), u), 2)), «expr ^ »(«expr * »((m : exprℕ()), v), 2))) : by { simp [] [] [] ["[", expr mul_pow, "]"] [] [],
       ring [] }
     «expr = »(..., «expr * »(«expr + »(«expr + »(«expr + »(«expr ^ »(w, 2), «expr ^ »(x, 2)), «expr ^ »(y, 2)), «expr ^ »(z, 2)), «expr + »(«expr + »(«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)), «expr ^ »(c, 2)), «expr ^ »(d, 2)))) : by { simp [] [] ["only"] ["[", expr hs.symm, ",", expr ht.symm, ",", expr hu.symm, ",", expr hv.symm, "]"] [] [],
       ring [] }
     «expr = »(..., _) : by { rw ["[", expr hn, ",", expr habcd, ",", expr int.nat_abs_of_nonneg hn_nonneg, "]"] [],
       dsimp [] ["[", expr m, "]"] [] [],
       ring [] }),
  «expr $ »(false.elim, nat.find_min hm hnm ⟨lt_trans hnm hmp, hn0, s, t, u, v, hstuv⟩))]

/-- **Four squares theorem** -/
theorem sum_four_squares : ∀ n : ℕ, ∃ a b c d : ℕ, ((((a^2)+b^2)+c^2)+d^2) = n
| 0 => ⟨0, 0, 0, 0, rfl⟩
| 1 => ⟨1, 0, 0, 0, rfl⟩
| n@(k+2) =>
  have hm : _root_.fact (min_fac (k+2)).Prime :=
    ⟨min_fac_prime
        (by 
          decide)⟩
  have  : n / min_fac n < n := factors_lemma 
  let ⟨a, b, c, d, h₁⟩ :=
    show ∃ a b c d : ℤ, ((((a^2)+b^2)+c^2)+d^2) = min_fac n by 
      exactI prime_sum_four_squares (min_fac (k+2))
  let ⟨w, x, y, z, h₂⟩ := sum_four_squares (n / min_fac n)
  ⟨((((a*w) - b*x) - c*y) - d*z).natAbs, ((((a*x)+b*w)+c*z) - d*y).natAbs, ((((a*y) - b*z)+c*w)+d*x).natAbs,
    ((((a*z)+b*y) - c*x)+d*w).natAbs,
    by 
      rw [←Int.coe_nat_inj', ←Nat.mul_div_cancel'ₓ (min_fac_dvd (k+2)), Int.coe_nat_mul, ←h₁, ←h₂]
      simp [sum_four_sq_mul_sum_four_sq]⟩

end Nat

