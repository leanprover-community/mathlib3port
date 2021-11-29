import Mathbin.Data.Polynomial.Inductions 
import Mathbin.Data.Polynomial.Monic 
import Mathbin.RingTheory.Multiplicity

/-!
# Division of univariate polynomials

The main defs are `div_by_monic` and `mod_by_monic`.
The compatibility between these is given by `mod_by_monic_add_div`.
We also define `root_multiplicity`.
-/


noncomputable theory

open_locale Classical BigOperators

open Finset

namespace Polynomial

universe u v w z

variable{R : Type u}{S : Type v}{T : Type w}{A : Type z}{a b : R}{n : ℕ}

section CommSemiringₓ

variable[CommSemiringₓ R]

theorem X_dvd_iff {α : Type u} [CommSemiringₓ α] {f : Polynomial α} : X ∣ f ↔ f.coeff 0 = 0 :=
  ⟨fun ⟨g, hfg⟩ =>
      by 
        rw [hfg, mul_commₓ, coeff_mul_X_zero],
    fun hf =>
      ⟨f.div_X,
        by 
          rw [mul_commₓ, ←add_zeroₓ (f.div_X*X), ←C_0, ←hf, div_X_mul_X_add]⟩⟩

end CommSemiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R]{p q : Polynomial R}

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem multiplicity_finite_of_degree_pos_of_monic
(hp : «expr < »((0 : with_bot exprℕ()), degree p))
(hmp : monic p)
(hq : «expr ≠ »(q, 0)) : multiplicity.finite p q :=
have zn0 : «expr ≠ »((0 : R), 1), from λ
h, by haveI [] [] [":=", expr subsingleton_of_zero_eq_one h]; exact [expr hq (subsingleton.elim _ _)],
⟨nat_degree q, λ
 ⟨r, hr⟩, have hp0 : «expr ≠ »(p, 0), from λ
 hp0, by simp [] [] [] ["[", expr hp0, "]"] [] ["at", ident hp]; contradiction,
 have hr0 : «expr ≠ »(r, 0), from λ hr0, by simp [] [] [] ["*"] [] ["at", "*"],
 have hpn1 : «expr = »(«expr ^ »(leading_coeff p, «expr + »(nat_degree q, 1)), 1), by simp [] [] [] ["[", expr show «expr = »(_, _), from hmp, "]"] [] [],
 have hpn0' : «expr ≠ »(«expr ^ »(leading_coeff p, «expr + »(nat_degree q, 1)), 0), from «expr ▸ »(hpn1.symm, zn0.symm),
 have hpnr0 : «expr ≠ »(«expr * »(leading_coeff «expr ^ »(p, «expr + »(nat_degree q, 1)), leading_coeff r), 0), by simp [] [] ["only"] ["[", expr leading_coeff_pow' hpn0', ",", expr leading_coeff_eq_zero, ",", expr hpn1, ",", expr one_pow, ",", expr one_mul, ",", expr ne.def, ",", expr hr0, "]"] [] []; simp [] [] [] [] [] [],
 have hnp : «expr < »(0, nat_degree p), by rw ["[", "<-", expr with_bot.coe_lt_coe, ",", "<-", expr degree_eq_nat_degree hp0, "]"] []; exact [expr hp],
 begin
   have [] [] [":=", expr congr_arg nat_degree hr],
   rw ["[", expr nat_degree_mul' hpnr0, ",", expr nat_degree_pow' hpn0', ",", expr add_mul, ",", expr add_assoc, "]"] ["at", ident this],
   exact [expr ne_of_lt (lt_add_of_le_of_pos (le_mul_of_one_le_right (nat.zero_le _) hnp) (add_pos_of_pos_of_nonneg (by rwa [expr one_mul] []) (nat.zero_le _))) this]
 end⟩

end CommSemiringₓ

section Ringₓ

variable[Ringₓ R]{p q : Polynomial R}

theorem div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
  degree (p - (C (leading_coeff p)*X ^ (nat_degree p - nat_degree q))*q) < degree p :=
  have hp : leading_coeff p ≠ 0 := mt leading_coeff_eq_zero.1 h.2
  if h0 : (p - (C (leading_coeff p)*X ^ (nat_degree p - nat_degree q))*q) = 0 then
    h0.symm ▸ (lt_of_not_geₓ$ mt le_bot_iff.1 (mt degree_eq_bot.1 h.2)) else
    have hq0 : q ≠ 0 := hq.ne_zero_of_polynomial_ne h.2
    have hlt : nat_degree q ≤ nat_degree p :=
      WithBot.coe_le_coe.1
        (by 
          rw [←degree_eq_nat_degree h.2, ←degree_eq_nat_degree hq0] <;> exact h.1)
    degree_sub_lt
      (by 
        rw [hq.degree_mul, degree_C_mul_X_pow _ hp, degree_eq_nat_degree h.2, degree_eq_nat_degree hq0,
          ←WithBot.coe_add, tsub_add_cancel_of_le hlt])
      h.2
      (by 
        rw [leading_coeff_mul_monic hq, leading_coeff_mul_X_pow, leading_coeff_C])

/-- See `div_by_monic`. -/
noncomputable def div_mod_by_monic_aux : ∀ (p : Polynomial R) {q : Polynomial R}, monic q → Polynomial R × Polynomial R
| p =>
  fun q hq =>
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      let z := C (leading_coeff p)*X ^ (nat_degree p - nat_degree q)
      have wf := div_wf_lemma h hq 
      let dm := div_mod_by_monic_aux (p - z*q) hq
      ⟨z+dm.1, dm.2⟩
    else ⟨0, p⟩

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : Polynomial R) : Polynomial R :=
  if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : Polynomial R) : Polynomial R :=
  if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl:70 " /ₘ " => div_by_monic

infixl:70 " %ₘ " => mod_by_monic

theorem degree_mod_by_monic_lt [Nontrivial R] :
  ∀ (p : Polynomial R) {q : Polynomial R} (hq : monic q), degree (p %ₘ q) < degree q
| p =>
  fun q hq =>
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      have wf := div_wf_lemma ⟨h.1, h.2⟩ hq 
      have  : degree ((p - (C (leading_coeff p)*X ^ (nat_degree p - nat_degree q))*q) %ₘ q) < degree q :=
        degree_mod_by_monic_lt (p - (C (leading_coeff p)*X ^ (nat_degree p - nat_degree q))*q) hq 
      by 
        unfold mod_by_monic  at this⊢
        unfold div_mod_by_monic_aux 
        rw [dif_pos hq] at this⊢
        rw [if_pos h]
        exact this
    else
      Or.cases_on (not_and_distrib.1 h)
        (by 
          unfold mod_by_monic div_mod_by_monic_aux 
          rw [dif_pos hq, if_neg h]
          exact lt_of_not_geₓ)
        (by 
          intro hp 
          unfold mod_by_monic div_mod_by_monic_aux 
          rw [dif_pos hq, if_neg h, not_not.1 hp]
          exact lt_of_le_of_neₓ bot_le (Ne.symm (mt degree_eq_bot.1 hq.ne_zero)))

@[simp]
theorem zero_mod_by_monic (p : Polynomial R) : 0 %ₘ p = 0 :=
  by 
    unfold mod_by_monic div_mod_by_monic_aux 
    byCases' hp : monic p
    ·
      rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl))]
    ·
      rw [dif_neg hp]

@[simp]
theorem zero_div_by_monic (p : Polynomial R) : 0 /ₘ p = 0 :=
  by 
    unfold div_by_monic div_mod_by_monic_aux 
    byCases' hp : monic p
    ·
      rw [dif_pos hp, if_neg (mt And.right (not_not_intro rfl))]
    ·
      rw [dif_neg hp]

@[simp]
theorem mod_by_monic_zero (p : Polynomial R) : p %ₘ 0 = p :=
  if h : monic (0 : Polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
    by 
      unfold mod_by_monic div_mod_by_monic_aux <;> rw [dif_neg h]

@[simp]
theorem div_by_monic_zero (p : Polynomial R) : p /ₘ 0 = 0 :=
  if h : monic (0 : Polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
    by 
      unfold div_by_monic div_mod_by_monic_aux <;> rw [dif_neg h]

theorem div_by_monic_eq_of_not_monic (p : Polynomial R) (hq : ¬monic q) : p /ₘ q = 0 :=
  dif_neg hq

theorem mod_by_monic_eq_of_not_monic (p : Polynomial R) (hq : ¬monic q) : p %ₘ q = p :=
  dif_neg hq

theorem mod_by_monic_eq_self_iff [Nontrivial R] (hq : monic q) : p %ₘ q = p ↔ degree p < degree q :=
  ⟨fun h => h ▸ degree_mod_by_monic_lt _ hq,
    fun h =>
      have  : ¬degree q ≤ degree p := not_le_of_gtₓ h 
      by 
        unfold mod_by_monic div_mod_by_monic_aux <;> rw [dif_pos hq, if_neg (mt And.left this)]⟩

theorem degree_mod_by_monic_le (p : Polynomial R) {q : Polynomial R} (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
  by 
    nontriviality R 
    exact (degree_mod_by_monic_lt _ hq).le

end Ringₓ

section CommRingₓ

variable[CommRingₓ R]{p q : Polynomial R}

theorem mod_by_monic_eq_sub_mul_div : ∀ (p : Polynomial R) {q : Polynomial R} (hq : monic q), p %ₘ q = p - q*p /ₘ q
| p =>
  fun q hq =>
    if h : degree q ≤ degree p ∧ p ≠ 0 then
      have wf := div_wf_lemma h hq 
      have ih := mod_by_monic_eq_sub_mul_div (p - (C (leading_coeff p)*X ^ (nat_degree p - nat_degree q))*q) hq 
      by 
        unfold mod_by_monic div_by_monic div_mod_by_monic_aux 
        rw [dif_pos hq, if_pos h]
        rw [mod_by_monic, dif_pos hq] at ih 
        refine' ih.trans _ 
        unfold div_by_monic 
        rw [dif_pos hq, dif_pos hq, if_pos h, mul_addₓ, sub_add_eq_sub_sub, mul_commₓ]
    else
      by 
        unfold mod_by_monic div_by_monic div_mod_by_monic_aux 
        rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]

theorem mod_by_monic_add_div (p : Polynomial R) {q : Polynomial R} (hq : monic q) : ((p %ₘ q)+q*p /ₘ q) = p :=
  eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem div_by_monic_eq_zero_iff
[nontrivial R]
(hq : monic q) : «expr ↔ »(«expr = »(«expr /ₘ »(p, q), 0), «expr < »(degree p, degree q)) :=
⟨λ
 h, by have [] [] [":=", expr mod_by_monic_add_div p hq]; rwa ["[", expr h, ",", expr mul_zero, ",", expr add_zero, ",", expr mod_by_monic_eq_self_iff hq, "]"] ["at", ident this], λ
 h, have «expr¬ »(«expr ≤ »(degree q, degree p)) := not_le_of_gt h,
 by unfold [ident div_by_monic, ident div_mod_by_monic_aux] []; rw ["[", expr dif_pos hq, ",", expr if_neg (mt and.left this), "]"] []⟩

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_add_div_by_monic
(hq : monic q)
(h : «expr ≤ »(degree q, degree p)) : «expr = »(«expr + »(degree q, degree «expr /ₘ »(p, q)), degree p) :=
begin
  nontriviality [expr R] [],
  have [ident hdiv0] [":", expr «expr ≠ »(«expr /ₘ »(p, q), 0)] [":=", expr by rwa ["[", expr («expr ≠ »), ",", expr div_by_monic_eq_zero_iff hq, ",", expr not_lt, "]"] []],
  have [ident hlc] [":", expr «expr ≠ »(«expr * »(leading_coeff q, leading_coeff «expr /ₘ »(p, q)), 0)] [":=", expr by rwa ["[", expr monic.def.1 hq, ",", expr one_mul, ",", expr («expr ≠ »), ",", expr leading_coeff_eq_zero, "]"] []],
  have [ident hmod] [":", expr «expr < »(degree «expr %ₘ »(p, q), degree «expr * »(q, «expr /ₘ »(p, q)))] [":=", expr calc
     «expr < »(degree «expr %ₘ »(p, q), degree q) : degree_mod_by_monic_lt _ hq
     «expr ≤ »(..., _) : by rw ["[", expr degree_mul' hlc, ",", expr degree_eq_nat_degree hq.ne_zero, ",", expr degree_eq_nat_degree hdiv0, ",", "<-", expr with_bot.coe_add, ",", expr with_bot.coe_le_coe, "]"] []; exact [expr nat.le_add_right _ _]],
  calc
    «expr = »(«expr + »(degree q, degree «expr /ₘ »(p, q)), degree «expr * »(q, «expr /ₘ »(p, q))) : eq.symm (degree_mul' hlc)
    «expr = »(..., degree «expr + »(«expr %ₘ »(p, q), «expr * »(q, «expr /ₘ »(p, q)))) : (degree_add_eq_right_of_degree_lt hmod).symm
    «expr = »(..., _) : congr_arg _ (mod_by_monic_add_div _ hq)
end

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_div_by_monic_le (p q : polynomial R) : «expr ≤ »(degree «expr /ₘ »(p, q), degree p) :=
if hp0 : «expr = »(p, 0) then by simp [] [] ["only"] ["[", expr hp0, ",", expr zero_div_by_monic, ",", expr le_refl, "]"] [] [] else if hq : monic q then if h : «expr ≤ »(degree q, degree p) then by haveI [] [] [":=", expr nontrivial.of_polynomial_ne hp0]; rw ["[", "<-", expr degree_add_div_by_monic hq h, ",", expr degree_eq_nat_degree hq.ne_zero, ",", expr degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq).1 (not_lt.2 h)), "]"] []; exact [expr with_bot.coe_le_coe.2 (nat.le_add_left _ _)] else by unfold [ident div_by_monic, ident div_mod_by_monic_aux] []; simp [] [] ["only"] ["[", expr dif_pos hq, ",", expr h, ",", expr false_and, ",", expr if_false, ",", expr degree_zero, ",", expr bot_le, "]"] [] [] else «expr ▸ »((div_by_monic_eq_of_not_monic p hq).symm, bot_le)

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem degree_div_by_monic_lt
(p : polynomial R)
{q : polynomial R}
(hq : monic q)
(hp0 : «expr ≠ »(p, 0))
(h0q : «expr < »(0, degree q)) : «expr < »(degree «expr /ₘ »(p, q), degree p) :=
if hpq : «expr < »(degree p, degree q) then begin
  haveI [] [] [":=", expr nontrivial.of_polynomial_ne hp0],
  rw ["[", expr (div_by_monic_eq_zero_iff hq).2 hpq, ",", expr degree_eq_nat_degree hp0, "]"] [],
  exact [expr with_bot.bot_lt_coe _]
end else begin
  haveI [] [] [":=", expr nontrivial.of_polynomial_ne hp0],
  rw ["[", "<-", expr degree_add_div_by_monic hq (not_lt.1 hpq), ",", expr degree_eq_nat_degree hq.ne_zero, ",", expr degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq).1 hpq), "]"] [],
  exact [expr with_bot.coe_lt_coe.2 (nat.lt_add_of_pos_left «expr $ »(with_bot.coe_lt_coe.1, «expr ▸ »(degree_eq_nat_degree hq.ne_zero, h0q)))]
end

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_degree_div_by_monic
{R : Type u}
[comm_ring R]
(f : polynomial R)
{g : polynomial R}
(hg : g.monic) : «expr = »(nat_degree «expr /ₘ »(f, g), «expr - »(nat_degree f, nat_degree g)) :=
begin
  by_cases [expr h01, ":", expr «expr = »((0 : R), 1)],
  { haveI [] [] [":=", expr subsingleton_of_zero_eq_one h01],
    rw ["[", expr subsingleton.elim «expr /ₘ »(f, g) 0, ",", expr subsingleton.elim f 0, ",", expr subsingleton.elim g 0, ",", expr nat_degree_zero, "]"] [] },
  haveI [] [":", expr nontrivial R] [":=", expr ⟨⟨0, 1, h01⟩⟩],
  by_cases [expr hfg, ":", expr «expr = »(«expr /ₘ »(f, g), 0)],
  { rw ["[", expr hfg, ",", expr nat_degree_zero, "]"] [],
    rw [expr div_by_monic_eq_zero_iff hg] ["at", ident hfg],
    rw [expr tsub_eq_zero_iff_le.mpr «expr $ »(nat_degree_le_nat_degree, le_of_lt hfg)] [] },
  have [ident hgf] [] [":=", expr hfg],
  rw [expr div_by_monic_eq_zero_iff hg] ["at", ident hgf],
  push_neg ["at", ident hgf],
  have [] [] [":=", expr degree_add_div_by_monic hg hgf],
  have [ident hf] [":", expr «expr ≠ »(f, 0)] [],
  { intro [ident hf],
    apply [expr hfg],
    rw ["[", expr hf, ",", expr zero_div_by_monic, "]"] [] },
  rw ["[", expr degree_eq_nat_degree hf, ",", expr degree_eq_nat_degree hg.ne_zero, ",", expr degree_eq_nat_degree hfg, ",", "<-", expr with_bot.coe_add, ",", expr with_bot.coe_eq_coe, "]"] ["at", ident this],
  rw ["[", "<-", expr this, ",", expr add_tsub_cancel_left, "]"] []
end

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem div_mod_by_monic_unique
{f g}
(q r : polynomial R)
(hg : monic g)
(h : «expr ∧ »(«expr = »(«expr + »(r, «expr * »(g, q)), f), «expr < »(degree r, degree g))) : «expr ∧ »(«expr = »(«expr /ₘ »(f, g), q), «expr = »(«expr %ₘ »(f, g), r)) :=
begin
  nontriviality [expr R] [],
  have [ident h₁] [":", expr «expr = »(«expr - »(r, «expr %ₘ »(f, g)), «expr * »(«expr- »(g), «expr - »(q, «expr /ₘ »(f, g))))] [],
  from [expr eq_of_sub_eq_zero (by rw ["[", "<-", expr sub_eq_zero_of_eq (h.1.trans (mod_by_monic_add_div f hg).symm), "]"] []; simp [] [] [] ["[", expr mul_add, ",", expr mul_comm, ",", expr sub_eq_add_neg, ",", expr add_comm, ",", expr add_left_comm, ",", expr add_assoc, "]"] [] [])],
  have [ident h₂] [":", expr «expr = »(degree «expr - »(r, «expr %ₘ »(f, g)), degree «expr * »(g, «expr - »(q, «expr /ₘ »(f, g))))] [],
  by simp [] [] [] ["[", expr h₁, "]"] [] [],
  have [ident h₄] [":", expr «expr < »(degree «expr - »(r, «expr %ₘ »(f, g)), degree g)] [],
  from [expr calc
     «expr ≤ »(degree «expr - »(r, «expr %ₘ »(f, g)), max (degree r) (degree «expr %ₘ »(f, g))) : degree_sub_le _ _
     «expr < »(..., degree g) : max_lt_iff.2 ⟨h.2, degree_mod_by_monic_lt _ hg⟩],
  have [ident h₅] [":", expr «expr = »(«expr - »(q, «expr /ₘ »(f, g)), 0)] [],
  from [expr by_contradiction (λ
    hqf, «expr $ »(not_le_of_gt h₄, calc
       «expr ≤ »(degree g, «expr + »(degree g, degree «expr - »(q, «expr /ₘ »(f, g)))) : by erw ["[", expr degree_eq_nat_degree hg.ne_zero, ",", expr degree_eq_nat_degree hqf, ",", expr with_bot.coe_le_coe, "]"] []; exact [expr nat.le_add_right _ _]
       «expr = »(..., degree «expr - »(r, «expr %ₘ »(f, g))) : by rw ["[", expr h₂, ",", expr degree_mul', "]"] []; simpa [] [] [] ["[", expr monic.def.1 hg, "]"] [] []))],
  exact [expr ⟨«expr $ »(eq.symm, eq_of_sub_eq_zero h₅), «expr $ »(eq.symm, «expr $ »(eq_of_sub_eq_zero, by simpa [] [] [] ["[", expr h₅, "]"] [] ["using", expr h₁]))⟩]
end

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_mod_div_by_monic
[comm_ring S]
(f : «expr →+* »(R, S))
(hq : monic q) : «expr ∧ »(«expr = »(«expr /ₘ »(p, q).map f, «expr /ₘ »(p.map f, q.map f)), «expr = »(«expr %ₘ »(p, q).map f, «expr %ₘ »(p.map f, q.map f))) :=
begin
  nontriviality [expr S] [],
  haveI [] [":", expr nontrivial R] [":=", expr f.domain_nontrivial],
  have [] [":", expr «expr ∧ »(«expr = »(«expr /ₘ »(map f p, map f q), map f «expr /ₘ »(p, q)), «expr = »(«expr %ₘ »(map f p, map f q), map f «expr %ₘ »(p, q)))] [],
  { exact [expr div_mod_by_monic_unique («expr /ₘ »(p, q).map f) _ (monic_map f hq) ⟨«expr $ »(eq.symm, by rw ["[", "<-", expr map_mul, ",", "<-", expr map_add, ",", expr mod_by_monic_add_div _ hq, "]"] []), calc
        «expr ≤ »(_, degree «expr %ₘ »(p, q)) : degree_map_le _ _
        «expr < »(..., degree q) : degree_mod_by_monic_lt _ hq
        «expr = »(..., _) : «expr $ »(eq.symm, degree_map_eq_of_leading_coeff_ne_zero _ (by rw ["[", expr monic.def.1 hq, ",", expr f.map_one, "]"] []; exact [expr one_ne_zero]))⟩] },
  exact [expr ⟨this.1.symm, this.2.symm⟩]
end

theorem map_div_by_monic [CommRingₓ S] (f : R →+* S) (hq : monic q) : (p /ₘ q).map f = p.map f /ₘ q.map f :=
  (map_mod_div_by_monic f hq).1

theorem map_mod_by_monic [CommRingₓ S] (f : R →+* S) (hq : monic q) : (p %ₘ q).map f = p.map f %ₘ q.map f :=
  (map_mod_div_by_monic f hq).2

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_iff_mod_by_monic_eq_zero (hq : monic q) : «expr ↔ »(«expr = »(«expr %ₘ »(p, q), 0), «expr ∣ »(q, p)) :=
⟨λ
 h, by rw ["[", "<-", expr mod_by_monic_add_div p hq, ",", expr h, ",", expr zero_add, "]"] []; exact [expr dvd_mul_right _ _], λ
 h, begin
   nontriviality [expr R] [],
   obtain ["⟨", ident r, ",", ident hr, "⟩", ":=", expr exists_eq_mul_right_of_dvd h],
   by_contradiction [ident hpq0],
   have [ident hmod] [":", expr «expr = »(«expr %ₘ »(p, q), «expr * »(q, «expr - »(r, «expr /ₘ »(p, q))))] [],
   { rw ["[", expr mod_by_monic_eq_sub_mul_div _ hq, ",", expr mul_sub, ",", "<-", expr hr, "]"] [] },
   have [] [":", expr «expr < »(degree «expr * »(q, «expr - »(r, «expr /ₘ »(p, q))), degree q)] [":=", expr «expr ▸ »(hmod, degree_mod_by_monic_lt _ hq)],
   have [ident hrpq0] [":", expr «expr ≠ »(leading_coeff «expr - »(r, «expr /ₘ »(p, q)), 0)] [":=", expr λ
    h, «expr $ »(hpq0, leading_coeff_eq_zero.1 (by rw ["[", expr hmod, ",", expr leading_coeff_eq_zero.1 h, ",", expr mul_zero, ",", expr leading_coeff_zero, "]"] []))],
   have [ident hlc] [":", expr «expr ≠ »(«expr * »(leading_coeff q, leading_coeff «expr - »(r, «expr /ₘ »(p, q))), 0)] [":=", expr by rwa ["[", expr monic.def.1 hq, ",", expr one_mul, "]"] []],
   rw ["[", expr degree_mul' hlc, ",", expr degree_eq_nat_degree hq.ne_zero, ",", expr degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hrpq0), "]"] ["at", ident this],
   exact [expr not_lt_of_ge (nat.le_add_right _ _) (with_bot.some_lt_some.1 this)]
 end⟩

theorem map_dvd_map [CommRingₓ S] (f : R →+* S) (hf : Function.Injective f) {x y : Polynomial R} (hx : x.monic) :
  x.map f ∣ y.map f ↔ x ∣ y :=
  by 
    rw [←dvd_iff_mod_by_monic_eq_zero hx, ←dvd_iff_mod_by_monic_eq_zero (monic_map f hx), ←map_mod_by_monic f hx]
    exact
      ⟨fun H =>
          map_injective f hf$
            by 
              rw [H, map_zero],
        fun H =>
          by 
            rw [H, map_zero]⟩

@[simp]
theorem mod_by_monic_one (p : Polynomial R) : p %ₘ 1 = 0 :=
  (dvd_iff_mod_by_monic_eq_zero
        (by 
          convert monic_one)).2
    (one_dvd _)

@[simp]
theorem div_by_monic_one (p : Polynomial R) : p /ₘ 1 = p :=
  by 
    convRHS => rw [←mod_by_monic_add_div p monic_one] <;> simp 

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem mod_by_monic_X_sub_C_eq_C_eval
(p : polynomial R)
(a : R) : «expr = »(«expr %ₘ »(p, «expr - »(X, C a)), C (p.eval a)) :=
begin
  nontriviality [expr R] [],
  have [ident h] [":", expr «expr = »(«expr %ₘ »(p, «expr - »(X, C a)).eval a, p.eval a)] [],
  { rw ["[", expr mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), ",", expr eval_sub, ",", expr eval_mul, ",", expr eval_sub, ",", expr eval_X, ",", expr eval_C, ",", expr sub_self, ",", expr zero_mul, ",", expr sub_zero, "]"] [] },
  have [] [":", expr «expr < »(degree «expr %ₘ »(p, «expr - »(X, C a)), 1)] [":=", expr «expr ▸ »(degree_X_sub_C a, degree_mod_by_monic_lt p (monic_X_sub_C a))],
  have [] [":", expr «expr ≤ »(degree «expr %ₘ »(p, «expr - »(X, C a)), 0)] [],
  { cases [expr degree «expr %ₘ »(p, «expr - »(X, C a))] [],
    { exact [expr bot_le] },
    { exact [expr with_bot.some_le_some.2 (nat.le_of_lt_succ (with_bot.some_lt_some.1 this))] } },
  rw ["[", expr eq_C_of_degree_le_zero this, ",", expr eval_C, "]"] ["at", ident h],
  rw ["[", expr eq_C_of_degree_le_zero this, ",", expr h, "]"] []
end

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem mul_div_by_monic_eq_iff_is_root : «expr ↔ »(«expr = »(«expr * »(«expr - »(X, C a), «expr /ₘ »(p, «expr - »(X, C a))), p), is_root p a) :=
⟨λ
 h, by rw ["[", "<-", expr h, ",", expr is_root.def, ",", expr eval_mul, ",", expr eval_sub, ",", expr eval_X, ",", expr eval_C, ",", expr sub_self, ",", expr zero_mul, "]"] [], λ
 h : «expr = »(p.eval a, 0), by conv [] [] { to_rhs,
   rw ["<-", expr mod_by_monic_add_div p (monic_X_sub_C a)] }; rw ["[", expr mod_by_monic_X_sub_C_eq_C_eval, ",", expr h, ",", expr C_0, ",", expr zero_add, "]"] []⟩

theorem dvd_iff_is_root : X - C a ∣ p ↔ is_root p a :=
  ⟨fun h =>
      by 
        rwa [←dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _), mod_by_monic_X_sub_C_eq_C_eval, ←C_0, C_inj] at h,
    fun h =>
      ⟨p /ₘ (X - C a),
        by 
          rw [mul_div_by_monic_eq_iff_is_root.2 h]⟩⟩

theorem mod_by_monic_X (p : Polynomial R) : p %ₘ X = C (p.eval 0) :=
  by 
    rw [←mod_by_monic_X_sub_C_eq_C_eval, C_0, sub_zero]

theorem eval₂_mod_by_monic_eq_self_of_root [CommRingₓ S] {f : R →+* S} {p q : Polynomial R} (hq : q.monic) {x : S}
  (hx : q.eval₂ f x = 0) : (p %ₘ q).eval₂ f x = p.eval₂ f x :=
  by 
    rw [mod_by_monic_eq_sub_mul_div p hq, eval₂_sub, eval₂_mul, hx, zero_mul, sub_zero]

theorem sum_fin [AddCommMonoidₓ S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} (hn : p.degree < n) :
  (∑i : Finₓ n, f i (p.coeff i)) = p.sum f :=
  by 
    byCases' hp : p = 0
    ·
      rw [hp, sum_zero_index, Finset.sum_eq_zero]
      intro i _ 
      exact hf i 
    rw [degree_eq_nat_degree hp, WithBot.coe_lt_coe] at hn 
    calc (∑i : Finₓ n, f i (p.coeff i)) = ∑i in Finset.range n, f i (p.coeff i) :=
      Finₓ.sum_univ_eq_sum_range (fun i => f i (p.coeff i)) _ _ = ∑i in p.support, f i (p.coeff i) :=
      (Finset.sum_subset (supp_subset_range_nat_degree_succ.trans (finset.range_subset.mpr hn))
          fun i _ hi =>
            show f i (p.coeff i) = 0 by 
              rw [not_mem_support_iff.mp hi, hf]).symm
        _ = p.sum f :=
      p.sum_def _

theorem sum_mod_by_monic_coeff [Nontrivial R] (hq : q.monic) {n : ℕ} (hn : q.degree ≤ n) :
  (∑i : Finₓ n, monomial i ((p %ₘ q).coeff i)) = p %ₘ q :=
  (sum_fin (fun i c => monomial i c)
        (by 
          simp )
        ((degree_mod_by_monic_lt _ hq).trans_le hn)).trans
    (sum_monomial_eq _)

section multiplicity

/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`". `
See `polynomial.mod_by_monic` for the algorithm that computes `%ₘ`.
 -/
def decidable_dvd_monic (p : Polynomial R) (hq : monic q) : Decidable (q ∣ p) :=
  decidableOfIff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

open_locale Classical

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem multiplicity_X_sub_C_finite (a : R) (h0 : «expr ≠ »(p, 0)) : multiplicity.finite «expr - »(X, C a) p :=
multiplicity_finite_of_degree_pos_of_monic (have «expr ≠ »((0 : R), 1), from λ
 h, by haveI [] [] [":=", expr subsingleton_of_zero_eq_one h]; exact [expr h0 (subsingleton.elim _ _)],
 by haveI [] [":", expr nontrivial R] [":=", expr ⟨⟨0, 1, this⟩⟩]; rw [expr degree_X_sub_C] []; exact [expr exprdec_trivial()]) (monic_X_sub_C _) h0

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The largest power of `X - C a` which divides `p`.
This is computable via the divisibility algorithm `decidable_dvd_monic`. -/
def root_multiplicity (a : R) (p : polynomial R) : exprℕ() :=
if h0 : «expr = »(p, 0) then 0 else let I : decidable_pred (λ
     n : exprℕ(), «expr¬ »(«expr ∣ »(«expr ^ »(«expr - »(X, C a), «expr + »(n, 1)), p))) := λ
    n, @not.decidable _ (decidable_dvd_monic p (monic_pow (monic_X_sub_C a) «expr + »(n, 1))) in
by exactI [expr nat.find (multiplicity_X_sub_C_finite a h0)]

theorem root_multiplicity_eq_multiplicity (p : Polynomial R) (a : R) :
  root_multiplicity a p = if h0 : p = 0 then 0 else (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
  by 
    simp [multiplicity, root_multiplicity, Part.Dom] <;> congr <;> funext  <;> congr

@[simp]
theorem root_multiplicity_zero {x : R} : root_multiplicity x 0 = 0 :=
  dif_pos rfl

theorem root_multiplicity_eq_zero {p : Polynomial R} {x : R} (h : ¬is_root p x) : root_multiplicity x p = 0 :=
  by 
    rw [root_multiplicity_eq_multiplicity]
    splitIfs
    ·
      rfl 
    rw [←Enat.coe_inj, Enat.coe_get, multiplicity.multiplicity_eq_zero_of_not_dvd, Nat.cast_zero]
    intro hdvd 
    exact h (dvd_iff_is_root.mp hdvd)

theorem root_multiplicity_pos {p : Polynomial R} (hp : p ≠ 0) {x : R} : 0 < root_multiplicity x p ↔ is_root p x :=
  by 
    rw [←dvd_iff_is_root, root_multiplicity_eq_multiplicity, dif_neg hp, ←Enat.coe_lt_coe, Enat.coe_get]
    exact multiplicity.dvd_iff_multiplicity_pos

theorem pow_root_multiplicity_dvd (p : Polynomial R) (a : R) : (X - C a) ^ root_multiplicity a p ∣ p :=
  if h : p = 0 then
    by 
      simp [h]
  else
    by 
      rw [root_multiplicity_eq_multiplicity, dif_neg h] <;> exact multiplicity.pow_multiplicity_dvd _

theorem div_by_monic_mul_pow_root_multiplicity_eq (p : Polynomial R) (a : R) :
  ((p /ₘ (X - C a) ^ root_multiplicity a p)*(X - C a) ^ root_multiplicity a p) = p :=
  have  : monic ((X - C a) ^ root_multiplicity a p) := monic_pow (monic_X_sub_C _) _ 
  by 
    convRHS =>
        rw [←mod_by_monic_add_div p this, (dvd_iff_mod_by_monic_eq_zero this).2 (pow_root_multiplicity_dvd _ _)] <;>
      simp [mul_commₓ]

-- error in Data.Polynomial.Div: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eval_div_by_monic_pow_root_multiplicity_ne_zero
{p : polynomial R}
(a : R)
(hp : «expr ≠ »(p, 0)) : «expr ≠ »(eval a «expr /ₘ »(p, «expr ^ »(«expr - »(X, C a), root_multiplicity a p)), 0) :=
begin
  haveI [] [":", expr nontrivial R] [":=", expr nontrivial.of_polynomial_ne hp],
  rw ["[", expr ne.def, ",", "<-", expr is_root.def, ",", "<-", expr dvd_iff_is_root, "]"] [],
  rintros ["⟨", ident q, ",", ident hq, "⟩"],
  have [] [] [":=", expr div_by_monic_mul_pow_root_multiplicity_eq p a],
  rw ["[", expr mul_comm, ",", expr hq, ",", "<-", expr mul_assoc, ",", "<-", expr pow_succ', ",", expr root_multiplicity_eq_multiplicity, ",", expr dif_neg hp, "]"] ["at", ident this],
  exact [expr multiplicity.is_greatest' (multiplicity_finite_of_degree_pos_of_monic (show «expr < »((0 : with_bot exprℕ()), degree «expr - »(X, C a)), by rw [expr degree_X_sub_C] []; exact [expr exprdec_trivial()]) (monic_X_sub_C _) hp) (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)]
end

end multiplicity

end CommRingₓ

end Polynomial

