import Mathbin.FieldTheory.Finite.Basic 
import Mathbin.Data.Zmod.Basic 
import Mathbin.Data.Nat.Parity

/-!
# Quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`exists_sq_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`exists_sq_eq_neg_one_iff_mod_four_ne_three` and
`exists_sq_eq_two_iff`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/


open Function Finset Nat FiniteField Zmod

open_locale BigOperators Nat

namespace Zmod

variable(p q : ℕ)[Fact p.prime][Fact q.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion_units (x : Units (Zmod p)) : (∃ y : Units (Zmod p), (y^2) = x) ↔ (x^p / 2) = 1 :=
  by 
    cases' Nat.Prime.eq_two_or_odd (Fact.out p.prime) with hp2 hp_odd
    ·
      substI p 
      refine' iff_of_true ⟨1, _⟩ _ <;> apply Subsingleton.elimₓ 
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (Units (Zmod p))
    obtain ⟨n, hn⟩ : x ∈ Submonoid.powers g
    ·
      rw [mem_powers_iff_mem_zpowers]
      apply hg 
    split 
    ·
      rintro ⟨y, rfl⟩
      rw [←pow_mulₓ, two_mul_odd_div_two hp_odd, units_pow_card_sub_one_eq_one]
    ·
      subst x 
      intro h 
      have key : (2*p / 2) ∣ n*p / 2
      ·
        rw [←pow_mulₓ] at h 
        rw [two_mul_odd_div_two hp_odd, ←card_units, ←order_of_eq_card_of_forall_mem_zpowers hg]
        apply order_of_dvd_of_pow_eq_one h 
      have  : 0 < p / 2 :=
        Nat.div_pos (Fact.out (1 < p))
          (by 
            decide)
      obtain ⟨m, rfl⟩ := dvd_of_mul_dvd_mul_right this key 
      refine' ⟨g^m, _⟩
      rw [mul_commₓ, pow_mulₓ]

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion {a : Zmod p} (ha : a ≠ 0) : (∃ y : Zmod p, (y^2) = a) ↔ (a^p / 2) = 1 :=
  by 
    apply
      (iff_congr _
            (by 
              simp [Units.ext_iff])).mp
        (euler_criterion_units p (Units.mk0 a ha))
    simp only [Units.ext_iff, sq, Units.coe_mk0, Units.coe_mul]
    split 
    ·
      rintro ⟨y, hy⟩
      exact ⟨y, hy⟩
    ·
      rintro ⟨y, rfl⟩
      have hy : y ≠ 0
      ·
        rintro rfl 
        simpa [zero_pow] using ha 
      refine' ⟨Units.mk0 y hy, _⟩
      simp 

theorem exists_sq_eq_neg_one_iff_mod_four_ne_three : (∃ y : Zmod p, (y^2) = -1) ↔ p % 4 ≠ 3 :=
  by 
    cases' Nat.Prime.eq_two_or_odd (Fact.out p.prime) with hp2 hp_odd
    ·
      substI p 
      exact
        by 
          decide 
    haveI  := Fact.mk hp_odd 
    have neg_one_ne_zero : (-1 : Zmod p) ≠ 0 
    exact mt neg_eq_zero.1 one_ne_zero 
    rw [euler_criterion p neg_one_ne_zero, neg_one_pow_eq_pow_mod_two]
    cases' mod_two_eq_zero_or_one (p / 2) with p_half_even p_half_odd
    ·
      rw [p_half_even, pow_zeroₓ, eq_self_iff_true, true_iffₓ]
      contrapose! p_half_even with hp 
      rw [←Nat.mod_mul_right_div_self, show (2*2) = 4 from rfl, hp]
      exact
        by 
          decide
    ·
      rw [p_half_odd, pow_oneₓ, iff_false_intro (ne_neg_self p one_ne_zero).symm, false_iffₓ, not_not]
      rw [←Nat.mod_mul_right_div_self, show (2*2) = 4 from rfl] at p_half_odd 
      rw [←Nat.mod_mul_left_mod _ 2, show (2*2) = 4 from rfl] at hp_odd 
      have hp : p % 4 < 4 
      exact
        Nat.mod_ltₓ _
          (by 
            decide)
      revert hp hp_odd p_half_odd 
      generalize p % 4 = k 
      decide!

theorem pow_div_two_eq_neg_one_or_one {a : Zmod p} (ha : a ≠ 0) : (a^p / 2) = 1 ∨ (a^p / 2) = -1 :=
  by 
    cases' Nat.Prime.eq_two_or_odd (Fact.out p.prime) with hp2 hp_odd
    ·
      substI p 
      revert a ha 
      exact
        by 
          decide 
    rw [←mul_self_eq_one_iff, ←pow_addₓ, ←two_mul, two_mul_odd_div_two hp_odd]
    exact pow_card_sub_one_eq_one ha

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp]
theorem wilsons_lemma : ((p - 1)! : Zmod p) = -1 :=
  by 
    refine'
      calc ((p - 1)! : Zmod p) = ∏x in Ico 1 (succ (p - 1)), x :=
        by 
          rw [←Finset.prod_Ico_id_eq_factorial, prod_nat_cast]
        _ = ∏x : Units (Zmod p), x := _ 
        _ = -1 :=
        by 
          simpRw [←Units.coe_hom_apply, ←(Units.coeHom (Zmod p)).map_prod, prod_univ_units_id_eq_neg_one,
            Units.coe_hom_apply, Units.coe_neg, Units.coe_one]
        
    have hp : 0 < p := (Fact.out p.prime).Pos 
    symm 
    refine' prod_bij (fun a _ => (a : Zmod p).val) _ _ _ _
    ·
      intro a ha 
      rw [mem_Ico, ←Nat.succ_subₓ hp, Nat.succ_sub_one]
      split 
      ·
        apply Nat.pos_of_ne_zeroₓ 
        rw [←@val_zero p]
        intro h 
        apply Units.ne_zero a (val_injective p h)
      ·
        exact val_lt _
    ·
      intro a ha 
      simp only [cast_id, nat_cast_val]
    ·
      intro _ _ _ _ h 
      rw [Units.ext_iff]
      exact val_injective p h
    ·
      intro b hb 
      rw [mem_Ico, Nat.succ_le_iff, ←succ_sub hp, succ_sub_one, pos_iff_ne_zero] at hb 
      refine' ⟨Units.mk0 b _, Finset.mem_univ _, _⟩
      ·
        intro h 
        apply hb.1
        applyFun val  at h 
        simpa only [val_cast_of_lt hb.right, val_zero] using h
      ·
        simp only [val_cast_of_lt hb.right, Units.coe_mk0]

@[simp]
theorem prod_Ico_one_prime : (∏x in Ico 1 p, (x : Zmod p)) = -1 :=
  by 
    conv  in Ico 1 p => rw [←succ_sub_one p, succ_sub (Fact.out p.prime).Pos]
    rw [←prod_nat_cast, Finset.prod_Ico_id_eq_factorial, wilsons_lemma]

end Zmod

-- error in NumberTheory.QuadraticReciprocity: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The image of the map sending a non zero natural number `x ≤ p / 2` to the absolute value
  of the element of interger in the interval `(-p/2, p/2]` congruent to `a * x` mod p is the set
  of non zero natural numbers `x` such that `x ≤ p / 2` -/
theorem Ico_map_val_min_abs_nat_abs_eq_Ico_map_id
(p : exprℕ())
[hp : fact p.prime]
(a : zmod p)
(hap : «expr ≠ »(a, 0)) : «expr = »((Ico 1 «expr / »(p, 2).succ).1.map (λ
  x, «expr * »(a, x).val_min_abs.nat_abs), (Ico 1 «expr / »(p, 2).succ).1.map (λ a, a)) :=
begin
  have [ident he] [":", expr ∀
   {x}, «expr ∈ »(x, Ico 1 «expr / »(p, 2).succ) → «expr ∧ »(«expr ≠ »(x, 0), «expr ≤ »(x, «expr / »(p, 2)))] [],
  by simp [] [] [] ["[", expr nat.lt_succ_iff, ",", expr nat.succ_le_iff, ",", expr pos_iff_ne_zero, "]"] [] [] { contextual := tt },
  have [ident hep] [":", expr ∀ {x}, «expr ∈ »(x, Ico 1 «expr / »(p, 2).succ) → «expr < »(x, p)] [],
  from [expr λ x hx, lt_of_le_of_lt (he hx).2 (nat.div_lt_self hp.1.pos exprdec_trivial())],
  have [ident hpe] [":", expr ∀ {x}, «expr ∈ »(x, Ico 1 «expr / »(p, 2).succ) → «expr¬ »(«expr ∣ »(p, x))] [],
  from [expr λ x hx hpx, not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero (he hx).1) hpx) (hep hx)],
  have [ident hmem] [":", expr ∀
   (x : exprℕ())
   (hx : «expr ∈ »(x, Ico 1 «expr / »(p, 2).succ)), «expr ∈ »((«expr * »(a, x) : zmod p).val_min_abs.nat_abs, Ico 1 «expr / »(p, 2).succ)] [],
  { assume [binders (x hx)],
    simp [] [] [] ["[", expr hap, ",", expr char_p.cast_eq_zero_iff (zmod p) p, ",", expr hpe hx, ",", expr lt_succ_iff, ",", expr succ_le_iff, ",", expr pos_iff_ne_zero, ",", expr nat_abs_val_min_abs_le _, "]"] [] [] },
  have [ident hsurj] [":", expr ∀
   (b : exprℕ())
   (hb : «expr ∈ »(b, Ico 1 «expr / »(p, 2).succ)), «expr∃ , »((x «expr ∈ » Ico 1 «expr / »(p, 2).succ), «expr = »(b, («expr * »(a, x) : zmod p).val_min_abs.nat_abs))] [],
  { assume [binders (b hb)],
    refine [expr ⟨(«expr / »(b, a) : zmod p).val_min_abs.nat_abs, mem_Ico.mpr ⟨_, _⟩, _⟩],
    { apply [expr nat.pos_of_ne_zero],
      simp [] [] ["only"] ["[", expr div_eq_mul_inv, ",", expr hap, ",", expr char_p.cast_eq_zero_iff (zmod p) p, ",", expr hpe hb, ",", expr not_false_iff, ",", expr val_min_abs_eq_zero, ",", expr inv_eq_zero, ",", expr int.nat_abs_eq_zero, ",", expr ne.def, ",", expr mul_eq_zero, ",", expr or_self, "]"] [] [] },
    { apply [expr lt_succ_of_le],
      apply [expr nat_abs_val_min_abs_le] },
    { rw [expr nat_cast_nat_abs_val_min_abs] [],
      split_ifs [] [],
      { erw ["[", expr mul_div_cancel' _ hap, ",", expr val_min_abs_def_pos, ",", expr val_cast_of_lt (hep hb), ",", expr if_pos (le_of_lt_succ (mem_Ico.1 hb).2), ",", expr int.nat_abs_of_nat, "]"] [] },
      { erw ["[", expr mul_neg_eq_neg_mul_symm, ",", expr mul_div_cancel' _ hap, ",", expr nat_abs_val_min_abs_neg, ",", expr val_min_abs_def_pos, ",", expr val_cast_of_lt (hep hb), ",", expr if_pos (le_of_lt_succ (mem_Ico.1 hb).2), ",", expr int.nat_abs_of_nat, "]"] [] } } },
  exact [expr multiset.map_eq_map_of_bij_of_nodup _ _ (finset.nodup _) (finset.nodup _) (λ
    x
    _, («expr * »(a, x) : zmod p).val_min_abs.nat_abs) hmem (λ
    _ _, rfl) (inj_on_of_surj_on_of_card_le _ hmem hsurj (le_refl _)) hsurj]
end

-- error in NumberTheory.QuadraticReciprocity: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem gauss_lemma_aux₁
(p : exprℕ())
[fact p.prime]
[fact «expr = »(«expr % »(p, 2), 1)]
{a : exprℕ()}
(hap : «expr ≠ »((a : zmod p), 0)) : «expr = »((«expr * »(«expr ^ »(a, «expr / »(p, 2)), «expr !»(«expr / »(p, 2))) : zmod p), «expr * »(«expr ^ »(«expr- »(1), ((Ico 1 «expr / »(p, 2).succ).filter (λ
     x : exprℕ(), «expr¬ »(«expr ≤ »((«expr * »(a, x) : zmod p).val, «expr / »(p, 2))))).card), «expr !»(«expr / »(p, 2)))) :=
calc
  «expr = »((«expr * »(«expr ^ »(a, «expr / »(p, 2)), «expr !»(«expr / »(p, 2))) : zmod p), «expr∏ in , »((x), Ico 1 «expr / »(p, 2).succ, «expr * »(a, x))) : by rw ["[", expr prod_mul_distrib, ",", "<-", expr prod_nat_cast, ",", "<-", expr prod_nat_cast, ",", expr prod_Ico_id_eq_factorial, ",", expr prod_const, ",", expr card_Ico, ",", expr succ_sub_one, "]"] []; simp [] [] [] [] [] []
  «expr = »(..., «expr∏ in , »((x), Ico 1 «expr / »(p, 2).succ, («expr * »(a, x) : zmod p).val)) : by simp [] [] [] [] [] []
  «expr = »(..., «expr∏ in , »((x), Ico 1 «expr / »(p, 2).succ, «expr * »(if «expr ≤ »((«expr * »(a, x) : zmod p).val, «expr / »(p, 2)) then 1 else «expr- »(1), («expr * »(a, x) : zmod p).val_min_abs.nat_abs))) : «expr $ »(prod_congr rfl, λ
   _ _, begin
     simp [] [] ["only"] ["[", expr nat_cast_nat_abs_val_min_abs, "]"] [] [],
     split_ifs [] []; simp [] [] [] [] [] []
   end)
  «expr = »(..., «expr * »(«expr ^ »(«expr- »(1), ((Ico 1 «expr / »(p, 2).succ).filter (λ
       x : exprℕ(), «expr¬ »(«expr ≤ »((«expr * »(a, x) : zmod p).val, «expr / »(p, 2))))).card), «expr∏ in , »((x), Ico 1 «expr / »(p, 2).succ, («expr * »(a, x) : zmod p).val_min_abs.nat_abs))) : have «expr = »(«expr∏ in , »((x), Ico 1 «expr / »(p, 2).succ, if «expr ≤ »((«expr * »(a, x) : zmod p).val, «expr / »(p, 2)) then (1 : zmod p) else «expr- »(1)), «expr∏ in , »((x), (Ico 1 «expr / »(p, 2).succ).filter (λ
     x : exprℕ(), «expr¬ »(«expr ≤ »((«expr * »(a, x) : zmod p).val, «expr / »(p, 2)))), «expr- »(1))), from prod_bij_ne_one (λ
   x
   _
   _, x) (λ
   x, by split_ifs [] []; simp [] [] [] ["*"] [] ["at", "*"] { contextual := tt }) (λ
   _
   _
   _
   _
   _
   _, id) (λ
   b
   h
   _, ⟨b, by simp [] [] [] ["[", "-", ident not_le, ",", "*", "]"] [] ["at", "*"]⟩) (by intros []; split_ifs ["at", "*"] []; simp [] [] [] ["*"] [] ["at", "*"]),
  by rw ["[", expr prod_mul_distrib, ",", expr this, "]"] []; simp [] [] [] [] [] []
  «expr = »(..., «expr * »(«expr ^ »(«expr- »(1), ((Ico 1 «expr / »(p, 2).succ).filter (λ
       x : exprℕ(), «expr¬ »(«expr ≤ »((«expr * »(a, x) : zmod p).val, «expr / »(p, 2))))).card), «expr !»(«expr / »(p, 2)))) : by rw ["[", "<-", expr prod_nat_cast, ",", expr finset.prod_eq_multiset_prod, ",", expr Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap, ",", "<-", expr finset.prod_eq_multiset_prod, ",", expr prod_Ico_id_eq_factorial, "]"] []

private theorem gauss_lemma_aux₂ (p : ℕ) [hp : Fact p.prime] [Fact (p % 2 = 1)] {a : ℕ} (hap : (a : Zmod p) ≠ 0) :
  (a^p / 2 : Zmod p) = (-1^((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a*x : Zmod p).val).card) :=
  (mul_left_inj'
        (show ((p / 2)! : Zmod p) ≠ 0 by 
          rw [Ne.def, CharP.cast_eq_zero_iff (Zmod p) p, hp.1.dvd_factorial, not_leₓ] <;>
            exact
              Nat.div_lt_selfₓ hp.1.Pos
                (by 
                  decide))).1$
    by 
      simpa using gauss_lemma_aux₁ p hap

private theorem eisenstein_lemma_aux₁ (p : ℕ) [Fact p.prime] [hp2 : Fact (p % 2 = 1)] {a : ℕ} (hap : (a : Zmod p) ≠ 0) :
  ((∑x in Ico 1 (p / 2).succ, a*x : ℕ) : Zmod 2) =
    (((Ico 1 (p / 2).succ).filter
            fun x : ℕ =>
              p / 2 < (a*x : Zmod p).val).card+∑x in Ico 1 (p / 2).succ, x)+(∑x in Ico 1 (p / 2).succ, (a*x) / p : ℕ) :=
  have hp2 : (p : Zmod 2) = (1 : ℕ) := (eq_iff_modeq_nat _).2 hp2.1
  calc
    ((∑x in Ico 1 (p / 2).succ, a*x : ℕ) : Zmod 2) =
      ((∑x in Ico 1 (p / 2).succ, ((a*x) % p)+p*(a*x) / p : ℕ) : Zmod 2) :=
    by 
      simp only [mod_add_div]
    _ = (∑x in Ico 1 (p / 2).succ, ((a*x : ℕ) : Zmod p).val : ℕ)+(∑x in Ico 1 (p / 2).succ, (a*x) / p : ℕ) :=
    by 
      simp only [val_nat_cast] <;> simp [sum_add_distrib, mul_sum.symm, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
    _ = _ :=
    congr_arg2 (·+·)
      (calc
        ((∑x in Ico 1 (p / 2).succ, ((a*x : ℕ) : Zmod p).val : ℕ) : Zmod 2) =
          ∑x in Ico 1 (p / 2).succ,
            (((a*x : Zmod p).valMinAbs+if (a*x : Zmod p).val ≤ p / 2 then 0 else p : ℤ) : Zmod 2) :=
        by 
          simp only [(val_eq_ite_val_min_abs _).symm] <;> simp [Nat.cast_sum]
        _ =
          ((Ico 1 (p / 2).succ).filter
                fun x : ℕ =>
                  p / 2 < (a*x : Zmod p).val).card+(∑x in Ico 1 (p / 2).succ, (a*x : Zmod p).valMinAbs.natAbs : ℕ) :=
        by 
          simp [ite_cast, add_commₓ, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
        _ = _ :=
        by 
          rw [Finset.sum_eq_multiset_sum, Ico_map_val_min_abs_nat_abs_eq_Ico_map_id p a hap,
              ←Finset.sum_eq_multiset_sum] <;>
            simp [Nat.cast_sum]
        )
      rfl
    

private theorem eisenstein_lemma_aux₂ (p : ℕ) [Fact p.prime] [Fact (p % 2 = 1)] {a : ℕ} (ha2 : a % 2 = 1)
  (hap : (a : Zmod p) ≠ 0) :
  ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a*x : Zmod p).val).card ≡ ∑x in Ico 1 (p / 2).succ, (x*a) / p [MOD
    2] :=
  have ha2 : (a : Zmod 2) = (1 : ℕ) := (eq_iff_modeq_nat _).2 ha2
  (eq_iff_modeq_nat 2).1$
    sub_eq_zero.1$
      by 
        simpa [add_left_commₓ, sub_eq_add_neg, finset.mul_sum.symm, mul_commₓ, ha2, Nat.cast_sum,
          add_neg_eq_iff_eq_add.symm, neg_eq_self_mod_two, add_assocₓ] using Eq.symm (eisenstein_lemma_aux₁ p hap)

theorem div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) :
  a / b = ((Ico 1 c.succ).filter fun x => (x*b) ≤ a).card :=
  calc a / b = (Ico 1 (a / b).succ).card :=
    by 
      simp 
    _ = ((Ico 1 c.succ).filter fun x => (x*b) ≤ a).card :=
    congr_argₓ _$
      Finset.ext$
        fun x =>
          have  : (x*b) ≤ a → x ≤ c :=
            fun h =>
              le_transₓ
                (by 
                  rwa [le_div_iff_mul_le _ _ hb0])
                hc 
          by 
            simp [lt_succ_iff, le_div_iff_mul_le _ _ hb0] <;> tauto
    

-- error in NumberTheory.QuadraticReciprocity: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`  -/
private
theorem sum_Ico_eq_card_lt
{p
 q : exprℕ()} : «expr = »(«expr∑ in , »((a), Ico 1 «expr / »(p, 2).succ, «expr / »(«expr * »(a, q), p)), (((Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ)).filter (λ
   x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.2, p), «expr * »(x.1, q)))).card) :=
if hp0 : «expr = »(p, 0) then by simp [] [] [] ["[", expr hp0, ",", expr finset.ext_iff, "]"] [] [] else calc
  «expr = »(«expr∑ in , »((a), Ico 1 «expr / »(p, 2).succ, «expr / »(«expr * »(a, q), p)), «expr∑ in , »((a), Ico 1 «expr / »(p, 2).succ, ((Ico 1 «expr / »(q, 2).succ).filter (λ
      x, «expr ≤ »(«expr * »(x, p), «expr * »(a, q)))).card)) : «expr $ »(finset.sum_congr rfl, λ
   x
   hx, div_eq_filter_card (nat.pos_of_ne_zero hp0) (calc
      «expr ≤ »(«expr / »(«expr * »(x, q), p), «expr / »(«expr * »(«expr / »(p, 2), q), p)) : nat.div_le_div_right (mul_le_mul_of_nonneg_right «expr $ »(le_of_lt_succ, by finish [] []) (nat.zero_le _))
      «expr ≤ »(..., _) : nat.div_mul_div_le_div _ _ _))
  «expr = »(..., _) : by rw ["[", "<-", expr card_sigma, "]"] []; exact [expr card_congr (λ
    a
    _, ⟨a.1, a.2⟩) (by simp [] [] ["only"] ["[", expr mem_filter, ",", expr mem_sigma, ",", expr and_self, ",", expr forall_true_iff, ",", expr mem_product, "]"] [] [] { contextual := tt }) (λ
    ⟨_, _⟩
    ⟨_, _⟩, by simp [] [] ["only"] ["[", expr prod.mk.inj_iff, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr heq_iff_eq, ",", expr forall_true_iff, "]"] [] [] { contextual := tt }) (λ
    ⟨b₁, b₂⟩
    (h), ⟨⟨b₁, b₂⟩, by revert [ident h]; simp [] [] ["only"] ["[", expr mem_filter, ",", expr eq_self_iff_true, ",", expr exists_prop_of_true, ",", expr mem_sigma, ",", expr and_self, ",", expr forall_true_iff, ",", expr mem_product, "]"] [] [] { contextual := tt }⟩)]

-- error in NumberTheory.QuadraticReciprocity: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Each of the sums in this lemma is the cardinality of the set integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
private
theorem sum_mul_div_add_sum_mul_div_eq_mul
(p q : exprℕ())
[hp : fact p.prime]
(hq0 : «expr ≠ »((q : zmod p), 0)) : «expr = »(«expr + »(«expr∑ in , »((a), Ico 1 «expr / »(p, 2).succ, «expr / »(«expr * »(a, q), p)), «expr∑ in , »((a), Ico 1 «expr / »(q, 2).succ, «expr / »(«expr * »(a, p), q))), «expr * »(«expr / »(p, 2), «expr / »(q, 2))) :=
begin
  have [ident hswap] [":", expr «expr = »((((Ico 1 «expr / »(q, 2).succ).product (Ico 1 «expr / »(p, 2).succ)).filter (λ
      x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.2, q), «expr * »(x.1, p)))).card, (((Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ)).filter (λ
      x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.1, q), «expr * »(x.2, p)))).card)] [":=", expr card_congr (λ
    x
    _, prod.swap x) (λ
    ⟨_, _⟩, by simp [] [] ["only"] ["[", expr mem_filter, ",", expr and_self, ",", expr prod.swap_prod_mk, ",", expr forall_true_iff, ",", expr mem_product, "]"] [] [] { contextual := tt }) (λ
    ⟨_, _⟩
    ⟨_, _⟩, by simp [] [] ["only"] ["[", expr prod.mk.inj_iff, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr prod.swap_prod_mk, ",", expr forall_true_iff, "]"] [] [] { contextual := tt }) (λ
    ⟨x₁, x₂⟩
    (h), ⟨⟨x₂, x₁⟩, by revert [ident h]; simp [] [] ["only"] ["[", expr mem_filter, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr exists_prop_of_true, ",", expr prod.swap_prod_mk, ",", expr forall_true_iff, ",", expr mem_product, "]"] [] [] { contextual := tt }⟩)],
  have [ident hdisj] [":", expr disjoint (((Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ)).filter (λ
     x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.2, p), «expr * »(x.1, q)))) (((Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ)).filter (λ
     x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.1, q), «expr * »(x.2, p))))] [],
  { apply [expr disjoint_filter.2 (λ x hx hpq hqp, _)],
    have [ident hxp] [":", expr «expr < »(x.1, p)] [],
    from [expr lt_of_le_of_lt (show «expr ≤ »(x.1, «expr / »(p, 2)), by simp [] [] ["only"] ["[", "*", ",", expr lt_succ_iff, ",", expr mem_Ico, ",", expr mem_product, "]"] [] ["at", "*"]; tauto []) (nat.div_lt_self hp.1.pos exprdec_trivial())],
    have [] [":", expr «expr = »((x.1 : zmod p), 0)] [],
    { simpa [] [] [] ["[", expr hq0, "]"] [] ["using", expr congr_arg (coe : exprℕ() → zmod p) (le_antisymm hpq hqp)] },
    apply_fun [expr zmod.val] ["at", ident this] [],
    rw ["[", expr val_cast_of_lt hxp, ",", expr val_zero, "]"] ["at", ident this],
    simpa [] [] ["only"] ["[", expr this, ",", expr nonpos_iff_eq_zero, ",", expr mem_Ico, ",", expr one_ne_zero, ",", expr false_and, ",", expr mem_product, "]"] [] ["using", expr hx] },
  have [ident hunion] [":", expr «expr = »(«expr ∪ »(((Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ)).filter (λ
      x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.2, p), «expr * »(x.1, q))), ((Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ)).filter (λ
      x : «expr × »(exprℕ(), exprℕ()), «expr ≤ »(«expr * »(x.1, q), «expr * »(x.2, p)))), (Ico 1 «expr / »(p, 2).succ).product (Ico 1 «expr / »(q, 2).succ))] [],
  from [expr finset.ext (λ
    x, by have [] [] [":=", expr le_total «expr * »(x.2, p) «expr * »(x.1, q)]; simp [] [] ["only"] ["[", expr mem_union, ",", expr mem_filter, ",", expr mem_Ico, ",", expr mem_product, "]"] [] []; tauto [])],
  rw ["[", expr sum_Ico_eq_card_lt, ",", expr sum_Ico_eq_card_lt, ",", expr hswap, ",", "<-", expr card_disjoint_union hdisj, ",", expr hunion, ",", expr card_product, "]"] [],
  simp [] [] ["only"] ["[", expr card_Ico, ",", expr tsub_zero, ",", expr succ_sub_succ_eq_sub, "]"] [] []
end

variable(p q : ℕ)[Fact p.prime][Fact q.prime]

namespace Zmod

/-- The Legendre symbol of `a` and `p` is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a ^ (p / 2)` is `1` modulo `p`
   (by `euler_criterion` this is equivalent to “`a` is a square modulo `p`”);
* `-1` otherwise.

-/
def legendre_sym (a p : ℕ) : ℤ :=
  if (a : Zmod p) = 0 then 0 else if ((a : Zmod p)^p / 2) = 1 then 1 else -1

theorem legendre_sym_eq_pow (a p : ℕ) [hp : Fact p.prime] : (legendre_sym a p : Zmod p) = (a^p / 2) :=
  by 
    rw [legendre_sym]
    byCases' ha : (a : Zmod p) = 0
    ·
      simp only [if_pos, ha, zero_pow (Nat.div_pos hp.1.two_le (succ_pos 1)), Int.cast_zero]
    cases' hp.1.eq_two_or_odd with hp2 hp_odd
    ·
      substI p 
      generalize (a : Zmod 2) = b 
      revert b 
      decide
    ·
      haveI  := Fact.mk hp_odd 
      rw [if_neg ha]
      have  : (-1 : Zmod p) ≠ 1 
      exact (ne_neg_self p one_ne_zero).symm 
      cases' pow_div_two_eq_neg_one_or_one p ha with h h
      ·
        rw [if_pos h, h, Int.cast_one]
      ·
        rw [h, if_neg this, Int.cast_neg, Int.cast_one]

theorem legendre_sym_eq_one_or_neg_one (a p : ℕ) (ha : (a : Zmod p) ≠ 0) :
  legendre_sym a p = -1 ∨ legendre_sym a p = 1 :=
  by 
    unfold legendre_sym <;> splitIfs <;> simp_all only [eq_self_iff_true, or_trueₓ, true_orₓ]

theorem legendre_sym_eq_zero_iff (a p : ℕ) : legendre_sym a p = 0 ↔ (a : Zmod p) = 0 :=
  by 
    split 
    ·
      classical 
      contrapose 
      intro ha 
      cases' legendre_sym_eq_one_or_neg_one a p ha with h h 
      all_goals 
        rw [h]
        normNum
    ·
      intro ha 
      rw [legendre_sym, if_pos ha]

/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
theorem gauss_lemma {a : ℕ} [Fact (p % 2 = 1)] (ha0 : (a : Zmod p) ≠ 0) :
  legendre_sym a p = (-1^((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a*x : Zmod p).val).card) :=
  have  :
    (legendre_sym a p : Zmod p) =
      ((-1^((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a*x : Zmod p).val).card : ℤ) : Zmod p) :=
    by 
      rw [legendre_sym_eq_pow, gauss_lemma_aux₂ p ha0] <;> simp 
  by 
    cases legendre_sym_eq_one_or_neg_one a p ha0 <;>
      cases neg_one_pow_eq_or ℤ ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a*x : Zmod p).val).card <;>
        simp_all [ne_neg_self p one_ne_zero, (ne_neg_self p one_ne_zero).symm]

theorem legendre_sym_eq_one_iff {a : ℕ} (ha0 : (a : Zmod p) ≠ 0) : legendre_sym a p = 1 ↔ ∃ b : Zmod p, (b^2) = a :=
  by 
    rw [euler_criterion p ha0, legendre_sym, if_neg ha0]
    splitIfs
    ·
      simp only [h, eq_self_iff_true]
    finish

theorem eisenstein_lemma [Fact (p % 2 = 1)] {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : Zmod p) ≠ 0) :
  legendre_sym a p = (-1^∑x in Ico 1 (p / 2).succ, (x*a) / p) :=
  by 
    rw [neg_one_pow_eq_pow_mod_two, gauss_lemma p ha0, neg_one_pow_eq_pow_mod_two,
      show _ = _ from eisenstein_lemma_aux₂ p ha1 ha0]

/-- **Quadratic reciprocity theorem** -/
theorem quadratic_reciprocity [hp1 : Fact (p % 2 = 1)] [hq1 : Fact (q % 2 = 1)] (hpq : p ≠ q) :
  (legendre_sym p q*legendre_sym q p) = (-1^(p / 2)*q / 2) :=
  have hpq0 : (p : Zmod q) ≠ 0 := prime_ne_zero q p hpq.symm 
  have hqp0 : (q : Zmod p) ≠ 0 := prime_ne_zero p q hpq 
  by 
    rw [eisenstein_lemma q hp1.1 hpq0, eisenstein_lemma p hq1.1 hqp0, ←pow_addₓ,
      sum_mul_div_add_sum_mul_div_eq_mul q p hpq0, mul_commₓ]

@[local instance]
theorem fact_prime_two : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

theorem legendre_sym_two [hp1 : Fact (p % 2 = 1)] : legendre_sym 2 p = (-1^(p / 4)+p / 2) :=
  have hp2 : p ≠ 2 :=
    mt (congr_argₓ (· % 2))
      (by 
        simpa using hp1.1)
  have hp22 : p / 2 / 2 = _ :=
    div_eq_filter_card
      (show 0 < 2 from
        by 
          decide)
      (Nat.div_le_selfₓ (p / 2) 2)
  have hcard : (Ico 1 (p / 2).succ).card = p / 2 :=
    by 
      simp 
  have hx2 : ∀ x _ : x ∈ Ico 1 (p / 2).succ, (2*x : Zmod p).val = 2*x :=
    fun x hx =>
      have h2xp : (2*x) < p :=
        calc (2*x) ≤ 2*p / 2 :=
          mul_le_mul_of_nonneg_left
            (le_of_lt_succ$
              by 
                finish)
            (by 
              decide)
          _ < _ :=
          by 
            convRHS => rw [←div_add_mod p 2, hp1.1] <;> exact lt_succ_self _ 
          
      by 
        rw [←Nat.cast_two, ←Nat.cast_mul, val_cast_of_lt h2xp]
  have hdisj :
    Disjoint ((Ico 1 (p / 2).succ).filter fun x => p / 2 < ((2 : ℕ)*x : Zmod p).val)
      ((Ico 1 (p / 2).succ).filter fun x => (x*2) ≤ p / 2) :=
    disjoint_filter.2
      fun x hx =>
        by 
          simp [hx2 _ hx, mul_commₓ]
  have hunion :
    (((Ico 1 (p / 2).succ).filter fun x => p / 2 < ((2 : ℕ)*x : Zmod p).val) ∪
        (Ico 1 (p / 2).succ).filter fun x => (x*2) ≤ p / 2) =
      Ico 1 (p / 2).succ :=
    by 
      rw [filter_union_right]
      convRHS => rw [←@filter_true _ (Ico 1 (p / 2).succ)]
      exact
        filter_congr
          fun x hx =>
            by 
              simp [hx2 _ hx, lt_or_leₓ, mul_commₓ]
  by 
    rw [gauss_lemma p (prime_ne_zero p 2 hp2), neg_one_pow_eq_pow_mod_two,
      @neg_one_pow_eq_pow_mod_two _ _ ((p / 4)+p / 2)]
    refine' congr_arg2 _ rfl ((eq_iff_modeq_nat 2).1 _)
    rw [show 4 = 2*2 from rfl, ←Nat.div_div_eq_div_mulₓ, hp22, Nat.cast_add, ←sub_eq_iff_eq_add', sub_eq_add_neg,
      neg_eq_self_mod_two, ←Nat.cast_add, ←card_disjoint_union hdisj, hunion, hcard]

theorem exists_sq_eq_two_iff [hp1 : Fact (p % 2 = 1)] : (∃ a : Zmod p, (a^2) = 2) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  have hp2 : ((2 : ℕ) : Zmod p) ≠ 0 :=
    prime_ne_zero p 2
      fun h =>
        by 
          simpa [h] using hp1.1
  have hpm4 : p % 4 = p % 8 % 4 := (Nat.mod_mul_left_mod p 2 4).symm 
  have hpm2 : p % 2 = p % 8 % 2 := (Nat.mod_mul_left_mod p 4 2).symm 
  by 
    rw
      [show (2 : Zmod p) = (2 : ℕ)by 
        simp ,
      ←legendre_sym_eq_one_iff p hp2, legendre_sym_two p,
      neg_one_pow_eq_one_iff_even
        (show (-1 : ℤ) ≠ 1 from
          by 
            decide),
      even_add, even_div, even_div]
    have  :=
      Nat.mod_ltₓ p
        (show 0 < 8 from
          by 
            decide)
    resetI 
    rw [fact_iff] at hp1 
    revert this hp1 
    erw [hpm4, hpm2]
    generalize hm : p % 8 = m 
    unfreezingI 
      clear! p 
    decide!

theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) [hq1 : Fact (q % 2 = 1)] :
  (∃ a : Zmod p, (a^2) = q) ↔ ∃ b : Zmod q, (b^2) = p :=
  if hpq : p = q then
    by 
      substI hpq
  else
    have h1 : ((p / 2)*q / 2) % 2 = 0 :=
      (dvd_iff_mod_eq_zero _ _).1
        (dvd_mul_of_dvd_left
          ((dvd_iff_mod_eq_zero _ _).2$
            by 
              rw [←mod_mul_right_div_self, show (2*2) = 4 from rfl, hp1] <;> rfl)
          _)
    by 
      haveI hp_odd : Fact (p % 2 = 1) := ⟨odd_of_mod_four_eq_one hp1⟩
      have hpq0 : (p : Zmod q) ≠ 0 := prime_ne_zero q p (Ne.symm hpq)
      have hqp0 : (q : Zmod p) ≠ 0 := prime_ne_zero p q hpq 
      have  := quadratic_reciprocity p q hpq 
      rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym, if_neg hqp0, if_neg hpq0] at this 
      rw [euler_criterion q hpq0, euler_criterion p hqp0]
      splitIfs  at this <;> simp  <;> contradiction

theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) (hpq : p ≠ q) :
  (∃ a : Zmod p, (a^2) = q) ↔ ¬∃ b : Zmod q, (b^2) = p :=
  have h1 : ((p / 2)*q / 2) % 2 = 1 :=
    Nat.odd_mul_odd
      (by 
        rw [←mod_mul_right_div_self, show (2*2) = 4 from rfl, hp3] <;> rfl)
      (by 
        rw [←mod_mul_right_div_self, show (2*2) = 4 from rfl, hq3] <;> rfl)
  by 
    haveI hp_odd : Fact (p % 2 = 1) := ⟨odd_of_mod_four_eq_three hp3⟩
    haveI hq_odd : Fact (q % 2 = 1) := ⟨odd_of_mod_four_eq_three hq3⟩
    have hpq0 : (p : Zmod q) ≠ 0 := prime_ne_zero q p (Ne.symm hpq)
    have hqp0 : (q : Zmod p) ≠ 0 := prime_ne_zero p q hpq 
    have  := quadratic_reciprocity p q hpq 
    rw [neg_one_pow_eq_pow_mod_two, h1, legendre_sym, legendre_sym, if_neg hpq0, if_neg hqp0] at this 
    rw [euler_criterion q hpq0, euler_criterion p hqp0]
    splitIfs  at this <;> simp  <;> contradiction

end Zmod

