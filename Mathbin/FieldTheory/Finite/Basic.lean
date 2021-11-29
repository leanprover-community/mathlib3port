import Mathbin.Tactic.ApplyFun 
import Mathbin.Data.Equiv.Ring 
import Mathbin.Data.Zmod.Algebra 
import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.RingTheory.IntegralDomain 
import Mathbin.FieldTheory.Separable 
import Mathbin.FieldTheory.SplittingField

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `ring_theory.integral_domain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`field_of_is_domain`).

## Main results

1. `fintype.card_units`: The unit group of a finite field is has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `finite_field.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `fintype (units K)` can be inferred from `fintype K` in the presence of `decidable_eq K`,
in this file we take the `fintype (units K)` argument directly to reduce the chance of typeclass
diamonds, as `fintype` carries data.

-/


variable {K : Type _} {R : Type _}

local notation "q" => Fintype.card K

open_locale BigOperators

namespace FiniteField

open Finset Function

section Polynomial

variable [CommRingₓ R] [IsDomain R]

open Polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : Polynomial R} (hp : 0 < p.degree) :
  Fintype.card R ≤ nat_degree p*(univ.Image fun x => eval x p).card :=
  Finset.card_le_mul_card_image _ _
    fun a _ =>
      calc _ = (p - C a).roots.toFinset.card :=
        congr_argₓ card
          (by 
            simp [Finset.ext_iff, mem_roots_sub_C hp])
        _ ≤ (p - C a).roots.card := Multiset.to_finset_card_le _ 
        _ ≤ _ := card_roots_sub_C' hp
        

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic
[fintype R]
{f g : polynomial R}
(hf2 : «expr = »(degree f, 2))
(hg2 : «expr = »(degree g, 2))
(hR : «expr = »(«expr % »(fintype.card R, 2), 1)) : «expr∃ , »((a b), «expr = »(«expr + »(f.eval a, g.eval b), 0)) :=
by letI [] [] [":=", expr classical.dec_eq R]; exact [expr suffices «expr¬ »(disjoint (univ.image (λ
    x : R, eval x f)) (univ.image (λ x : R, eval x «expr- »(g)))), begin
   simp [] [] ["only"] ["[", expr disjoint_left, ",", expr mem_image, "]"] [] ["at", ident this],
   push_neg ["at", ident this],
   rcases [expr this, "with", "⟨", ident x, ",", "⟨", ident a, ",", "_", ",", ident ha, "⟩", ",", "⟨", ident b, ",", "_", ",", ident hb, "⟩", "⟩"],
   exact [expr ⟨a, b, by rw ["[", expr ha, ",", "<-", expr hb, ",", expr eval_neg, ",", expr neg_add_self, "]"] []⟩]
 end,
 assume
 hd : disjoint _ _, «expr $ »(lt_irrefl «expr * »(2, «expr ∪ »(univ.image (λ
     x : R, eval x f), univ.image (λ x : R, eval x «expr- »(g))).card), calc
    «expr ≤ »(«expr * »(2, «expr ∪ »(univ.image (λ
        x : R, eval x f), univ.image (λ
        x : R, eval x «expr- »(g))).card), «expr * »(2, fintype.card R)) : nat.mul_le_mul_left _ (finset.card_le_univ _)
    «expr = »(..., «expr + »(fintype.card R, fintype.card R)) : two_mul _
    «expr < »(..., «expr + »(«expr * »(nat_degree f, (univ.image (λ
         x : R, eval x f)).card), «expr * »(nat_degree «expr- »(g), (univ.image (λ
         x : R, eval x «expr- »(g))).card))) : add_lt_add_of_lt_of_le (lt_of_le_of_ne (card_image_polynomial_eval (by rw [expr hf2] []; exact [expr exprdec_trivial()])) (mt (congr_arg ((«expr % » 2))) (by simp [] [] [] ["[", expr nat_degree_eq_of_degree_eq_some hf2, ",", expr hR, "]"] [] []))) (card_image_polynomial_eval (by rw ["[", expr degree_neg, ",", expr hg2, "]"] []; exact [expr exprdec_trivial()]))
    «expr = »(..., «expr * »(2, «expr ∪ »(univ.image (λ
        x : R, eval x f), univ.image (λ
        x : R, eval x «expr- »(g))).card)) : by rw ["[", expr card_disjoint_union hd, "]"] []; simp [] [] [] ["[", expr nat_degree_eq_of_degree_eq_some hf2, ",", expr nat_degree_eq_of_degree_eq_some hg2, ",", expr bit0, ",", expr mul_add, "]"] [] [])]

end Polynomial

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_univ_units_id_eq_neg_one
[field K]
[fintype (units K)] : «expr = »(«expr∏ , »((x : units K), x), («expr- »(1) : units K)) :=
begin
  classical,
  have [] [":", expr «expr = »(«expr∏ in , »((x), (@univ (units K) _).erase «expr- »(1), x), 1)] [],
  from [expr prod_involution (λ
    x
    _, «expr ⁻¹»(x)) (by simp [] [] [] [] [] []) (λ
    a, by simp [] [] [] ["[", expr units.inv_eq_self_iff, "]"] [] [] { contextual := tt }) (λ
    a, by simp [] [] [] ["[", expr @inv_eq_iff_inv_eq _ _ a, ",", expr eq_comm, "]"] [] [] { contextual := tt }) (by simp [] [] [] [] [] [])],
  rw ["[", "<-", expr insert_erase (mem_univ («expr- »(1) : units K)), ",", expr prod_insert (not_mem_erase _ _), ",", expr this, ",", expr mul_one, "]"] []
end

section 

variable [GroupWithZeroₓ K] [Fintype K]

theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : (a^q - 1) = 1 :=
  calc (a^Fintype.card K - 1) = (Units.mk0 a ha^Fintype.card K - 1 : Units K) :=
    by 
      rw [Units.coe_pow, Units.coe_mk0]
    _ = 1 :=
    by 
      classical 
      rw [←Fintype.card_units, pow_card_eq_one]
      rfl
    

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pow_card (a : K) : «expr = »(«expr ^ »(a, exprq()), a) :=
begin
  have [ident hp] [":", expr «expr < »(0, fintype.card K)] [":=", expr lt_trans zero_lt_one fintype.one_lt_card],
  by_cases [expr h, ":", expr «expr = »(a, 0)],
  { rw [expr h] [],
    apply [expr zero_pow hp] },
  rw ["[", "<-", expr nat.succ_pred_eq_of_pos hp, ",", expr pow_succ, ",", expr nat.pred_eq_sub_one, ",", expr pow_card_sub_one_eq_one a h, ",", expr mul_one, "]"] []
end

theorem pow_card_pow (n : ℕ) (a : K) : (a^q^n) = a :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      simp [pow_succₓ, pow_mulₓ, ih, pow_card]

end 

variable (K) [Field K] [Fintype K]

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card
(p : exprℕ())
[char_p K p] : «expr∃ , »((n : «exprℕ+»()), «expr ∧ »(nat.prime p, «expr = »(exprq(), «expr ^ »(p, (n : exprℕ()))))) :=
begin
  haveI [ident hp] [":", expr fact p.prime] [":=", expr ⟨char_p.char_is_prime K p⟩],
  letI [] [":", expr module (zmod p) K] [":=", expr { ..(zmod.cast_hom dvd_rfl K).to_module }],
  obtain ["⟨", ident n, ",", ident h, "⟩", ":=", expr vector_space.card_fintype (zmod p) K],
  rw [expr zmod.card] ["at", ident h],
  refine [expr ⟨⟨n, _⟩, hp.1, h⟩],
  apply [expr or.resolve_left (nat.eq_zero_or_pos n)],
  rintro [ident rfl],
  rw [expr pow_zero] ["at", ident h],
  have [] [":", expr «expr = »((0 : K), 1)] [],
  { apply [expr fintype.card_le_one_iff.mp (le_of_eq h)] },
  exact [expr absurd this zero_ne_one]
end

theorem card' : ∃ (p : ℕ)(n : ℕ+), Nat.Prime p ∧ Fintype.card K = (p^(n : ℕ)) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, @FiniteField.card K _ _ p hc⟩

@[simp]
theorem cast_card_eq_zero : (q : K) = 0 :=
  by 
    rcases CharP.exists K with ⟨p, _char_p⟩
    skip 
    rcases card K p with ⟨n, hp, hn⟩
    simp only [CharP.cast_eq_zero_iff K p, hn]
    conv  => congr rw [←pow_oneₓ p]
    exact pow_dvd_pow _ n.2

theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Units K, (x^i) = 1) ↔ q - 1 ∣ i :=
  by 
    classical 
    obtain ⟨x, hx⟩ := IsCyclic.exists_generator (Units K)
    rw [←Fintype.card_units, ←order_of_eq_card_of_forall_mem_zpowers hx, order_of_dvd_iff_pow_eq_one]
    split 
    ·
      intro h 
      apply h
    ·
      intro h y 
      simpRw [←mem_powers_iff_mem_zpowers]  at hx 
      rcases hx y with ⟨j, rfl⟩
      rw [←pow_mulₓ, mul_commₓ, pow_mulₓ, h, one_pow]

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
theorem sum_pow_units
[fintype (units K)]
(i : exprℕ()) : «expr = »(«expr∑ , »((x : units K), («expr ^ »(x, i) : K)), if «expr ∣ »(«expr - »(exprq(), 1), i) then «expr- »(1) else 0) :=
begin
  let [ident φ] [":", expr «expr →* »(units K, K)] [":=", expr { to_fun := λ x, «expr ^ »(x, i),
     map_one' := by rw ["[", expr units.coe_one, ",", expr one_pow, "]"] [],
     map_mul' := by { intros [],
       rw ["[", expr units.coe_mul, ",", expr mul_pow, "]"] [] } }],
  haveI [] [":", expr decidable «expr = »(φ, 1)] [],
  { classical,
    apply_instance },
  calc
    «expr = »(«expr∑ , »((x : units K), φ x), if «expr = »(φ, 1) then fintype.card (units K) else 0) : sum_hom_units φ
    «expr = »(..., if «expr ∣ »(«expr - »(exprq(), 1), i) then «expr- »(1) else 0) : _,
  suffices [] [":", expr «expr ↔ »(«expr ∣ »(«expr - »(exprq(), 1), i), «expr = »(φ, 1))],
  { simp [] [] ["only"] ["[", expr this, "]"] [] [],
    split_ifs [] ["with", ident h, ident h],
    swap,
    refl,
    rw ["[", expr fintype.card_units, ",", expr nat.cast_sub, ",", expr cast_card_eq_zero, ",", expr nat.cast_one, ",", expr zero_sub, "]"] [],
    show [expr «expr ≤ »(1, exprq())],
    from [expr fintype.card_pos_iff.mpr ⟨0⟩] },
  rw ["[", "<-", expr forall_pow_eq_one_iff, ",", expr monoid_hom.ext_iff, "]"] [],
  apply [expr forall_congr],
  intro [ident x],
  rw ["[", expr units.ext_iff, ",", expr units.coe_pow, ",", expr units.coe_one, ",", expr monoid_hom.one_apply, "]"] [],
  refl
end

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one
(i : exprℕ())
(h : «expr < »(i, «expr - »(exprq(), 1))) : «expr = »(«expr∑ , »((x : K), «expr ^ »(x, i)), 0) :=
begin
  by_cases [expr hi, ":", expr «expr = »(i, 0)],
  { simp [] [] ["only"] ["[", expr hi, ",", expr nsmul_one, ",", expr sum_const, ",", expr pow_zero, ",", expr card_univ, ",", expr cast_card_eq_zero, "]"] [] [] },
  classical,
  have [ident hiq] [":", expr «expr¬ »(«expr ∣ »(«expr - »(exprq(), 1), i))] [],
  { contrapose ["!"] [ident h],
    exact [expr nat.le_of_dvd (nat.pos_of_ne_zero hi) h] },
  let [ident φ] [":", expr «expr ↪ »(units K, K)] [":=", expr ⟨coe, units.ext⟩],
  have [] [":", expr «expr = »(univ.map φ, «expr \ »(univ, {0}))] [],
  { ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr true_and, ",", expr embedding.coe_fn_mk, ",", expr mem_sdiff, ",", expr units.exists_iff_ne_zero, ",", expr mem_univ, ",", expr mem_map, ",", expr exists_prop_of_true, ",", expr mem_singleton, "]"] [] [] },
  calc
    «expr = »(«expr∑ , »((x : K), «expr ^ »(x, i)), «expr∑ in , »((x), «expr \ »(univ, {(0 : K)}), «expr ^ »(x, i))) : by rw ["[", "<-", expr sum_sdiff ({0} : finset K).subset_univ, ",", expr sum_singleton, ",", expr zero_pow (nat.pos_of_ne_zero hi), ",", expr add_zero, "]"] []
    «expr = »(..., «expr∑ , »((x : units K), «expr ^ »(x, i))) : by { rw ["[", "<-", expr this, ",", expr univ.sum_map φ, "]"] [],
      refl }
    «expr = »(..., 0) : by { rw ["[", expr sum_pow_units K i, ",", expr if_neg, "]"] [],
      exact [expr hiq] }
end

section IsSplittingField

open Polynomial

section 

variable (K' : Type _) [Field K'] {p n : ℕ}

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem X_pow_card_sub_X_nat_degree_eq
(hp : «expr < »(1, p)) : «expr = »((«expr - »(«expr ^ »(X, p), X) : polynomial K').nat_degree, p) :=
begin
  have [ident h1] [":", expr «expr < »((X : polynomial K').degree, («expr ^ »(X, p) : polynomial K').degree)] [],
  { rw ["[", expr degree_X_pow, ",", expr degree_X, "]"] [],
    exact_mod_cast [expr hp] },
  rw ["[", expr nat_degree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), ",", expr nat_degree_X_pow, "]"] []
end

theorem X_pow_card_pow_sub_X_nat_degree_eq (hn : n ≠ 0) (hp : 1 < p) :
  ((X^p^n) - X : Polynomial K').natDegree = (p^n) :=
  X_pow_card_sub_X_nat_degree_eq K'$ Nat.one_lt_pow _ _ (Nat.pos_of_ne_zeroₓ hn) hp

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : ((X^p) - X : Polynomial K') ≠ 0 :=
  ne_zero_of_nat_degree_gt$
    calc 1 < _ := hp 
      _ = _ := (X_pow_card_sub_X_nat_degree_eq K' hp).symm
      

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : ((X^p^n) - X : Polynomial K') ≠ 0 :=
  X_pow_card_sub_X_ne_zero K'$ Nat.one_lt_pow _ _ (Nat.pos_of_ne_zeroₓ hn) hp

end 

variable (p : ℕ) [Fact p.prime] [CharP K p]

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem roots_X_pow_card_sub_X : «expr = »(roots («expr - »(«expr ^ »(X, exprq()), X) : polynomial K), finset.univ.val) :=
begin
  classical,
  have [ident aux] [":", expr «expr ≠ »((«expr - »(«expr ^ »(X, exprq()), X) : polynomial K), 0)] [":=", expr X_pow_card_sub_X_ne_zero K fintype.one_lt_card],
  have [] [":", expr «expr = »((roots («expr - »(«expr ^ »(X, exprq()), X) : polynomial K)).to_finset, finset.univ)] [],
  { rw [expr eq_univ_iff_forall] [],
    intro [ident x],
    rw ["[", expr multiset.mem_to_finset, ",", expr mem_roots aux, ",", expr is_root.def, ",", expr eval_sub, ",", expr eval_pow, ",", expr eval_X, ",", expr sub_eq_zero, ",", expr pow_card, "]"] [] },
  rw ["[", "<-", expr this, ",", expr multiset.to_finset_val, ",", expr eq_comm, ",", expr multiset.erase_dup_eq_self, "]"] [],
  apply [expr nodup_roots],
  rw [expr separable_def] [],
  convert [] [expr is_coprime_one_right.neg_right] [],
  rw ["[", expr derivative_sub, ",", expr derivative_X, ",", expr derivative_X_pow, ",", "<-", expr C_eq_nat_cast, ",", expr C_eq_zero.mpr (char_p.cast_card_eq_zero K), ",", expr zero_mul, ",", expr zero_sub, "]"] []
end

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : is_splitting_field (zmod p) K «expr - »(«expr ^ »(X, exprq()), X) :=
{ splits := begin
    have [ident h] [":", expr «expr = »((«expr - »(«expr ^ »(X, exprq()), X) : polynomial K).nat_degree, exprq())] [":=", expr X_pow_card_sub_X_nat_degree_eq K fintype.one_lt_card],
    rw ["[", "<-", expr splits_id_iff_splits, ",", expr splits_iff_card_roots, ",", expr map_sub, ",", expr map_pow, ",", expr map_X, ",", expr h, ",", expr roots_X_pow_card_sub_X K, ",", "<-", expr finset.card_def, ",", expr finset.card_univ, "]"] []
  end,
  adjoin_roots := begin
    classical,
    transitivity [expr algebra.adjoin (zmod p) ((roots («expr - »(«expr ^ »(X, exprq()), X) : polynomial K)).to_finset : set K)],
    { simp [] [] ["only"] ["[", expr map_pow, ",", expr map_X, ",", expr map_sub, "]"] [] [],
      convert [] [expr rfl] [] },
    { rw ["[", expr roots_X_pow_card_sub_X, ",", expr val_to_finset, ",", expr coe_univ, ",", expr algebra.adjoin_univ, "]"] [] }
  end }

end IsSplittingField

variable {K}

theorem frobenius_pow {p : ℕ} [Fact p.prime] [CharP K p] {n : ℕ} (hcard : q = (p^n)) : (frobenius K p^n) = 1 :=
  by 
    ext 
    convRHS => rw [RingHom.one_def, RingHom.id_apply, ←pow_card x, hcard]
    clear hcard 
    induction n
    ·
      simp 
    rw [pow_succₓ, pow_succ'ₓ, pow_mulₓ, RingHom.mul_def, RingHom.comp_apply, frobenius_def, n_ih]

open Polynomial

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem expand_card (f : polynomial K) : «expr = »(expand K exprq() f, «expr ^ »(f, exprq())) :=
begin
  cases [expr char_p.exists K] ["with", ident p, ident hp],
  letI [] [] [":=", expr hp],
  rcases [expr finite_field.card K p, "with", "⟨", "⟨", ident n, ",", ident npos, "⟩", ",", "⟨", ident hp, ",", ident hn, "⟩", "⟩"],
  haveI [] [":", expr fact p.prime] [":=", expr ⟨hp⟩],
  dsimp [] [] [] ["at", ident hn],
  rw ["[", expr hn, ",", "<-", expr map_expand_pow_char, ",", expr frobenius_pow hn, ",", expr ring_hom.one_def, ",", expr map_id, "]"] []
end

end FiniteField

namespace Zmod

open FiniteField Polynomial

theorem sq_add_sq (p : ℕ) [hp : Fact p.prime] (x : Zmod p) : ∃ a b : Zmod p, ((a^2)+b^2) = x :=
  by 
    cases' hp.1.eq_two_or_odd with hp2 hp_odd
    ·
      subst p 
      change Finₓ 2 at x 
      finCases x
      ·
        use 0
        simp 
      ·
        use 0, 1
        simp 
    let f : Polynomial (Zmod p) := X^2
    let g : Polynomial (Zmod p) := (X^2) - C x 
    obtain ⟨a, b, hab⟩ : ∃ a b, (f.eval a+g.eval b) = 0 :=
      @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2)
        (degree_X_pow_sub_C
          (by 
            decide)
          _)
        (by 
          rw [Zmod.card, hp_odd])
    refine' ⟨a, b, _⟩
    rw [←sub_eq_zero]
    simpa only [eval_C, eval_X, eval_pow, eval_sub, ←add_sub_assoc] using hab

end Zmod

namespace CharP

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sq_add_sq
(R : Type*)
[comm_ring R]
[is_domain R]
(p : exprℕ())
[fact «expr < »(0, p)]
[char_p R p]
(x : exprℤ()) : «expr∃ , »((a b : exprℕ()), «expr = »((«expr + »(«expr ^ »(a, 2), «expr ^ »(b, 2)) : R), x)) :=
begin
  haveI [] [] [":=", expr char_is_prime_of_pos R p],
  obtain ["⟨", ident a, ",", ident b, ",", ident hab, "⟩", ":=", expr zmod.sq_add_sq p x],
  refine [expr ⟨a.val, b.val, _⟩],
  simpa [] [] [] [] [] ["using", expr congr_arg (zmod.cast_hom dvd_rfl R) hab]
end

end CharP

open_locale Nat

open Zmod

/-- The **Fermat-Euler totient theorem**. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
theorem Zmod.pow_totient {n : ℕ} [Fact (0 < n)] (x : Units (Zmod n)) : (x^φ n) = 1 :=
  by 
    rw [←card_units_eq_totient, pow_card_eq_one]

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The **Fermat-Euler totient theorem**. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem nat.modeq.pow_totient {x n : exprℕ()} (h : nat.coprime x n) : «expr ≡ [MOD ]»(«expr ^ »(x, exprφ() n), 1, n) :=
begin
  cases [expr n] [],
  { simp [] [] [] [] [] [] },
  rw ["<-", expr zmod.eq_iff_modeq_nat] [],
  let [ident x'] [":", expr units (zmod «expr + »(n, 1))] [":=", expr zmod.unit_of_coprime _ h],
  have [] [] [":=", expr zmod.pow_totient x'],
  apply_fun [expr (coe : units (zmod «expr + »(n, 1)) → zmod «expr + »(n, 1))] ["at", ident this] [],
  simpa [] [] ["only"] ["[", "-", ident zmod.pow_totient, ",", expr nat.succ_eq_add_one, ",", expr nat.cast_pow, ",", expr units.coe_one, ",", expr nat.cast_one, ",", expr coe_unit_of_coprime, ",", expr units.coe_pow, "]"] [] []
end

section 

variable {V : Type _} [Fintype K] [DivisionRing K] [AddCommGroupₓ V] [Module K V]

theorem card_eq_pow_finrank [Fintype V] : Fintype.card V = (q^FiniteDimensional.finrank K V) :=
  by 
    let b := IsNoetherian.finsetBasis K V 
    rw [Module.card_fintype b, ←FiniteDimensional.finrank_eq_card_basis b]

end 

open FiniteField

namespace Zmod

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A variation on Fermat's little theorem. See `zmod.pow_card_sub_one_eq_one` -/
@[simp]
theorem pow_card {p : exprℕ()} [fact p.prime] (x : zmod p) : «expr = »(«expr ^ »(x, p), x) :=
by { have [ident h] [] [":=", expr finite_field.pow_card x],
  rwa [expr zmod.card p] ["at", ident h] }

@[simp]
theorem pow_card_pow {n p : ℕ} [Fact p.prime] (x : Zmod p) : (x^p^n) = x :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      simp [pow_succₓ, pow_mulₓ, ih, pow_card]

@[simp]
theorem frobenius_zmod (p : ℕ) [Fact p.prime] : frobenius (Zmod p) p = RingHom.id _ :=
  by 
    ext a 
    rw [frobenius_def, Zmod.pow_card, RingHom.id_apply]

@[simp]
theorem card_units (p : ℕ) [Fact p.prime] : Fintype.card (Units (Zmod p)) = p - 1 :=
  by 
    rw [Fintype.card_units, card]

/-- **Fermat's Little Theorem**: for every unit `a` of `zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.prime] (a : Units (Zmod p)) : (a^p - 1) = 1 :=
  by 
    rw [←card_units p, pow_card_eq_one]

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Fermat's Little Theorem**: for all nonzero `a : zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one
{p : exprℕ()}
[fact p.prime]
{a : zmod p}
(ha : «expr ≠ »(a, 0)) : «expr = »(«expr ^ »(a, «expr - »(p, 1)), 1) :=
by { have [ident h] [] [":=", expr pow_card_sub_one_eq_one a ha],
  rwa [expr zmod.card p] ["at", ident h] }

open Polynomial

-- error in FieldTheory.Finite.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem expand_card
{p : exprℕ()}
[fact p.prime]
(f : polynomial (zmod p)) : «expr = »(expand (zmod p) p f, «expr ^ »(f, p)) :=
by { have [ident h] [] [":=", expr finite_field.expand_card f],
  rwa [expr zmod.card p] ["at", ident h] }

end Zmod

