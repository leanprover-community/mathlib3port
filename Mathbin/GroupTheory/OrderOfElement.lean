import Mathbin.Data.Int.Gcd 
import Mathbin.Algebra.IterateHom 
import Mathbin.Algebra.Pointwise 
import Mathbin.Dynamics.PeriodicPts 
import Mathbin.GroupTheory.Coset

/-!
# Order of an element

This file defines the order of an element of a finite group. For a finite group `G` the order of
`x ∈ G` is the minimal `n ≥ 1` such that `x ^ n = 1`.

## Main definitions

* `is_of_fin_order` is a predicate on an element `x` of a monoid `G` saying that `x` is of finite
  order.
* `is_of_fin_add_order` is the additive analogue of `is_of_find_order`.
* `order_of x` defines the order of an element `x` of a monoid `G`, by convention its value is `0`
  if `x` has infinite order.
* `add_order_of` is the additive analogue of `order_of`.

## Tags
order of an element
-/


open Function Nat

open_locale Pointwise

universe u v

variable{G : Type u}{A : Type v}

variable{x y : G}{a b : A}{n m : ℕ}

section MonoidAddMonoid

variable[Monoidₓ G][AddMonoidₓ A]

section IsOfFinOrder

theorem is_periodic_pt_add_iff_nsmul_eq_zero (a : A) : is_periodic_pt ((·+·) a) n 0 ↔ n • a = 0 :=
  by 
    rw [is_periodic_pt, is_fixed_pt, add_left_iterate, add_zeroₓ]

@[toAdditive is_periodic_pt_add_iff_nsmul_eq_zero]
theorem is_periodic_pt_mul_iff_pow_eq_one (x : G) : is_periodic_pt ((·*·) x) n 1 ↔ x ^ n = 1 :=
  by 
    rw [is_periodic_pt, is_fixed_pt, mul_left_iterate, mul_oneₓ]

/-- `is_of_fin_add_order` is a predicate on an element `a` of an additive monoid to be of finite
order, i.e. there exists `n ≥ 1` such that `n • a = 0`.-/
def IsOfFinAddOrder (a : A) : Prop :=
  (0 : A) ∈ periodic_pts ((·+·) a)

/-- `is_of_fin_order` is a predicate on an element `x` of a monoid to be of finite order, i.e. there
exists `n ≥ 1` such that `x ^ n = 1`.-/
@[toAdditive IsOfFinAddOrder]
def IsOfFinOrder (x : G) : Prop :=
  (1 : G) ∈ periodic_pts ((·*·) x)

theorem is_of_fin_add_order_of_mul_iff : IsOfFinAddOrder (Additive.ofMul x) ↔ IsOfFinOrder x :=
  Iff.rfl

theorem is_of_fin_order_of_add_iff : IsOfFinOrder (Multiplicative.ofAdd a) ↔ IsOfFinAddOrder a :=
  Iff.rfl

theorem is_of_fin_add_order_iff_nsmul_eq_zero (a : A) : IsOfFinAddOrder a ↔ ∃ n, 0 < n ∧ n • a = 0 :=
  by 
    convert Iff.rfl 
    simp only [exists_prop, is_periodic_pt_add_iff_nsmul_eq_zero]

@[toAdditive is_of_fin_add_order_iff_nsmul_eq_zero]
theorem is_of_fin_order_iff_pow_eq_one (x : G) : IsOfFinOrder x ↔ ∃ n, 0 < n ∧ x ^ n = 1 :=
  by 
    convert Iff.rfl 
    simp [is_periodic_pt_mul_iff_pow_eq_one]

end IsOfFinOrder

/-- `order_of x` is the order of the element `x`, i.e. the `n ≥ 1`, s.t. `x ^ n = 1` if it exists.
Otherwise, i.e. if `x` is of infinite order, then `order_of x` is `0` by convention.-/
@[toAdditive addOrderOf
      "`add_order_of a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it\nexists. Otherwise, i.e. if `a` is of infinite order, then `add_order_of a` is `0` by convention."]
noncomputable def orderOf (x : G) : ℕ :=
  minimal_period ((·*·) x) 1

@[toAdditive]
theorem Commute.order_of_mul_dvd_lcm (h : Commute x y) : orderOf (x*y) ∣ Nat.lcmₓ (orderOf x) (orderOf y) :=
  by 
    convert Function.Commute.minimal_period_of_comp_dvd_lcm h.function_commute_mul_left 
    rw [orderOf, comp_mul_left]

@[simp]
theorem add_order_of_of_mul_eq_order_of (x : G) : addOrderOf (Additive.ofMul x) = orderOf x :=
  rfl

@[simp]
theorem order_of_of_add_eq_add_order_of (a : A) : orderOf (Multiplicative.ofAdd a) = addOrderOf a :=
  rfl

@[toAdditive add_order_of_pos']
theorem order_of_pos' (h : IsOfFinOrder x) : 0 < orderOf x :=
  minimal_period_pos_of_mem_periodic_pts h

@[toAdditive add_order_of_nsmul_eq_zero]
theorem pow_order_of_eq_one (x : G) : x ^ orderOf x = 1 :=
  by 
    convert is_periodic_pt_minimal_period ((·*·) x) _ 
    rw [orderOf, mul_left_iterate, mul_oneₓ]

@[toAdditive add_order_of_eq_zero]
theorem order_of_eq_zero (h : ¬IsOfFinOrder x) : orderOf x = 0 :=
  by 
    rwa [orderOf, minimal_period, dif_neg]

@[toAdditive add_order_of_eq_zero_iff]
theorem order_of_eq_zero_iff : orderOf x = 0 ↔ ¬IsOfFinOrder x :=
  ⟨fun h H => (order_of_pos' H).ne' h, order_of_eq_zero⟩

@[toAdditive nsmul_ne_zero_of_lt_add_order_of']
theorem pow_ne_one_of_lt_order_of' (n0 : n ≠ 0) (h : n < orderOf x) : x ^ n ≠ 1 :=
  fun j => not_is_periodic_pt_of_pos_of_lt_minimal_period n0 h ((is_periodic_pt_mul_iff_pow_eq_one x).mpr j)

@[toAdditive add_order_of_le_of_nsmul_eq_zero]
theorem order_of_le_of_pow_eq_one (hn : 0 < n) (h : x ^ n = 1) : orderOf x ≤ n :=
  is_periodic_pt.minimal_period_le hn
    (by 
      rwa [is_periodic_pt_mul_iff_pow_eq_one])

@[simp, toAdditive]
theorem order_of_one : orderOf (1 : G) = 1 :=
  by 
    rw [orderOf, one_mul_eq_id, minimal_period_id]

@[simp, toAdditive AddMonoidₓ.order_of_eq_one_iff]
theorem order_of_eq_one_iff : orderOf x = 1 ↔ x = 1 :=
  by 
    rw [orderOf, is_fixed_point_iff_minimal_period_eq_one, is_fixed_pt, mul_oneₓ]

@[toAdditive nsmul_eq_mod_add_order_of]
theorem pow_eq_mod_order_of {n : ℕ} : x ^ n = x ^ (n % orderOf x) :=
  calc x ^ n = x ^ (n % orderOf x)+orderOf x*n / orderOf x :=
    by 
      rw [Nat.mod_add_divₓ]
    _ = x ^ (n % orderOf x) :=
    by 
      simp [pow_addₓ, pow_mulₓ, pow_order_of_eq_one]
    

@[toAdditive add_order_of_dvd_of_nsmul_eq_zero]
theorem order_of_dvd_of_pow_eq_one (h : x ^ n = 1) : orderOf x ∣ n :=
  is_periodic_pt.minimal_period_dvd ((is_periodic_pt_mul_iff_pow_eq_one _).mpr h)

@[toAdditive add_order_of_dvd_iff_nsmul_eq_zero]
theorem order_of_dvd_iff_pow_eq_one {n : ℕ} : orderOf x ∣ n ↔ x ^ n = 1 :=
  ⟨fun h =>
      by 
        rw [pow_eq_mod_order_of, Nat.mod_eq_zero_of_dvdₓ h, pow_zeroₓ],
    order_of_dvd_of_pow_eq_one⟩

@[toAdditive exists_nsmul_eq_self_of_coprime]
theorem exists_pow_eq_self_of_coprime (h : n.coprime (orderOf x)) : ∃ m : ℕ, (x ^ n) ^ m = x :=
  by 
    byCases' h0 : orderOf x = 0
    ·
      rw [h0, coprime_zero_right] at h 
      exact
        ⟨1,
          by 
            rw [h, pow_oneₓ, pow_oneₓ]⟩
    byCases' h1 : orderOf x = 1
    ·
      exact
        ⟨0,
          by 
            rw [order_of_eq_one_iff.mp h1, one_pow, one_pow]⟩
    obtain ⟨m, hm⟩ := exists_mul_mod_eq_one_of_coprime h (one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, h1⟩)
    exact
      ⟨m,
        by 
          rw [←pow_mulₓ, pow_eq_mod_order_of, hm, pow_oneₓ]⟩

-- error in GroupTheory.OrderOfElement: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `x^n = 1`, but `x^(n/p) ≠ 1` for all prime factors `p` of `r`,
then `x` has order `n` in `G`.
-/
@[to_additive #[ident add_order_of_eq_of_nsmul_and_div_prime_nsmul]]
theorem order_of_eq_of_pow_and_pow_div_prime
(hn : «expr < »(0, n))
(hx : «expr = »(«expr ^ »(x, n), 1))
(hd : ∀
 p : exprℕ(), p.prime → «expr ∣ »(p, n) → «expr ≠ »(«expr ^ »(x, «expr / »(n, p)), 1)) : «expr = »(order_of x, n) :=
begin
  cases [expr exists_eq_mul_right_of_dvd (order_of_dvd_of_pow_eq_one hx)] ["with", ident a, ident ha],
  suffices [] [":", expr «expr = »(a, 1)],
  by simp [] [] [] ["[", expr this, ",", expr ha, "]"] [] [],
  by_contra [],
  have [ident a_min_fac_dvd_p_sub_one] [":", expr «expr ∣ »(a.min_fac, n)] [],
  { obtain ["⟨", ident b, ",", ident hb, "⟩", ":", expr «expr∃ , »((b : exprℕ()), «expr = »(a, «expr * »(b, a.min_fac))), ":=", expr exists_eq_mul_left_of_dvd a.min_fac_dvd],
    rw ["[", expr hb, ",", "<-", expr mul_assoc, "]"] ["at", ident ha],
    exact [expr dvd.intro_left «expr * »(order_of x, b) ha.symm] },
  refine [expr hd a.min_fac (nat.min_fac_prime h) a_min_fac_dvd_p_sub_one _],
  rw ["[", "<-", expr order_of_dvd_iff_pow_eq_one, ",", expr nat.dvd_div_iff a_min_fac_dvd_p_sub_one, ",", expr ha, ",", expr mul_comm, ",", expr nat.mul_dvd_mul_iff_left (order_of_pos' _), "]"] [],
  { exact [expr nat.min_fac_dvd a] },
  { rw [expr is_of_fin_order_iff_pow_eq_one] [],
    exact [expr Exists.intro n (id ⟨hn, hx⟩)] }
end

@[toAdditive add_order_of_eq_add_order_of_iff]
theorem order_of_eq_order_of_iff {H : Type _} [Monoidₓ H] {y : H} :
  orderOf x = orderOf y ↔ ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1 :=
  by 
    simpRw [←is_periodic_pt_mul_iff_pow_eq_one, ←minimal_period_eq_minimal_period_iff, orderOf]

@[toAdditive add_order_of_injective]
theorem order_of_injective {H : Type _} [Monoidₓ H] (f : G →* H) (hf : Function.Injective f) (x : G) :
  orderOf (f x) = orderOf x :=
  by 
    simpRw [order_of_eq_order_of_iff, ←f.map_pow, ←f.map_one, hf.eq_iff, iff_selfₓ, forall_const]

@[simp, normCast, toAdditive]
theorem order_of_submonoid {H : Submonoid G} (y : H) : orderOf (y : G) = orderOf y :=
  order_of_injective H.subtype Subtype.coe_injective y

@[toAdditive order_of_add_units]
theorem order_of_units {y : Units G} : orderOf (y : G) = orderOf y :=
  order_of_injective (Units.coeHom G) Units.ext y

variable(x)

@[toAdditive add_order_of_nsmul']
theorem order_of_pow' (h : n ≠ 0) : orderOf (x ^ n) = orderOf x / gcd (orderOf x) n :=
  by 
    convert minimal_period_iterate_eq_div_gcd h 
    simp only [orderOf, mul_left_iterate]

variable(a)

variable(n)

@[toAdditive add_order_of_nsmul'']
theorem order_of_pow'' (h : IsOfFinOrder x) : orderOf (x ^ n) = orderOf x / gcd (orderOf x) n :=
  by 
    convert minimal_period_iterate_eq_div_gcd' h 
    simp only [orderOf, mul_left_iterate]

section PPrime

variable{a x n}{p : ℕ}[hp : Fact p.prime]

include hp

theorem add_order_of_eq_prime (hg : p • a = 0) (hg1 : a ≠ 0) : addOrderOf a = p :=
  minimal_period_eq_prime ((is_periodic_pt_add_iff_nsmul_eq_zero _).mpr hg)
    (by 
      rwa [is_fixed_pt, add_zeroₓ])

@[toAdditive add_order_of_eq_prime]
theorem order_of_eq_prime (hg : x ^ p = 1) (hg1 : x ≠ 1) : orderOf x = p :=
  minimal_period_eq_prime ((is_periodic_pt_mul_iff_pow_eq_one _).mpr hg)
    (by 
      rwa [is_fixed_pt, mul_oneₓ])

@[toAdditive add_order_of_eq_prime_pow]
theorem order_of_eq_prime_pow (hnot : ¬x ^ p ^ n = 1) (hfin : (x ^ p ^ n+1) = 1) : orderOf x = p ^ n+1 :=
  by 
    apply minimal_period_eq_prime_pow <;> rwa [is_periodic_pt_mul_iff_pow_eq_one]

omit hp

-- error in GroupTheory.OrderOfElement: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
example : «expr = »(order_of («expr- »(1) : units exprℤ()), 2) :=
begin
  haveI [] [":", expr fact (prime 2)] [":=", expr ⟨prime_two⟩],
  exact [expr order_of_eq_prime (int.units_mul_self _) exprdec_trivial()]
end

end PPrime

end MonoidAddMonoid

section CancelMonoid

variable[LeftCancelMonoid G](x)

variable[AddLeftCancelMonoid A](a)

@[toAdditive nsmul_injective_aux]
theorem pow_injective_aux (h : n ≤ m) (hm : m < orderOf x) (eq : x ^ n = x ^ m) : n = m :=
  by_contradiction$
    fun ne : n ≠ m =>
      have h₁ : m - n > 0 :=
        Nat.pos_of_ne_zeroₓ
          (by 
            simp [tsub_eq_iff_eq_add_of_le h, Ne.symm])
      have h₂ : m = n+m - n := (add_tsub_cancel_of_le h).symm 
      have h₃ : x ^ (m - n) = 1 :=
        by 
          rw [h₂, pow_addₓ] at eq 
          apply mul_left_cancelₓ 
          convert Eq.symm 
          exact mul_oneₓ (x ^ n)
      have le : orderOf x ≤ m - n := order_of_le_of_pow_eq_one h₁ h₃ 
      have lt : m - n < orderOf x := (tsub_lt_iff_left h).mpr$ Nat.lt_add_left _ _ _ hm 
      lt_irreflₓ _ (le.trans_lt lt)

@[toAdditive nsmul_injective_of_lt_add_order_of]
theorem pow_injective_of_lt_order_of (hn : n < orderOf x) (hm : m < orderOf x) (eq : x ^ n = x ^ m) : n = m :=
  (le_totalₓ n m).elim (fun h => pow_injective_aux x h hm Eq) fun h => (pow_injective_aux x h hn Eq.symm).symm

end CancelMonoid

section Groupₓ

variable[Groupₓ G][AddGroupₓ A]{x a}{i : ℤ}

@[toAdditive add_order_of_dvd_iff_zsmul_eq_zero]
theorem order_of_dvd_iff_zpow_eq_one : (orderOf x : ℤ) ∣ i ↔ x ^ i = 1 :=
  by 
    rcases Int.eq_coe_or_neg i with ⟨i, rfl | rfl⟩
    ·
      rw [Int.coe_nat_dvd, order_of_dvd_iff_pow_eq_one, zpow_coe_nat]
    ·
      rw [dvd_neg, Int.coe_nat_dvd, zpow_neg, inv_eq_one, zpow_coe_nat, order_of_dvd_iff_pow_eq_one]

@[simp, normCast, toAdditive]
theorem order_of_subgroup {H : Subgroup G} (y : H) : orderOf (y : G) = orderOf y :=
  order_of_injective H.subtype Subtype.coe_injective y

@[toAdditive zsmul_eq_mod_add_order_of]
theorem zpow_eq_mod_order_of : x ^ i = x ^ (i % orderOf x) :=
  calc x ^ i = x ^ (i % orderOf x)+orderOf x*i / orderOf x :=
    by 
      rw [Int.mod_add_div]
    _ = x ^ (i % orderOf x) :=
    by 
      simp [zpow_add, zpow_mul, pow_order_of_eq_one]
    

set_option pp.all true

@[toAdditive nsmul_inj_iff_of_add_order_of_eq_zero]
theorem pow_inj_iff_of_order_of_eq_zero (h : orderOf x = 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m :=
  by 
    byCases' hx : x = 1
    ·
      rw [←order_of_eq_one_iff, h] at hx 
      contradiction 
    rw [order_of_eq_zero_iff, is_of_fin_order_iff_pow_eq_one] at h 
    pushNeg  at h 
    induction' n with n IH generalizing m
    ·
      cases m
      ·
        simp 
      ·
        simpa [eq_comm] using h m.succ m.zero_lt_succ
    ·
      cases m
      ·
        simpa using h n.succ n.zero_lt_succ
      ·
        simp [pow_succₓ, IH]

@[toAdditive nsmul_inj_mod]
theorem pow_inj_mod {n m : ℕ} : x ^ n = x ^ m ↔ n % orderOf x = m % orderOf x :=
  by 
    cases' (orderOf x).zero_le.eq_or_lt with hx hx
    ·
      simp [pow_inj_iff_of_order_of_eq_zero, hx.symm]
    rw [pow_eq_mod_order_of, @pow_eq_mod_order_of _ _ _ m]
    exact ⟨pow_injective_of_lt_order_of _ (Nat.mod_ltₓ _ hx) (Nat.mod_ltₓ _ hx), fun h => congr_argₓ _ h⟩

end Groupₓ

section Fintype

variable[Fintype G][Fintype A]

section FiniteMonoid

variable[Monoidₓ G][AddMonoidₓ A]

open_locale BigOperators

@[toAdditive sum_card_add_order_of_eq_card_nsmul_eq_zero]
theorem sum_card_order_of_eq_card_pow_eq_one [DecidableEq G] (hn : 0 < n) :
  (∑m in (Finset.range n.succ).filter (· ∣ n), (Finset.univ.filter fun x : G => orderOf x = m).card) =
    (Finset.univ.filter fun x : G => x ^ n = 1).card :=
  calc (∑m in (Finset.range n.succ).filter (· ∣ n), (Finset.univ.filter fun x : G => orderOf x = m).card) = _ :=
    (Finset.card_bUnion
        (by 
          intros 
          apply Finset.disjoint_filter.2
          cc)).symm
      
    _ = _ :=
    congr_argₓ Finset.card
      (Finset.ext
        (by 
          intro x 
          suffices  : orderOf x ≤ n ∧ orderOf x ∣ n ↔ x ^ n = 1
          ·
            simpa [Nat.lt_succ_iff]
          exact
            ⟨fun h =>
                let ⟨m, hm⟩ := h.2
                by 
                  rw [hm, pow_mulₓ, pow_order_of_eq_one, one_pow],
              fun h => ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩))
    

end FiniteMonoid

section FiniteCancelMonoid

variable[LeftCancelMonoid G][AddLeftCancelMonoid A]

@[toAdditive exists_nsmul_eq_zero]
theorem exists_pow_eq_one (x : G) : IsOfFinOrder x :=
  by 
    refine' (is_of_fin_order_iff_pow_eq_one _).mpr _ 
    obtain ⟨i, j, a_eq, ne⟩ : ∃ i j : ℕ, x ^ i = x ^ j ∧ i ≠ j :=
      by 
        simpa only [not_forall, exists_prop, injective] using not_injective_infinite_fintype fun i : ℕ => x ^ i 
    wlog h'' : j ≤ i 
    refine' ⟨i - j, tsub_pos_of_lt (lt_of_le_of_neₓ h'' Ne.symm), mul_right_injective (x ^ j) _⟩
    rw [mul_oneₓ, ←pow_addₓ, ←a_eq, add_tsub_cancel_of_le h'']

@[toAdditive add_order_of_le_card_univ]
theorem order_of_le_card_univ : orderOf x ≤ Fintype.card G :=
  Finset.le_card_of_inj_on_range ((· ^ ·) x) (fun n _ => Finset.mem_univ _)
    fun i hi j hj => pow_injective_of_lt_order_of x hi hj

/-- This is the same as `order_of_pos' but with one fewer explicit assumption since this is
  automatic in case of a finite cancellative monoid.-/
@[toAdditive add_order_of_pos
      "This is the same as `add_order_of_pos' but with one fewer explicit assumption since this is\n  automatic in case of a finite cancellative additive monoid."]
theorem order_of_pos (x : G) : 0 < orderOf x :=
  order_of_pos' (exists_pow_eq_one x)

open Nat

/-- This is the same as `order_of_pow'` and `order_of_pow''` but with one assumption less which is
automatic in the case of a finite cancellative monoid.-/
@[toAdditive add_order_of_nsmul
      "This is the same as `add_order_of_nsmul'` and `add_order_of_nsmul` but with one assumption less\nwhich is automatic in the case of a finite cancellative additive monoid."]
theorem order_of_pow (x : G) : orderOf (x ^ n) = orderOf x / gcd (orderOf x) n :=
  order_of_pow'' _ _ (exists_pow_eq_one _)

@[toAdditive mem_multiples_iff_mem_range_add_order_of]
theorem mem_powers_iff_mem_range_order_of [DecidableEq G] :
  y ∈ Submonoid.powers x ↔ y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x : ℕ → G) :=
  Finset.mem_range_iff_mem_finset_range_of_mod_eq' (order_of_pos x) fun i => pow_eq_mod_order_of.symm

@[toAdditive decidableMultiples]
noncomputable instance decidablePowers [DecidableEq G] : DecidablePred (· ∈ Submonoid.powers x) :=
  by 
    intro y 
    apply decidableOfIff' (y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x))
    exact mem_powers_iff_mem_range_order_of

/--The equivalence between `fin (order_of x)` and `submonoid.powers x`, sending `i` to `x ^ i`."-/
@[toAdditive finEquivMultiples
      "The equivalence between `fin (add_order_of a)` and\n`add_submonoid.multiples a`, sending `i` to `i • a`."]
noncomputable def finEquivPowers (x : G) : Finₓ (orderOf x) ≃ (Submonoid.powers x : Set G) :=
  Equiv.ofBijective (fun n => ⟨x ^ «expr↑ » n, ⟨n, rfl⟩⟩)
    ⟨fun ⟨i, hi⟩ ⟨j, hj⟩ ij => Subtype.mk_eq_mk.2 (pow_injective_of_lt_order_of x hi hj (Subtype.mk_eq_mk.1 ij)),
      fun ⟨_, i, rfl⟩ => ⟨⟨i % orderOf x, mod_lt i (order_of_pos x)⟩, Subtype.eq pow_eq_mod_order_of.symm⟩⟩

@[simp, toAdditive fin_equiv_multiples_apply]
theorem fin_equiv_powers_apply {x : G} {n : Finₓ (orderOf x)} : finEquivPowers x n = ⟨x ^ «expr↑ » n, n, rfl⟩ :=
  rfl

@[simp, toAdditive fin_equiv_multiples_symm_apply]
theorem fin_equiv_powers_symm_apply (x : G) (n : ℕ) {hn : ∃ m : ℕ, x ^ m = x ^ n} :
  (finEquivPowers x).symm ⟨x ^ n, hn⟩ = ⟨n % orderOf x, Nat.mod_ltₓ _ (order_of_pos x)⟩ :=
  by 
    rw [Equiv.symm_apply_eq, fin_equiv_powers_apply, Subtype.mk_eq_mk, pow_eq_mod_order_of, Finₓ.coe_mk]

/-- The equivalence between `submonoid.powers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[toAdditive multiplesEquivMultiples
      "The equivalence between `submonoid.multiples` of two elements `a, b` of the same additive order,\n  mapping `i • a` to `i • b`."]
noncomputable def powersEquivPowers (h : orderOf x = orderOf y) :
  (Submonoid.powers x : Set G) ≃ (Submonoid.powers y : Set G) :=
  (finEquivPowers x).symm.trans ((Finₓ.cast h).toEquiv.trans (finEquivPowers y))

@[simp, toAdditive multiples_equiv_multiples_apply]
theorem powers_equiv_powers_apply (h : orderOf x = orderOf y) (n : ℕ) :
  powersEquivPowers h ⟨x ^ n, n, rfl⟩ = ⟨y ^ n, n, rfl⟩ :=
  by 
    rw [powersEquivPowers, Equiv.trans_apply, Equiv.trans_apply, fin_equiv_powers_symm_apply, ←Equiv.eq_symm_apply,
      fin_equiv_powers_symm_apply]
    simp [h]

@[toAdditive add_order_of_eq_card_multiples]
theorem order_eq_card_powers [DecidableEq G] : orderOf x = Fintype.card (Submonoid.powers x : Set G) :=
  (Fintype.card_fin (orderOf x)).symm.trans (Fintype.card_eq.2 ⟨finEquivPowers x⟩)

end FiniteCancelMonoid

section FiniteGroup

variable[Groupₓ G][AddGroupₓ A]

@[toAdditive]
theorem exists_zpow_eq_one (x : G) : ∃ (i : ℤ)(H : i ≠ 0), x ^ (i : ℤ) = 1 :=
  by 
    rcases exists_pow_eq_one x with ⟨w, hw1, hw2⟩
    refine' ⟨w, int.coe_nat_ne_zero.mpr (ne_of_gtₓ hw1), _⟩
    rw [zpow_coe_nat]
    exact (is_periodic_pt_mul_iff_pow_eq_one _).mp hw2

open Subgroup

@[toAdditive mem_multiples_iff_mem_zmultiples]
theorem mem_powers_iff_mem_zpowers : y ∈ Submonoid.powers x ↔ y ∈ zpowers x :=
  ⟨fun ⟨n, hn⟩ =>
      ⟨n,
        by 
          simp_all ⟩,
    fun ⟨i, hi⟩ =>
      ⟨(i % orderOf x).natAbs,
        by 
          rwa [←zpow_coe_nat, Int.nat_abs_of_nonneg (Int.mod_nonneg _ (Int.coe_nat_ne_zero_iff_pos.2 (order_of_pos x))),
            ←zpow_eq_mod_order_of]⟩⟩

@[toAdditive multiples_eq_zmultiples]
theorem powers_eq_zpowers (x : G) : (Submonoid.powers x : Set G) = zpowers x :=
  Set.ext$ fun x => mem_powers_iff_mem_zpowers

@[toAdditive mem_zmultiples_iff_mem_range_add_order_of]
theorem mem_zpowers_iff_mem_range_order_of [DecidableEq G] :
  y ∈ Subgroup.zpowers x ↔ y ∈ (Finset.range (orderOf x)).Image ((· ^ ·) x : ℕ → G) :=
  by 
    rw [←mem_powers_iff_mem_zpowers, mem_powers_iff_mem_range_order_of]

@[toAdditive decidableZmultiples]
noncomputable instance decidableZpowers [DecidableEq G] : DecidablePred (· ∈ Subgroup.zpowers x) :=
  by 
    simpRw [←SetLike.mem_coe]
    rw [←powers_eq_zpowers]
    exact decidablePowers

/-- The equivalence between `fin (order_of x)` and `subgroup.zpowers x`, sending `i` to `x ^ i`. -/
@[toAdditive finEquivZmultiples
      "The equivalence between `fin (add_order_of a)` and `subgroup.zmultiples a`, sending `i`\nto `i • a`."]
noncomputable def finEquivZpowers (x : G) : Finₓ (orderOf x) ≃ (Subgroup.zpowers x : Set G) :=
  (finEquivPowers x).trans (Equiv.Set.ofEq (powers_eq_zpowers x))

@[simp, toAdditive fin_equiv_zmultiples_apply]
theorem fin_equiv_zpowers_apply {n : Finₓ (orderOf x)} : finEquivZpowers x n = ⟨x ^ (n : ℕ), n, zpow_coe_nat x n⟩ :=
  rfl

@[simp, toAdditive fin_equiv_zmultiples_symm_apply]
theorem fin_equiv_zpowers_symm_apply (x : G) (n : ℕ) {hn : ∃ m : ℤ, x ^ m = x ^ n} :
  (finEquivZpowers x).symm ⟨x ^ n, hn⟩ = ⟨n % orderOf x, Nat.mod_ltₓ _ (order_of_pos x)⟩ :=
  by 
    rw [finEquivZpowers, Equiv.symm_trans_apply, Equiv.Set.of_eq_symm_apply]
    exact fin_equiv_powers_symm_apply x n

/-- The equivalence between `subgroup.zpowers` of two elements `x, y` of the same order, mapping
  `x ^ i` to `y ^ i`. -/
@[toAdditive zmultiplesEquivZmultiples
      "The equivalence between `subgroup.zmultiples` of two elements `a, b` of the same additive order,\n  mapping `i • a` to `i • b`."]
noncomputable def zpowersEquivZpowers (h : orderOf x = orderOf y) :
  (Subgroup.zpowers x : Set G) ≃ (Subgroup.zpowers y : Set G) :=
  (finEquivZpowers x).symm.trans ((Finₓ.cast h).toEquiv.trans (finEquivZpowers y))

@[simp, toAdditive zmultiples_equiv_zmultiples_apply]
theorem zpowers_equiv_zpowers_apply (h : orderOf x = orderOf y) (n : ℕ) :
  zpowersEquivZpowers h ⟨x ^ n, n, zpow_coe_nat x n⟩ = ⟨y ^ n, n, zpow_coe_nat y n⟩ :=
  by 
    rw [zpowersEquivZpowers, Equiv.trans_apply, Equiv.trans_apply, fin_equiv_zpowers_symm_apply, ←Equiv.eq_symm_apply,
      fin_equiv_zpowers_symm_apply]
    simp [h]

@[toAdditive add_order_eq_card_zmultiples]
theorem order_eq_card_zpowers [DecidableEq G] : orderOf x = Fintype.card (Subgroup.zpowers x : Set G) :=
  (Fintype.card_fin (orderOf x)).symm.trans (Fintype.card_eq.2 ⟨finEquivZpowers x⟩)

open QuotientGroup

-- error in GroupTheory.OrderOfElement: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident add_order_of_dvd_card_univ]]
theorem order_of_dvd_card_univ : «expr ∣ »(order_of x, fintype.card G) :=
begin
  classical,
  have [ident ft_prod] [":", expr fintype «expr × »(quotient (zpowers x), zpowers x)] [],
  from [expr fintype.of_equiv G group_equiv_quotient_times_subgroup],
  have [ident ft_s] [":", expr fintype (zpowers x)] [],
  from [expr @fintype.prod_right _ _ _ ft_prod _],
  have [ident ft_cosets] [":", expr fintype (quotient (zpowers x))] [],
  from [expr @fintype.prod_left _ _ _ ft_prod ⟨⟨1, (zpowers x).one_mem⟩⟩],
  have [ident eq₁] [":", expr «expr = »(fintype.card G, «expr * »(@fintype.card _ ft_cosets, @fintype.card _ ft_s))] [],
  from [expr calc
     «expr = »(fintype.card G, @fintype.card _ ft_prod) : @fintype.card_congr _ _ _ ft_prod group_equiv_quotient_times_subgroup
     «expr = »(..., @fintype.card _ (@prod.fintype _ _ ft_cosets ft_s)) : «expr $ »(congr_arg (@fintype.card _), subsingleton.elim _ _)
     «expr = »(..., «expr * »(@fintype.card _ ft_cosets, @fintype.card _ ft_s)) : @fintype.card_prod _ _ ft_cosets ft_s],
  have [ident eq₂] [":", expr «expr = »(order_of x, @fintype.card _ ft_s)] [],
  from [expr calc
     «expr = »(order_of x, _) : order_eq_card_zpowers
     «expr = »(..., _) : «expr $ »(congr_arg (@fintype.card _), subsingleton.elim _ _)],
  exact [expr dvd.intro (@fintype.card (quotient (subgroup.zpowers x)) ft_cosets) (by rw ["[", expr eq₁, ",", expr eq₂, ",", expr mul_comm, "]"] [])]
end

@[simp, toAdditive card_nsmul_eq_zero]
theorem pow_card_eq_one : x ^ Fintype.card G = 1 :=
  let ⟨m, hm⟩ := @order_of_dvd_card_univ _ x _ _ 
  by 
    simp [hm, pow_mulₓ, pow_order_of_eq_one]

@[toAdditive nsmul_eq_mod_card]
theorem pow_eq_mod_card (n : ℕ) : x ^ n = x ^ (n % Fintype.card G) :=
  by 
    rw [pow_eq_mod_order_of, ←Nat.mod_mod_of_dvd n order_of_dvd_card_univ, ←pow_eq_mod_order_of]

@[toAdditive]
theorem zpow_eq_mod_card (n : ℤ) : x ^ n = x ^ (n % Fintype.card G) :=
  by 
    rw [zpow_eq_mod_order_of, ←Int.mod_mod_of_dvd n (Int.coe_nat_dvd.2 order_of_dvd_card_univ), ←zpow_eq_mod_order_of]

-- error in GroupTheory.OrderOfElement: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `gcd(|G|,n)=1` then the `n`th power map is a bijection -/
@[simps #[]]
def pow_coprime (h : nat.coprime (fintype.card G) n) : «expr ≃ »(G, G) :=
{ to_fun := λ g, «expr ^ »(g, n),
  inv_fun := λ g, «expr ^ »(g, nat.gcd_b (fintype.card G) n),
  left_inv := λ
  g, by { have [ident key] [":", expr «expr = »(«expr ^ »(g, _), «expr ^ »(g, _))] [":=", expr congr_arg (λ
      n : exprℤ(), «expr ^ »(g, n)) (nat.gcd_eq_gcd_ab (fintype.card G) n)],
    rwa ["[", expr zpow_add, ",", expr zpow_mul, ",", expr zpow_mul, ",", expr zpow_coe_nat, ",", expr zpow_coe_nat, ",", expr zpow_coe_nat, ",", expr h.gcd_eq_one, ",", expr pow_one, ",", expr pow_card_eq_one, ",", expr one_zpow, ",", expr one_mul, ",", expr eq_comm, "]"] ["at", ident key] },
  right_inv := λ
  g, by { have [ident key] [":", expr «expr = »(«expr ^ »(g, _), «expr ^ »(g, _))] [":=", expr congr_arg (λ
      n : exprℤ(), «expr ^ »(g, n)) (nat.gcd_eq_gcd_ab (fintype.card G) n)],
    rwa ["[", expr zpow_add, ",", expr zpow_mul, ",", expr zpow_mul', ",", expr zpow_coe_nat, ",", expr zpow_coe_nat, ",", expr zpow_coe_nat, ",", expr h.gcd_eq_one, ",", expr pow_one, ",", expr pow_card_eq_one, ",", expr one_zpow, ",", expr one_mul, ",", expr eq_comm, "]"] ["at", ident key] } }

@[simp]
theorem pow_coprime_one (h : Nat.Coprime (Fintype.card G) n) : powCoprime h 1 = 1 :=
  one_pow n

@[simp]
theorem pow_coprime_inv (h : Nat.Coprime (Fintype.card G) n) {g : G} : powCoprime h (g⁻¹) = powCoprime h g⁻¹ :=
  inv_pow g n

theorem inf_eq_bot_of_coprime {G : Type _} [Groupₓ G] {H K : Subgroup G} [Fintype H] [Fintype K]
  (h : Nat.Coprime (Fintype.card H) (Fintype.card K)) : H⊓K = ⊥ :=
  by 
    refine' (H⊓K).eq_bot_iff_forall.mpr fun x hx => _ 
    rw [←order_of_eq_one_iff, ←Nat.dvd_one, ←h.gcd_eq_one, Nat.dvd_gcd_iffₓ]
    exact
      ⟨(congr_argₓ (· ∣ Fintype.card H) (order_of_subgroup ⟨x, hx.1⟩)).mpr order_of_dvd_card_univ,
        (congr_argₓ (· ∣ Fintype.card K) (order_of_subgroup ⟨x, hx.2⟩)).mpr order_of_dvd_card_univ⟩

variable(a)

theorem image_range_add_order_of [DecidableEq A] :
  Finset.image (fun i => i • a) (Finset.range (addOrderOf a)) = (AddSubgroup.zmultiples a : Set A).toFinset :=
  by 
    ext x 
    rw [Set.mem_to_finset, SetLike.mem_coe, mem_zmultiples_iff_mem_range_add_order_of]

/-- TODO: Generalise to `submonoid.powers`.-/
@[toAdditive image_range_add_order_of]
theorem image_range_order_of [DecidableEq G] :
  Finset.image (fun i => x ^ i) (Finset.range (orderOf x)) = (zpowers x : Set G).toFinset :=
  by 
    ext x 
    rw [Set.mem_to_finset, SetLike.mem_coe, mem_zpowers_iff_mem_range_order_of]

/-- TODO: Generalise to `finite_cancel_monoid`. -/
@[toAdditive gcd_nsmul_card_eq_zero_iff]
theorem pow_gcd_card_eq_one_iff : x ^ n = 1 ↔ x ^ gcd n (Fintype.card G) = 1 :=
  ⟨fun h => pow_gcd_eq_one _ h$ pow_card_eq_one,
    fun h =>
      let ⟨m, hm⟩ := gcd_dvd_left n (Fintype.card G)
      by 
        rw [hm, pow_mulₓ, h, one_pow]⟩

end FiniteGroup

end Fintype

section PowIsSubgroup

/-- A nonempty idempotent subset of a finite cancellative monoid is a submonoid -/
def submonoidOfIdempotent {M : Type _} [LeftCancelMonoid M] [Fintype M] (S : Set M) (hS1 : S.nonempty)
  (hS2 : (S*S) = S) : Submonoid M :=
  have pow_mem : ∀ a : M, a ∈ S → ∀ n : ℕ, (a ^ n+1) ∈ S :=
    fun a ha =>
      Nat.rec
        (by 
          rwa [zero_addₓ, pow_oneₓ])
        fun n ih => (congr_arg2 (· ∈ ·) (pow_succₓ a (n+1)).symm hS2).mp (Set.mul_mem_mul ha ih)
  { Carrier := S,
    one_mem' :=
      by 
        obtain ⟨a, ha⟩ := hS1 
        rw [←pow_order_of_eq_one a, ←tsub_add_cancel_of_le (succ_le_of_lt (order_of_pos a))]
        exact pow_mem a ha (orderOf a - 1),
    mul_mem' := fun a b ha hb => (congr_arg2 (· ∈ ·) rfl hS2).mp (Set.mul_mem_mul ha hb) }

/-- A nonempty idempotent subset of a finite group is a subgroup -/
def subgroupOfIdempotent {G : Type _} [Groupₓ G] [Fintype G] (S : Set G) (hS1 : S.nonempty) (hS2 : (S*S) = S) :
  Subgroup G :=
  { submonoidOfIdempotent S hS1 hS2 with Carrier := S,
    inv_mem' :=
      fun a ha =>
        by 
          rw [←one_mulₓ (a⁻¹), ←pow_oneₓ a, ←pow_order_of_eq_one a, ←pow_sub a (order_of_pos a)]
          exact (submonoidOfIdempotent S hS1 hS2).pow_mem ha (orderOf a - 1) }

/-- If `S` is a nonempty subset of a finite group `G`, then `S ^ |G|` is a subgroup -/
def powCardSubgroup {G : Type _} [Groupₓ G] [Fintype G] (S : Set G) (hS : S.nonempty) : Subgroup G :=
  have one_mem : (1 : G) ∈ S ^ Fintype.card G :=
    by 
      obtain ⟨a, ha⟩ := hS 
      rw [←pow_card_eq_one]
      exact Set.pow_mem_pow ha (Fintype.card G)
  subgroupOfIdempotent (S ^ Fintype.card G) ⟨1, one_mem⟩
    (by 
      classical 
      refine'
        (Set.eq_of_subset_of_card_le (fun b hb => (congr_argₓ (· ∈ _) (one_mulₓ b)).mp (Set.mul_mem_mul one_mem hb))
            (ge_of_eq _)).symm
          
      change _ = Fintype.card (_*_ : Set G)
      rw [←pow_addₓ, Groupₓ.card_pow_eq_card_pow_card_univ S (Fintype.card G) le_rfl,
        Groupₓ.card_pow_eq_card_pow_card_univ S (Fintype.card G+Fintype.card G) le_add_self])

end PowIsSubgroup

