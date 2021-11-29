import Mathbin.GroupTheory.OrderOfElement 
import Mathbin.Algebra.PunitInstances 
import Mathbin.Algebra.GcdMonoid.Finset 
import Mathbin.RingTheory.Int.Basic

/-!
# Exponent of a group

This file defines the exponent of a group, or more generally a monoid. For a group `G` it is defined
to be the minimal `n≥1` such that `g ^ n = 1` for all `g ∈ G`. For a finite group `G` it is equal to
the lowest common multiple of the order of all elements of the group `G`.

## Main definitions

* `monoid.exponent_exists` is a predicate on a monoid `G` saying that there is some positive `n`
  such that `g ^ n = 1` for all `g ∈ G`.
* `monoid.exponent` defines the exponent of a monoid `G` as the minimal positive `n` such that
  `g ^ n = 1` for all `g ∈ G`, by convention it is `0` if no such `n` exists.
* `add_monoid.exponent_exists` the additive version of `monoid.exponent_exists`.
* `add_monoid.exponent` the additive version of `monoid.exponent`.

## Main results

* `lcm_order_eq_exponent`: For a finite group `G`, the exponent is equal to the `lcm` of the order
  of its elements.

## TODO
* Compute the exponent of cyclic groups.
* Refactor the characteristic of a ring to be the exponent of its underlying additive group.
-/


universe u

variable (G : Type u) [Monoidₓ G]

open_locale Classical

namespace Monoidₓ

/--A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[toAdditive
      "A predicate on an additive monoid saying that there is a positive integer `n` such\n  that `n • g = 0` for all `g`."]
def exponent_exists :=
  ∃ n, 0 < n ∧ ∀ g : G, (g^n) = 1

/--The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
  `g ∈ G` if it exists, otherwise it is zero by convention.-/
@[toAdditive
      "The exponent of an additive group is the smallest positive integer `n` such that\n  `n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention."]
noncomputable def exponent :=
  if h : exponent_exists G then Nat.findₓ h else 0

@[toAdditive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : (g^exponent G) = 1 :=
  by 
    byCases' exponent_exists G
    ·
      simpRw [exponent, dif_pos h]
      exact (Nat.find_specₓ h).2 g
    ·
      simpRw [exponent, dif_neg h, pow_zeroₓ]

@[toAdditive nsmul_eq_mod_exponent]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : (g^n) = (g^n % exponent G) :=
  calc (g^n) = (g^(n % exponent G)+exponent G*n / exponent G) :=
    by 
      rw [Nat.mod_add_divₓ]
    _ = (g^n % exponent G) :=
    by 
      simp [pow_addₓ, pow_mulₓ, pow_exponent_eq_one]
    

-- error in GroupTheory.Exponent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem exponent_pos_of_exists
(n : exprℕ())
(hpos : «expr < »(0, n))
(hG : ∀ g : G, «expr = »(«expr ^ »(g, n), 1)) : «expr < »(0, exponent G) :=
begin
  have [ident h] [":", expr «expr∃ , »((n), «expr ∧ »(«expr < »(0, n), ∀
     g : G, «expr = »(«expr ^ »(g, n), 1)))] [":=", expr ⟨n, hpos, hG⟩],
  rw ["[", expr exponent, ",", expr dif_pos, "]"] [],
  exact [expr (nat.find_spec h).1]
end

@[toAdditive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, (g^n) = 1) : exponent G ≤ n :=
  by 
    rw [exponent, dif_pos]
    ·
      apply Nat.find_min'ₓ 
      exact ⟨hpos, hG⟩
    ·
      exact ⟨n, hpos, hG⟩

-- error in GroupTheory.Exponent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem exponent_min
(m : exprℕ())
(hpos : «expr < »(0, m))
(hm : «expr < »(m, exponent G)) : «expr∃ , »((g : G), «expr ≠ »(«expr ^ »(g, m), 1)) :=
begin
  by_contradiction [],
  push_neg ["at", ident h],
  have [ident hcon] [":", expr «expr ≤ »(exponent G, m)] [":=", expr exponent_min' G m hpos h],
  linarith [] [] []
end

@[simp, toAdditive]
theorem exp_eq_one_of_subsingleton [Subsingleton G] : exponent G = 1 :=
  by 
    apply le_antisymmₓ
    ·
      apply exponent_min' _ _ Nat.one_posₓ 
      simp 
    ·
      apply Nat.succ_le_of_ltₓ 
      apply exponent_pos_of_exists _ 1 Nat.one_posₓ 
      simp 

@[toAdditive add_order_dvd_exponent]
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  order_of_dvd_of_pow_eq_one (pow_exponent_eq_one G g)

-- error in GroupTheory.Exponent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem exponent_dvd_of_forall_pow_eq_one
(n : exprℕ())
(hpos : «expr < »(0, n))
(hG : ∀ g : G, «expr = »(«expr ^ »(g, n), 1)) : «expr ∣ »(exponent G, n) :=
begin
  apply [expr nat.dvd_of_mod_eq_zero],
  by_contradiction [ident h],
  have [ident h₁] [] [":=", expr nat.pos_of_ne_zero h],
  have [ident h₂] [":", expr «expr < »(«expr % »(n, exponent G), exponent G)] [":=", expr nat.mod_lt _ (exponent_pos_of_exists _ n hpos hG)],
  have [ident h₃] [":", expr «expr ≤ »(exponent G, «expr % »(n, exponent G))] [],
  { apply [expr exponent_min' _ _ h₁],
    simp_rw ["<-", expr pow_eq_mod_exponent] [],
    exact [expr hG] },
  linarith [] [] []
end

variable [Fintype G]

@[toAdditive lcm_add_order_of_dvd_exponent]
theorem lcm_order_of_dvd_exponent : (Finset.univ : Finset G).lcm orderOf ∣ exponent G :=
  by 
    apply Finset.lcm_dvd 
    intro g hg 
    exact order_dvd_exponent G g

-- error in GroupTheory.Exponent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[ident lcm_add_order_eq_exponent]]
theorem lcm_order_eq_exponent
{H : Type u}
[fintype H]
[left_cancel_monoid H] : «expr = »((finset.univ : finset H).lcm order_of, exponent H) :=
begin
  apply [expr nat.dvd_antisymm (lcm_order_of_dvd_exponent H)],
  apply [expr exponent_dvd_of_forall_pow_eq_one],
  { apply [expr nat.pos_of_ne_zero],
    by_contradiction [],
    rw [expr finset.lcm_eq_zero_iff] ["at", ident h],
    cases [expr h] ["with", ident g, ident hg],
    simp [] [] ["only"] ["[", expr true_and, ",", expr set.mem_univ, ",", expr finset.coe_univ, "]"] [] ["at", ident hg],
    exact [expr ne_of_gt (order_of_pos g) hg] },
  { intro [ident g],
    have [ident h] [":", expr «expr ∣ »(order_of g, (finset.univ : finset H).lcm order_of)] [],
    { apply [expr finset.dvd_lcm],
      exact [expr finset.mem_univ g] },
    cases [expr h] ["with", ident m, ident hm],
    rw ["[", expr hm, ",", expr pow_mul, ",", expr pow_order_of_eq_one, ",", expr one_pow, "]"] [] }
end

end Monoidₓ

