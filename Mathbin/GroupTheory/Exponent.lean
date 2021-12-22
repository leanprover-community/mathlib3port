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

/-- A predicate on a monoid saying that there is a positive integer `n` such that `g ^ n = 1`
  for all `g`.-/
@[to_additive
      "A predicate on an additive monoid saying that there is a positive integer `n` such\n  that `n • g = 0` for all `g`."]
def exponent_exists :=
  ∃ n, 0 < n ∧ ∀ g : G, (g^n) = 1

/-- The exponent of a group is the smallest positive integer `n` such that `g ^ n = 1` for all
  `g ∈ G` if it exists, otherwise it is zero by convention.-/
@[to_additive
      "The exponent of an additive group is the smallest positive integer `n` such that\n  `n • g = 0` for all `g ∈ G` if it exists, otherwise it is zero by convention."]
noncomputable def exponent :=
  if h : exponent_exists G then Nat.findₓ h else 0

@[to_additive exponent_nsmul_eq_zero]
theorem pow_exponent_eq_one (g : G) : (g^exponent G) = 1 := by
  by_cases' exponent_exists G
  ·
    simp_rw [exponent, dif_pos h]
    exact (Nat.find_specₓ h).2 g
  ·
    simp_rw [exponent, dif_neg h, pow_zeroₓ]

@[to_additive nsmul_eq_mod_exponent]
theorem pow_eq_mod_exponent {n : ℕ} (g : G) : (g^n) = (g^n % exponent G) :=
  calc (g^n) = (g^(n % exponent G)+exponent G*n / exponent G) := by
    rw [Nat.mod_add_divₓ]
    _ = (g^n % exponent G) := by
    simp [pow_addₓ, pow_mulₓ, pow_exponent_eq_one]
    

@[to_additive]
theorem exponent_pos_of_exists (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, (g^n) = 1) : 0 < exponent G := by
  have h : ∃ n, 0 < n ∧ ∀ g : G, (g^n) = 1 := ⟨n, hpos, hG⟩
  rw [exponent, dif_pos]
  exact (Nat.find_specₓ h).1

@[to_additive]
theorem exponent_min' (n : ℕ) (hpos : 0 < n) (hG : ∀ g : G, (g^n) = 1) : exponent G ≤ n := by
  rw [exponent, dif_pos]
  ·
    apply Nat.find_min'ₓ
    exact ⟨hpos, hG⟩
  ·
    exact ⟨n, hpos, hG⟩

@[to_additive]
theorem exponent_min (m : ℕ) (hpos : 0 < m) (hm : m < exponent G) : ∃ g : G, (g^m) ≠ 1 := by
  by_contra
  push_neg  at h
  have hcon : exponent G ≤ m := exponent_min' G m hpos h
  linarith

@[simp, to_additive]
theorem exp_eq_one_of_subsingleton [Subsingleton G] : exponent G = 1 := by
  apply le_antisymmₓ
  ·
    apply exponent_min' _ _ Nat.one_posₓ
    simp
  ·
    apply Nat.succ_le_of_ltₓ
    apply exponent_pos_of_exists _ 1 Nat.one_posₓ
    simp

@[to_additive add_order_dvd_exponent]
theorem order_dvd_exponent (g : G) : orderOf g ∣ exponent G :=
  order_of_dvd_of_pow_eq_one (pow_exponent_eq_one G g)

@[to_additive]
theorem exponent_dvd_of_forall_pow_eq_one (n : ℕ) (hG : ∀ g : G, (g^n) = 1) : exponent G ∣ n := by
  by_cases' hpos : n = 0
  ·
    simp [hpos]
  apply Nat.dvd_of_mod_eq_zeroₓ
  by_contra h
  have h₁ := Nat.pos_of_ne_zeroₓ h
  have h₂ : n % exponent G < exponent G := Nat.mod_ltₓ _ (exponent_pos_of_exists _ n (Nat.pos_of_ne_zeroₓ hpos) hG)
  have h₃ : exponent G ≤ n % exponent G := by
    apply exponent_min' _ _ h₁
    simp_rw [← pow_eq_mod_exponent]
    exact hG
  linarith

variable [Fintype G]

@[to_additive lcm_add_order_of_dvd_exponent]
theorem lcm_order_of_dvd_exponent : (Finset.univ : Finset G).lcm orderOf ∣ exponent G := by
  apply Finset.lcm_dvd
  intro g hg
  exact order_dvd_exponent G g

@[to_additive lcm_add_order_eq_exponent]
theorem lcm_order_eq_exponent {H : Type u} [Fintype H] [LeftCancelMonoid H] :
    (Finset.univ : Finset H).lcm orderOf = exponent H := by
  apply Nat.dvd_antisymm (lcm_order_of_dvd_exponent H)
  apply exponent_dvd_of_forall_pow_eq_one
  intro g
  have h : orderOf g ∣ (Finset.univ : Finset H).lcm orderOf := by
    apply Finset.dvd_lcm
    exact Finset.mem_univ g
  cases' h with m hm
  rw [hm, pow_mulₓ, pow_order_of_eq_one, one_pow]

end Monoidₓ

