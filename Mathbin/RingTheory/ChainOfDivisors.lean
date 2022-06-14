/-
Copyright (c) 2021 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.Algebra.Squarefree

/-!

# Chains of divisors

The results in this file show that in the monoid `associates M` of a `unique_factorization_monoid`
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, meaning that we can find a strictly increasing bijection between `fin (n + 1)`
and the set of factors of `a`.

## Main results
- `divisor_chain.exists_chain_of_prime_pow` : existence of a chain for prime powers.
- `divisor_chain.is_prime_pow_of_has_chain` : elements that have a chain are prime powers.
- `multiplicity_prime_le_multiplicity_image_by_factor_order_iso` : if there is a
  monotone bijection `d` between the set of factors of `a : associates M` and the set of factors of
  `b : associates N`, then, for any prime `p ∣ a`, `multiplicity p a ≤ multiplicity (d p) b`.

## Todo
- Show that under the assumptions of `multiplicity_prime_le_multiplicity_image_by_factor_order_iso`,
  `d p` is prime whenever `p` is prime. Applying
  `multiplicity_prime_le_multiplicity_image_by_factor_order_iso` on `d.symm` then gives us
  `multiplicity p a = multiplicity (d p) b`.
- Create a structure for chains of divisors.

-/


variable {M : Type _} [CancelCommMonoidWithZero M]

open UniqueFactorizationMonoid multiplicity Irreducible

namespace DivisorChain

theorem exists_chain_of_prime_pow {p : Associates M} {n : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    ∃ c : Finₓ (n + 1) → Associates M, c 1 = p ∧ StrictMono c ∧ ∀ {r : Associates M}, r ≤ p ^ n ↔ ∃ i, r = c i := by
  refine' ⟨fun i => p ^ (i : ℕ), _, fun n m h => _, fun y => ⟨fun h => _, _⟩⟩
  · rw [Finₓ.coe_one', Nat.mod_eq_of_ltₓ, pow_oneₓ]
    exact Nat.lt_succ_of_leₓ (nat.one_le_iff_ne_zero.mpr hn)
    
  · exact
      associates.dvd_not_unit_iff_lt.mp
        ⟨pow_ne_zero n hp.ne_zero, p ^ (m - n : ℕ),
          not_is_unit_of_not_is_unit_dvd hp.not_unit (dvd_pow dvd_rfl (Nat.sub_pos_of_ltₓ h).ne'),
          (pow_mul_pow_sub p h.le).symm⟩
    
  · obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h
    rw [associated_iff_eq] at hi
    exact ⟨⟨i, Nat.lt_succ_of_leₓ i_le⟩, hi⟩
    
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ (n - i : ℕ), (pow_mul_pow_sub p (nat.succ_le_succ_iff.mp i.2)).symm⟩
    

theorem element_of_chain_not_is_unit_of_index_ne_zero {n : ℕ} {i : Finₓ (n + 1)} (i_pos : i ≠ 0)
    {c : Finₓ (n + 1) → Associates M} (h₁ : StrictMono c) : ¬IsUnit (c i) :=
  DvdNotUnit.not_unit
    (Associates.dvd_not_unit_iff_lt.2 (h₁ <| show (0 : Finₓ (n + 1)) < i from i.pos_iff_ne_zero.mpr i_pos))

theorem first_of_chain_is_unit {q : Associates M} {n : ℕ} {c : Finₓ (n + 1) → Associates M} (h₁ : StrictMono c)
    (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) : IsUnit (c 0) := by
  obtain ⟨i, hr⟩ := h₂.mp Associates.one_le
  rw [Associates.is_unit_iff_eq_one, ← Associates.le_one_iff, hr]
  exact h₁.monotone (Finₓ.zero_le i)

/-- The second element of a chain is irreducible. -/
theorem second_of_chain_is_irreducible {q : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : Irreducible (c 1) := by
  cases n
  · contradiction
    
  refine' (Associates.is_atom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨_, fun b hb => _⟩
  · exact ne_bot_of_gt (h₁ (show (0 : Finₓ (n + 2)) < 1 from Finₓ.one_pos))
    
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩))
  cases i
  · exact (Associates.is_unit_iff_eq_one _).mp (first_of_chain_is_unit h₁ @h₂)
    
  · simpa [Finₓ.lt_iff_coe_lt_coe] using h₁.lt_iff_lt.mp hb
    

theorem eq_second_of_chain_of_prime_dvd {p q r : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hp : Prime p) (hr : r ∣ q) (hp' : p ∣ r) :
    p = c 1 := by
  cases n
  · contradiction
    
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr)
  refine' congr_arg c ((eq_of_ge_of_not_gt _) fun hi => _)
  · rw [Finₓ.le_iff_coe_le_coe, Finₓ.coe_one, Nat.succ_le_iff, ← Finₓ.coe_zero, ← Finₓ.lt_iff_coe_lt_coe,
      Finₓ.pos_iff_ne_zero]
    rintro rfl
    exact hp.not_unit (first_of_chain_is_unit h₁ @h₂)
    
  obtain rfl | ⟨j, rfl⟩ := i.eq_zero_or_eq_succ
  · cases hi
    
  refine'
    not_irreducible_of_not_unit_dvd_not_unit
      (DvdNotUnit.not_unit (Associates.dvd_not_unit_iff_lt.2 (h₁ (show (0 : Finₓ (n + 2)) < j from _)))) _
      hp.irreducible
  · simpa [← Finₓ.succ_zero_eq_one, Finₓ.succ_lt_succ_iff] using hi
    
  · refine' Associates.dvd_not_unit_iff_lt.2 (h₁ _)
    simpa only [Finₓ.coe_eq_cast_succ] using Finₓ.lt_succ
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem card_subset_divisors_le_length_of_chain {q : Associates M} {n : ℕ} {c : Finₓ (n + 1) → Associates M}
    (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) {m : Finset (Associates M)} (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 := by
  classical
  have mem_image : ∀ r : Associates M, r ≤ q → r ∈ finset.univ.image c := by
    intro r hr
    obtain ⟨i, hi⟩ := h₂.1 hr
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi.symm⟩
  rw [← Finset.card_fin (n + 1)]
  exact (Finset.card_le_of_subset fun x hx => mem_image x <| hm x hx).trans Finset.card_image_le

variable [UniqueFactorizationMonoid M]

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem element_of_chain_eq_pow_second_of_chain {q r : Associates M} {n : ℕ} (hn : n ≠ 0)
    {c : Finₓ (n + 1) → Associates M} (h₁ : StrictMono c) (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) (hr : r ∣ q) (hq : q ≠ 0) :
    ∃ i : Finₓ (n + 1), r = c 1 ^ (i : ℕ) := by
  classical
  let i := (normalized_factors r).card
  have hi : normalized_factors r = Multiset.repeat (c 1) i := by
    apply Multiset.eq_repeat_of_mem
    intro b hb
    refine'
      eq_second_of_chain_of_prime_dvd hn h₁ (fun r' => h₂) (prime_of_normalized_factor b hb) hr
        (dvd_of_mem_normalized_factors hb)
  have H : r = c 1 ^ i := by
    have := UniqueFactorizationMonoid.normalized_factors_prod (ne_zero_of_dvd_ne_zero hq hr)
    rw [associated_iff_eq, hi, Multiset.prod_repeat] at this
    rw [this]
  refine' ⟨⟨i, _⟩, H⟩
  have : (finset.univ.image fun m : Finₓ (i + 1) => c 1 ^ (m : ℕ)).card = i + 1 := by
    conv_rhs => rw [← Finset.card_fin (i + 1)]
    cases n
    · contradiction
      
    rw [Finset.card_image_iff]
    refine' Set.inj_on_of_injective (fun m m' h => Finₓ.ext _) _
    refine'
      pow_injective_of_not_unit
        (element_of_chain_not_is_unit_of_index_ne_zero
          (by
            simp )
          h₁)
        _ h
    exact Irreducible.ne_zero (second_of_chain_is_irreducible hn h₁ (@h₂) hq)
  suffices H' : ∀, ∀ r ∈ finset.univ.image fun m : Finₓ (i + 1) => c 1 ^ (m : ℕ), ∀, r ≤ q
  · simp only [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← this]
    apply card_subset_divisors_le_length_of_chain (@h₂) H'
    
  simp only [Finset.mem_image]
  rintro r ⟨a, ha, rfl⟩
  refine' dvd_trans _ hr
  use c 1 ^ (i - a)
  rw [pow_mul_pow_sub (c 1)]
  · exact H
    
  · exact nat.succ_le_succ_iff.mp a.2
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem eq_pow_second_of_chain_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : q = c 1 ^ n := by
  classical
  obtain ⟨i, hi'⟩ := element_of_chain_eq_pow_second_of_chain hn h₁ (fun r => h₂) (dvd_refl q) hq
  convert hi'
  refine' (Nat.lt_succ_iffₓ.1 i.prop).antisymm' (Nat.le_of_succ_le_succₓ _)
  calc n + 1 = (Finset.univ : Finset (Finₓ (n + 1))).card := (Finset.card_fin _).symm _ = (finset.univ.image c).card :=
      (finset.card_image_iff.mpr
          (h₁.injective.inj_on _)).symm _ ≤ (finset.univ.image fun m : Finₓ (i + 1) => c 1 ^ (m : ℕ)).card :=
      Finset.card_le_of_subset _ _ ≤ (Finset.univ : Finset (Finₓ (i + 1))).card := Finset.card_image_le _ = i + 1 :=
      Finset.card_fin _
  intro r hr
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hr
  have := h₂.2 ⟨j, rfl⟩
  rw [hi'] at this
  obtain ⟨u, hu, hu'⟩ := (dvd_prime_pow (show Prime (c 1) from _) i).1 this
  refine' finset.mem_image.mpr ⟨u, Finset.mem_univ _, _⟩
  · rw [associated_iff_eq] at hu'
    rw [Finₓ.coe_coe_of_lt (Nat.lt_succ_of_leₓ hu), hu']
    
  · rw [← irreducible_iff_prime]
    exact second_of_chain_is_irreducible hn h₁ (@h₂) hq
    

theorem is_prime_pow_of_has_chain {q : Associates M} {n : ℕ} (hn : n ≠ 0) {c : Finₓ (n + 1) → Associates M}
    (h₁ : StrictMono c) (h₂ : ∀ {r : Associates M}, r ≤ q ↔ ∃ i, r = c i) (hq : q ≠ 0) : IsPrimePow q :=
  ⟨c 1, n, irreducible_iff_prime.mp (second_of_chain_is_irreducible hn h₁ (@h₂) hq), zero_lt_iff.mpr hn,
    (eq_pow_second_of_chain_of_has_chain hn h₁ (@h₂) hq).symm⟩

end DivisorChain

variable {N : Type _} [CancelCommMonoidWithZero N] [UniqueFactorizationMonoid N] [DecidableEq (Associates M)]
  [UniqueFactorizationMonoid M]

open DivisorChain

theorem pow_image_of_prime_by_factor_order_iso_dvd {m p : Associates M} {n : Associates N} (hn : n ≠ 0)
    (hp : p ∈ normalizedFactors m) (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) {s : ℕ}
    (hs' : p ^ s ≤ m) : (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : Associates N) ^ s ≤ n := by
  by_cases' hs : s = 0
  · simp [hs]
    
  suffices (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : Associates N) ^ s = ↑(d ⟨p ^ s, hs'⟩) by
    rw [this]
    apply Subtype.prop (d ⟨p ^ s, hs'⟩)
  obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := exists_chain_of_prime_pow hs (prime_of_normalized_factor p hp)
  set c₂ : Finₓ (s + 1) → Associates N := fun t =>
    d
      ⟨c₁ t,
        le_transₓ
          (hc₁''.2
            ⟨t, by
              simp ⟩)
          hs'⟩
  have c₂.def : ∀ t, c₂ t = d ⟨c₁ t, _⟩ := fun t => rfl
  refine' (congr_arg (· ^ s) (c₂.def 1).symm).trans _
  refine' (eq_pow_second_of_chain_of_has_chain hs (fun t u h => _) (fun r => ⟨fun hr => _, _⟩) _).symm
  · rw [c₂.def, c₂.def, Subtype.coe_lt_coe, d.lt_iff_lt, Subtype.mk_lt_mk, hc₁'.lt_iff_lt]
    exact h
    
  · have : r ≤ n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2
    suffices d.symm ⟨r, this⟩ ≤ ⟨c₁ 1 ^ s, hs'⟩ by
      obtain ⟨i, hi⟩ := hc₁''.1 this
      use i
      simp only [c₂.def, ← hi, d.apply_symm_apply, Subtype.coe_eta, Subtype.coe_mk]
    conv_rhs => rw [← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩]
    rw [d.symm.le_iff_le]
    simpa only [← Subtype.coe_le_coe, Subtype.coe_mk] using hr
    
  · rintro ⟨i, hr⟩
    rw [hr, c₂.def, Subtype.coe_le_coe, d.le_iff_le]
    simpa [Subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩
    
  exact ne_zero_of_dvd_ne_zero hn (Subtype.prop (d ⟨c₁ 1 ^ s, _⟩))

variable [DecidableRel ((· ∣ ·) : Associates M → Associates M → Prop)]
  [DecidableRel ((· ∣ ·) : Associates N → Associates N → Prop)]

theorem multiplicity_prime_le_multiplicity_image_by_factor_order_iso {m p : Associates M} {n : Associates N}
    (hp : p ∈ normalizedFactors m) (d : { l : Associates M // l ≤ m } ≃o { l : Associates N // l ≤ n }) :
    multiplicity p m ≤ multiplicity (↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩)) n := by
  by_cases' hn : n = 0
  · simp [hn]
    
  by_cases' hm : m = 0
  · simpa [hm] using hp
    
  rw [← Enat.coe_get (finite_iff_dom.1 <| finite_prime_left (prime_of_normalized_factor p hp) hm), ←
    pow_dvd_iff_le_multiplicity]
  exact pow_image_of_prime_by_factor_order_iso_dvd hn hp d (pow_multiplicity_dvd _)

