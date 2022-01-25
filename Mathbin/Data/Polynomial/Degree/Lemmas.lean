import Mathbin.Data.Polynomial.Eval
import Mathbin.Tactic.IntervalCases

/-!
# Theory of degrees of polynomials

Some of the main results include
- `nat_degree_comp_le` : The degree of the composition is at most the product of degrees

-/


noncomputable section

open_locale Classical

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q r : Polynomial R}

section Degree

theorem nat_degree_comp_le : nat_degree (p.comp q) ≤ nat_degree p * nat_degree q :=
  if h0 : p.comp q = 0 then by
    rw [h0, nat_degree_zero] <;> exact Nat.zero_leₓ _
  else
    WithBot.coe_le_coe.1 $
      calc
        ↑nat_degree (p.comp q) = degree (p.comp q) := (degree_eq_nat_degree h0).symm
        _ = _ := congr_argₓ degree comp_eq_sum_left
        _ ≤ _ := degree_sum_le _ _
        _ ≤ _ :=
          sup_le fun n hn =>
            calc
              degree (C (coeff p n) * q ^ n) ≤ degree (C (coeff p n)) + degree (q ^ n) := degree_mul_le _ _
              _ ≤ nat_degree (C (coeff p n)) + n • degree q := add_le_add degree_le_nat_degree (degree_pow_le _ _)
              _ ≤ nat_degree (C (coeff p n)) + n • nat_degree q :=
                add_le_add_left (nsmul_le_nsmul_of_le_right (@degree_le_nat_degree _ _ q) n) _
              _ = (n * nat_degree q : ℕ) := by
                rw [nat_degree_C, WithBot.coe_zero, zero_addₓ, ← WithBot.coe_nsmul, nsmul_eq_mul] <;> simp
              _ ≤ (nat_degree p * nat_degree q : ℕ) :=
                WithBot.coe_le_coe.2 $
                  mul_le_mul_of_nonneg_right (le_nat_degree_of_ne_zero (mem_support_iff.1 hn)) (Nat.zero_leₓ _)
              
        

theorem degree_pos_of_root {p : Polynomial R} (hp : p ≠ 0) (h : is_root p a) : 0 < degree p :=
  lt_of_not_geₓ $ fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [is_root, this, eval_C] at h
    simp only [h, RingHom.map_zero] at this
    exact hp this

theorem nat_degree_le_iff_coeff_eq_zero : p.nat_degree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [nat_degree_le_iff_degree_le, degree_le_iff_coeff_zero, WithBot.coe_lt_coe]

theorem nat_degree_C_mul_le (a : R) (f : Polynomial R) : (C a * f).natDegree ≤ f.nat_degree :=
  calc
    (C a * f).natDegree ≤ (C a).natDegree + f.nat_degree := nat_degree_mul_le
    _ = 0 + f.nat_degree := by
      rw [nat_degree_C a]
    _ = f.nat_degree := zero_addₓ _
    

theorem nat_degree_mul_C_le (f : Polynomial R) (a : R) : (f * C a).natDegree ≤ f.nat_degree :=
  calc
    (f * C a).natDegree ≤ f.nat_degree + (C a).natDegree := nat_degree_mul_le
    _ = f.nat_degree + 0 := by
      rw [nat_degree_C a]
    _ = f.nat_degree := add_zeroₓ _
    

theorem eq_nat_degree_of_le_mem_support (pn : p.nat_degree ≤ n) (ns : n ∈ p.support) : p.nat_degree = n :=
  le_antisymmₓ pn (le_nat_degree_of_mem_supp _ ns)

theorem nat_degree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) : (C a * p).natDegree = p.nat_degree :=
  le_antisymmₓ (nat_degree_C_mul_le a p)
    (calc
      p.nat_degree = (1 * p).natDegree := by
        nth_rw 0[← one_mulₓ p]
      _ = (C ai * (C a * p)).natDegree := by
        rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (C a * p).natDegree := nat_degree_C_mul_le ai (C a * p)
      )

theorem nat_degree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) : (p * C a).natDegree = p.nat_degree :=
  le_antisymmₓ (nat_degree_mul_C_le p a)
    (calc
      p.nat_degree = (p * 1).natDegree := by
        nth_rw 0[← mul_oneₓ p]
      _ = (p * C a * C ai).natDegree := by
        rw [← C_1, ← au, RingHom.map_mul, ← mul_assoc]
      _ ≤ (p * C a).natDegree := nat_degree_mul_C_le (p * C a) ai
      )

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
Lemma `nat_degree_mul_C_eq_of_no_zero_divisors` below separates cases, in order to overcome this
hurdle.
-/
theorem nat_degree_mul_C_eq_of_mul_ne_zero (h : p.leading_coeff * a ≠ 0) : (p * C a).natDegree = p.nat_degree := by
  refine' eq_nat_degree_of_le_mem_support (nat_degree_mul_C_le p a) _
  refine' mem_support_iff.mpr _
  rwa [coeff_mul_C]

/-- Although not explicitly stated, the assumptions of lemma `nat_degree_C_mul_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leading_coeff ≠ 0`.
Lemma `nat_degree_C_mul_eq_of_no_zero_divisors` below separates cases, in order to overcome this
hurdle.
-/
theorem nat_degree_C_mul_eq_of_mul_ne_zero (h : a * p.leading_coeff ≠ 0) : (C a * p).natDegree = p.nat_degree := by
  refine' eq_nat_degree_of_le_mem_support (nat_degree_C_mul_le a p) _
  refine' mem_support_iff.mpr _
  rwa [coeff_C_mul]

theorem nat_degree_add_coeff_mul (f g : Polynomial R) :
    (f * g).coeff (f.nat_degree + g.nat_degree) = f.coeff f.nat_degree * g.coeff g.nat_degree := by
  simp only [coeff_nat_degree, coeff_mul_degree_add_degree]

theorem nat_degree_lt_coeff_mul (h : p.nat_degree + q.nat_degree < m + n) : (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_nat_degree_lt (nat_degree_mul_le.trans_lt h)

theorem degree_sum_eq_of_disjoint (f : S → Polynomial R) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on degree ∘ f)) : degree (s.sum f) = s.sup fun i => degree (f i) := by
  induction' s using Finset.induction_on with x s hx IH
  · simp
    
  · simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    specialize
      IH
        (h.mono fun _ => by
          simp (config := { contextual := true }))
    rcases lt_trichotomyₓ (degree (f x)) (degree (s.sum f)) with (H | H | H)
    · rw [← IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H]
      
    · rcases s.eq_empty_or_nonempty with (rfl | hs)
      · simp
        
      obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup s hs fun i => degree (f i)
      rw [IH, hy'] at H
      by_cases' hx0 : f x = 0
      · simp [hx0, IH]
        
      have hy0 : f y ≠ 0 := by
        contrapose! H
        simpa [H, degree_eq_bot] using hx0
      refine' absurd H (h _ _ fun H => hx _)
      · simp [hx0]
        
      · simp [hy, hy0]
        
      · exact H.symm ▸ hy
        
      
    · rw [← IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H]
      
    

theorem nat_degree_sum_eq_of_disjoint (f : S → Polynomial R) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on nat_degree ∘ f)) :
    nat_degree (s.sum f) = s.sup fun i => nat_degree (f i) := by
  by_cases' H : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.nonempty := ⟨x, hx⟩
    refine' nat_degree_eq_of_degree_eq_some _
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, Finset.coe_sup', ← Finset.sup'_eq_sup hs]
      refine' le_antisymmₓ _ _
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases' hb' : f b = 0
        · simpa [hb'] using hs
          
        rw [degree_eq_nat_degree hb']
        exact Finset.le_sup' _ hb
        
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [Finset.le_sup'_iff, exists_prop, Function.comp_app]
        by_cases' hb' : f b = 0
        · refine' ⟨x, hx, _⟩
          contrapose! hx'
          simpa [hb', degree_eq_bot] using hx'
          
        exact ⟨b, hb, (degree_eq_nat_degree hb').Ge⟩
        
      
    · exact h.imp fun x y hxy hxy' => hxy (nat_degree_eq_of_degree_eq hxy')
      
    
  · push_neg  at H
    rw [Finset.sum_eq_zero H, nat_degree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [H x hx]
    

variable [Semiringₓ S]

theorem nat_degree_pos_of_eval₂_root {p : Polynomial R} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) : 0 < nat_degree p :=
  lt_of_not_geₓ $ fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_nat_degree_le_zero hlt
    rw [A, eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, RingHom.map_zero] at A
    exact hp A

theorem degree_pos_of_eval₂_root {p : Polynomial R} (hp : p ≠ 0) (f : R →+* S) {z : S} (hz : eval₂ f z p = 0)
    (inj : ∀ x : R, f x = 0 → x = 0) : 0 < degree p :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_eval₂_root hp f hz inj)

@[simp]
theorem coe_lt_degree {p : Polynomial R} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < nat_degree p := by
  by_cases' h : p = 0
  · simp [h]
    
  rw [degree_eq_nat_degree h, WithBot.coe_lt_coe]

end Degree

end Semiringₓ

section NoZeroDivisors

variable [Semiringₓ R] [NoZeroDivisors R] {p q : Polynomial R}

theorem nat_degree_mul_C_eq_of_no_zero_divisors (a0 : a ≠ 0) : (p * C a).natDegree = p.nat_degree := by
  by_cases' p0 : p = 0
  · rw [p0, zero_mul]
    
  · exact nat_degree_mul_C_eq_of_mul_ne_zero (mul_ne_zero (leading_coeff_ne_zero.mpr p0) a0)
    

theorem nat_degree_C_mul_eq_of_no_zero_divisors (a0 : a ≠ 0) : (C a * p).natDegree = p.nat_degree := by
  by_cases' p0 : p = 0
  · rw [p0, mul_zero]
    
  · exact nat_degree_C_mul_eq_of_mul_ne_zero (mul_ne_zero a0 (leading_coeff_ne_zero.mpr p0))
    

end NoZeroDivisors

end Polynomial

