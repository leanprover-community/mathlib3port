/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.MonoidAlgebra.Support

/-!
# Variations on non-zero divisors in `add_monoid_algebra`s

This file studies the interaction between typeclass assumptions on two Types `R` and `A` and
whether `add_monoid_algebra R A` has non-zero zero-divisors.  For some background on related
questions, see [Kaplansky's Conjectures](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures),
especially the *zero divisor conjecture*.

_Conjecture._
Let `K` be a field, and `G` a torsion-free group. The group ring `K[G]` does not contain
nontrivial zero divisors, that is, it is a domain.

We formalize in this file the well-known result that if `R` is a field and `A` is a left-ordered
group, then `R[A]` contains no non-zero zero-divisors.  Some of these assumptions can be trivially
weakened: below we mention what assumptions are sufficient for the proofs in this file.

##  Main results

* `no_zero_divisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `add_monoid_algebra R A` has no non-zero zero-divisors.
* `no_zero_divisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `add_monoid_algebra R A` has no non-zero zero-divisors.

The conditions on `A` imposed in `no_zero_divisors.of_left_ordered` are sometimes referred to as
`left-ordered`.
The conditions on `A` imposed in `no_zero_divisors.of_right_ordered` are sometimes referred to as
`right-ordered`.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.
-/


namespace AddMonoidAlgebra

open Finsupp

variable {R A : Type _} [Semiringₓ R]

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_forall_ne [Add A] {f g : AddMonoidAlgebra R A} {a0 b0 : A}
    (h : ∀ {a b : A}, a ∈ f.Support → b ∈ g.Support → a ≠ a0 ∨ b ≠ b0 → a + b ≠ a0 + b0) :
    (f * g) (a0 + b0) = f a0 * g b0 := by
  classical
  rw [mul_apply]
  refine' (Finsetₓ.sum_eq_single a0 _ _).trans _
  · exact fun b H hb => Finsetₓ.sum_eq_zero fun x H1 => if_neg (h H H1 (Or.inl hb))
    
  · exact fun af0 => by simp [not_mem_support_iff.mp af0]
    
  · refine' (Finsetₓ.sum_eq_single b0 (fun b bg b0 => _) _).trans (if_pos rfl)
    · by_cases af:a0 ∈ f.support
      · exact if_neg (h af bg (Or.inr b0))
        
      · simp only [not_mem_support_iff.mp af, zero_mul, if_t_t]
        
      
    · exact fun bf0 => by simp [not_mem_support_iff.mp bf0]
      
    

section LeftOrRightOrderability

theorem Left.exists_add_of_mem_support_single_mul [AddLeftCancelSemigroup A] {g : AddMonoidAlgebra R A} (a x : A)
    (hx : x ∈ (single a 1 * g : AddMonoidAlgebra R A).Support) : ∃ b ∈ g.Support, a + b = x := by
  rwa [support_single_mul _ _ (fun y => by rw [one_mulₓ] : ∀ y : R, 1 * y = 0 ↔ _), Finsetₓ.mem_map] at hx

theorem Right.exists_add_of_mem_support_single_mul [AddRightCancelSemigroup A] {f : AddMonoidAlgebra R A} (b x : A)
    (hx : x ∈ (f * single b 1 : AddMonoidAlgebra R A).Support) : ∃ a ∈ f.Support, a + b = x := by
  rwa [support_mul_single _ _ (fun y => by rw [mul_oneₓ] : ∀ y : R, y * 1 = 0 ↔ _), Finsetₓ.mem_map] at hx

/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a left-ordered add right
cancel semigroup, then `add_monoid_algebra R A` also contains no non-zero zero-divisors. -/
theorem NoZeroDivisors.of_left_ordered [NoZeroDivisors R] [AddRightCancelSemigroup A] [LinearOrderₓ A]
    [CovariantClass A A (· + ·) (· < ·)] : NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨fun f g fg => by
    contrapose! fg
    let gmin : A := g.support.min' (support_nonempty_iff.mpr fg.2)
    refine' support_nonempty_iff.mp _
    obtain ⟨a, ha, H⟩ :=
      right.exists_add_of_mem_support_single_mul gmin
        ((f * single gmin 1 : AddMonoidAlgebra R A).Support.min'
          (by rw [support_mul_single] <;> simp [support_nonempty_iff.mpr fg.1]))
        (Finsetₓ.min'_mem _ _)
    refine' ⟨a + gmin, mem_support_iff.mpr _⟩
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    · refine' mul_ne_zero _ _
      exacts[mem_support_iff.mp ha, mem_support_iff.mp (Finsetₓ.min'_mem _ _)]
      
    · rw [H]
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gtₓ _
      · refine' lt_of_lt_of_leₓ (_ : _ < b + gmin) _
        · apply Finsetₓ.min'_lt_of_mem_erase_min'
          rw [← H]
          apply Finsetₓ.mem_erase_of_ne_of_mem
          · simpa only [Ne.def, add_left_injₓ]
            
          · rw [support_mul_single _ _ (fun y => by rw [mul_oneₓ] : ∀ y : R, y * 1 = 0 ↔ _)]
            simpa only [Finsetₓ.mem_map, add_right_embedding_apply, add_left_injₓ, exists_propₓ, exists_eq_right]
            
          
        · haveI : CovariantClass A A (· + ·) (· ≤ ·) := Add.to_covariant_class_left A
          exact add_le_add_left (Finsetₓ.min'_le _ _ cg) _
          
        
      · refine' lt_of_le_of_ltₓ (_ : _ ≤ b + gmin) _
        · apply Finsetₓ.min'_le
          rw [support_mul_single _ _ (fun y => by rw [mul_oneₓ] : ∀ y : R, y * 1 = 0 ↔ _)]
          simp only [bf, Finsetₓ.mem_map, add_right_embedding_apply, add_left_injₓ, exists_propₓ, exists_eq_right]
          
        · refine' add_lt_add_left _ _
          exact Finsetₓ.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hc, cg⟩)
          
        
      ⟩

/-- If `R` is a semiring with no non-trivial zero-divisors and `A` is a right-ordered add left
cancel semigroup, then `add_monoid_algebra R A` also contains no non-zero zero-divisors. -/
theorem NoZeroDivisors.of_right_ordered [NoZeroDivisors R] [AddLeftCancelSemigroup A] [LinearOrderₓ A]
    [CovariantClass A A (Function.swap (· + ·)) (· < ·)] : NoZeroDivisors (AddMonoidAlgebra R A) :=
  ⟨fun f g fg => by
    contrapose! fg
    let fmin : A := f.support.min' (support_nonempty_iff.mpr fg.1)
    refine' support_nonempty_iff.mp _
    obtain ⟨a, ha, H⟩ :=
      left.exists_add_of_mem_support_single_mul fmin
        ((single fmin 1 * g : AddMonoidAlgebra R A).Support.min'
          (by rw [support_single_mul] <;> simp [support_nonempty_iff.mpr fg.2]))
        (Finsetₓ.min'_mem _ _)
    refine' ⟨fmin + a, mem_support_iff.mpr _⟩
    rw [mul_apply_add_eq_mul_of_forall_ne _]
    · refine' mul_ne_zero _ _
      exacts[mem_support_iff.mp (Finsetₓ.min'_mem _ _), mem_support_iff.mp ha]
      
    · rw [H]
      rintro b c bf cg (hb | hc) <;> refine' ne_of_gtₓ _
      · refine' lt_of_le_of_ltₓ (_ : _ ≤ fmin + c) _
        · apply Finsetₓ.min'_le
          rw [support_single_mul _ _ (fun y => by rw [one_mulₓ] : ∀ y : R, 1 * y = 0 ↔ _)]
          simp only [cg, Finsetₓ.mem_map, add_left_embedding_apply, add_right_injₓ, exists_propₓ, exists_eq_right]
          
        · refine' add_lt_add_right _ _
          exact Finsetₓ.min'_lt_of_mem_erase_min' _ _ (finset.mem_erase.mpr ⟨hb, bf⟩)
          
        
      · refine' lt_of_lt_of_leₓ (_ : _ < fmin + c) _
        · apply Finsetₓ.min'_lt_of_mem_erase_min'
          rw [← H]
          apply Finsetₓ.mem_erase_of_ne_of_mem
          · simpa only [Ne.def, add_right_injₓ]
            
          · rw [support_single_mul _ _ (fun y => by rw [one_mulₓ] : ∀ y : R, 1 * y = 0 ↔ _)]
            simpa only [Finsetₓ.mem_map, add_left_embedding_apply, add_right_injₓ, exists_propₓ, exists_eq_right]
            
          
        · haveI : CovariantClass A A (Function.swap (· + ·)) (· ≤ ·) := Add.to_covariant_class_right A
          exact add_le_add_right (Finsetₓ.min'_le _ _ bf) _
          
        
      ⟩

end LeftOrRightOrderability

end AddMonoidAlgebra

