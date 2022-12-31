/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.pointwise.finite
! leanprover-community/mathlib commit a437a2499163d85d670479f69f625f461cc5fef9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite
import Mathbin.Data.Set.Pointwise.Smul

/-! # Finiteness lemmas for pointwise operations on sets -/


open Pointwise

variable {F α β γ : Type _}

namespace Set

section InvolutiveInv

variable [InvolutiveInv α] {s : Set α}

@[to_additive]
theorem Finite.inv (hs : s.Finite) : s⁻¹.Finite :=
  hs.Preimage <| inv_injective.InjOn _
#align set.finite.inv Set.Finite.inv

end InvolutiveInv

section Mul

variable [Mul α] {s t : Set α}

@[to_additive]
theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite :=
  Finite.image2 _
#align set.finite.mul Set.Finite.mul

/-- Multiplication preserves finiteness. -/
@[to_additive "Addition preserves finiteness."]
def fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t : Set α) :=
  Set.fintypeImage2 _ _ _
#align set.fintype_mul Set.fintypeMul

end Mul

section Monoid

variable [Monoid α] {s t : Set α}

@[to_additive]
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)]
    [DecidablePred (· ∈ t)] : DecidablePred (· ∈ s * t) := fun _ => decidable_of_iff _ mem_mul.symm
#align set.decidable_mem_mul Set.decidableMemMul

@[to_additive]
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)] (n : ℕ) :
    DecidablePred (· ∈ s ^ n) := by
  induction' n with n ih
  · simp_rw [pow_zero, mem_one]
    infer_instance
  · letI := ih
    rw [pow_succ]
    infer_instance
#align set.decidable_mem_pow Set.decidableMemPow

end Monoid

section HasSmul

variable [HasSmul α β] {s : Set α} {t : Set β}

@[to_additive]
theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite :=
  Finite.image2 _
#align set.finite.smul Set.Finite.smul

end HasSmul

section HasSmulSet

variable [HasSmul α β] {s : Set β} {a : α}

@[to_additive]
theorem Finite.smul_set : s.Finite → (a • s).Finite :=
  Finite.image _
#align set.finite.smul_set Set.Finite.smul_set

end HasSmulSet

section Vsub

variable [VSub α β] {s t : Set β}

include α

theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.image2 _ ht
#align set.finite.vsub Set.Finite.vsub

end Vsub

end Set

open Set

namespace Group

variable {G : Type _} [Group G] [Fintype G] (S : Set G)

@[to_additive]
theorem card_pow_eq_card_pow_card_univ [∀ k : ℕ, DecidablePred (· ∈ S ^ k)] :
    ∀ k, Fintype.card G ≤ k → Fintype.card ↥(S ^ k) = Fintype.card ↥(S ^ Fintype.card G) :=
  by
  have hG : 0 < Fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩
  by_cases hS : S = ∅
  · refine' fun k hk => Fintype.card_congr _
    rw [hS, empty_pow (ne_of_gt (lt_of_lt_of_le hG hk)), empty_pow (ne_of_gt hG)]
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hS
  classical!
  have key : ∀ (a) (s t : Set G), (∀ b : G, b ∈ s → a * b ∈ t) → Fintype.card s ≤ Fintype.card t :=
    by
    refine' fun a s t h => Fintype.card_le_of_injective (fun ⟨b, hb⟩ => ⟨a * b, h b hb⟩) _
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_left_cancel (subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n => Fintype.card ↥(S ^ n) : ℕ → ℕ) :=
    monotone_nat_of_le_succ fun n => key a _ _ fun b hb => Set.mul_mem_mul ha hb
  convert
    card_pow_eq_card_pow_card_univ_aux mono (fun n => set_fintype_card_le_univ (S ^ n)) fun n h =>
      le_antisymm (mono (n + 1).le_succ) (key a⁻¹ _ _ _)
  · simp only [Finset.filter_congr_decidable, Fintype.card_of_finset]
  replace h : {a} * S ^ n = S ^ (n + 1)
  · refine' Set.eq_of_subset_of_card_le _ (le_trans (ge_of_eq h) _)
    · exact mul_subset_mul (set.singleton_subset_iff.mpr ha) Set.Subset.rfl
    · convert key a (S ^ n) ({a} * S ^ n) fun b hb => Set.mul_mem_mul (Set.mem_singleton a) hb
  rw [pow_succ', ← h, mul_assoc, ← pow_succ', h]
  rintro _ ⟨b, c, hb, hc, rfl⟩
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_left]
#align group.card_pow_eq_card_pow_card_univ Group.card_pow_eq_card_pow_card_univ

end Group

