/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Algebra.Hom.Ring
import Algebra.Order.Monoid.WithTop
import Algebra.Order.Ring.Canonical

#align_import algebra.order.ring.with_top from "leanprover-community/mathlib"@"0111834459f5d7400215223ea95ae38a1265a907"

/-! # Structures involving `*` and `0` on `with_top` and `with_bot`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main results of this section are `with_top.canonically_ordered_comm_semiring` and
`with_bot.ordered_comm_semiring`.
-/


variable {α : Type _}

namespace WithTop

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithTop α) where
  zero := 0
  mul m n := if m = 0 ∨ n = 0 then 0 else Option.map₂ (· * ·) m n
  zero_mul a := if_pos <| Or.inl rfl
  mul_zero a := if_pos <| Or.inr rfl

#print WithTop.mul_def /-
theorem mul_def {a b : WithTop α} : a * b = if a = 0 ∨ b = 0 then 0 else Option.map₂ (· * ·) a b :=
  rfl
#align with_top.mul_def WithTop.mul_def
-/

#print WithTop.mul_top' /-
theorem mul_top' {a : WithTop α} : a * ⊤ = if a = 0 then 0 else ⊤ := by
  induction a using WithTop.recTopCoe <;> simp [mul_def] <;> rfl
#align with_top.mul_top' WithTop.mul_top'
-/

#print WithTop.mul_top /-
@[simp]
theorem mul_top {a : WithTop α} (h : a ≠ 0) : a * ⊤ = ⊤ := by rw [mul_top', if_neg h]
#align with_top.mul_top WithTop.mul_top
-/

#print WithTop.top_mul' /-
theorem top_mul' {a : WithTop α} : ⊤ * a = if a = 0 then 0 else ⊤ := by
  induction a using WithTop.recTopCoe <;> simp [mul_def] <;> rfl
#align with_top.top_mul' WithTop.top_mul'
-/

#print WithTop.top_mul /-
@[simp]
theorem top_mul {a : WithTop α} (h : a ≠ 0) : ⊤ * a = ⊤ := by rw [top_mul', if_neg h]
#align with_top.top_mul WithTop.top_mul
-/

#print WithTop.top_mul_top /-
@[simp]
theorem top_mul_top : (⊤ * ⊤ : WithTop α) = ⊤ :=
  top_mul top_ne_zero
#align with_top.top_mul_top WithTop.top_mul_top
-/

#print WithTop.mul_eq_top_iff /-
theorem mul_eq_top_iff {a b : WithTop α} : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 :=
  by
  rw [mul_def, ite_eq_iff, ← none_eq_top, Option.map₂_eq_none_iff]
  have ha : a = 0 → a ≠ none := fun h => h.symm ▸ zero_ne_top
  have hb : b = 0 → b ≠ none := fun h => h.symm ▸ zero_ne_top
  tauto
#align with_top.mul_eq_top_iff WithTop.mul_eq_top_iff
-/

#print WithTop.mul_lt_top' /-
theorem mul_lt_top' [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ :=
  by
  rw [WithTop.lt_top_iff_ne_top] at *
  simp only [Ne.def, mul_eq_top_iff, *, and_false_iff, false_and_iff, false_or_iff, not_false_iff]
#align with_top.mul_lt_top' WithTop.mul_lt_top'
-/

#print WithTop.mul_lt_top /-
theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
  mul_lt_top' (WithTop.lt_top_iff_ne_top.2 ha) (WithTop.lt_top_iff_ne_top.2 hb)
#align with_top.mul_lt_top WithTop.mul_lt_top
-/

instance [NoZeroDivisors α] : NoZeroDivisors (WithTop α) :=
  by
  refine' ⟨fun a b h₁ => Decidable.by_contradiction fun h₂ => _⟩
  rw [mul_def, if_neg h₂] at h₁ 
  rcases Option.mem_map₂_iff.1 h₁ with ⟨a, b, rfl : _ = _, rfl : _ = _, hab⟩
  exact h₂ ((eq_zero_or_eq_zero_of_mul_eq_zero hab).imp (congr_arg some) (congr_arg some))

end Mul

section MulZeroClass

variable [MulZeroClass α]

#print WithTop.coe_mul /-
@[simp, norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithTop α) = a * b :=
  Decidable.byCases (fun this : a = 0 => by simp [this]) fun ha =>
    Decidable.byCases (fun this : b = 0 => by simp [this]) fun hb => by simp [*, mul_def]
#align with_top.coe_mul WithTop.coe_mul
-/

#print WithTop.mul_coe /-
theorem mul_coe {b : α} (hb : b ≠ 0) : ∀ {a : WithTop α}, a * b = a.bind fun a : α => ↑(a * b)
  | none =>
    show (if (⊤ : WithTop α) = 0 ∨ (b : WithTop α) = 0 then 0 else ⊤ : WithTop α) = ⊤ by simp [hb]
  | some a => show ↑a * ↑b = ↑(a * b) from coe_mul.symm
#align with_top.mul_coe WithTop.mul_coe
-/

#print WithTop.untop'_zero_mul /-
@[simp]
theorem untop'_zero_mul (a b : WithTop α) : (a * b).untop' 0 = a.untop' 0 * b.untop' 0 :=
  by
  by_cases ha : a = 0;
  · rw [ha, MulZeroClass.zero_mul, ← coe_zero, untop'_coe, MulZeroClass.zero_mul]
  by_cases hb : b = 0;
  · rw [hb, MulZeroClass.mul_zero, ← coe_zero, untop'_coe, MulZeroClass.mul_zero]
  induction a using WithTop.recTopCoe; · rw [top_mul hb, untop'_top, MulZeroClass.zero_mul]
  induction b using WithTop.recTopCoe; · rw [mul_top ha, untop'_top, MulZeroClass.mul_zero]
  rw [← coe_mul, untop'_coe, untop'_coe, untop'_coe]
#align with_top.untop'_zero_mul WithTop.untop'_zero_mul
-/

end MulZeroClass

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `0 * ⊤ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithTop α) :=
  { WithTop.mulZeroClass with
    mul := (· * ·)
    one := 1
    zero := 0
    one_mul := fun a =>
      match a with
      | ⊤ => mul_top (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, one_mul]
    mul_one := fun a =>
      match a with
      | ⊤ => top_mul (mt coe_eq_coe.1 one_ne_zero)
      | (a : α) => by rw [← coe_one, ← coe_mul, mul_one] }

#print MonoidWithZeroHom.withTopMap /-
/-- A version of `with_top.map` for `monoid_with_zero_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def MonoidWithZeroHom.withTopMap {R S : Type _} [MulZeroOneClass R] [DecidableEq R]
    [Nontrivial R] [MulZeroOneClass S] [DecidableEq S] [Nontrivial S] (f : R →*₀ S)
    (hf : Function.Injective f) : WithTop R →*₀ WithTop S :=
  { f.toZeroHom.withTop_map,
    f.toMonoidHom.toOneHom.withTop_map with
    toFun := WithTop.map f
    map_mul' := fun x y =>
      by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (Option.map_injective hf).eq_iff' f.to_zero_hom.with_top_map.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx); · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy); · simp
      induction x using WithTop.recTopCoe; · simp [hy, this]
      induction y using WithTop.recTopCoe
      · have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
        simp [hx, this]
      simp only [← coe_mul, map_coe, map_mul] }
#align monoid_with_zero_hom.with_top_map MonoidWithZeroHom.withTopMap
-/

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithTop α) :=
  { WithTop.mulZeroClass with
    mul := (· * ·)
    zero := 0
    mul_assoc := fun a b c => by
      rcases eq_or_ne a 0 with (rfl | ha); · simp only [MulZeroClass.zero_mul]
      rcases eq_or_ne b 0 with (rfl | hb);
      · simp only [MulZeroClass.zero_mul, MulZeroClass.mul_zero]
      rcases eq_or_ne c 0 with (rfl | hc); · simp only [MulZeroClass.mul_zero]
      induction a using WithTop.recTopCoe; · simp [hb, hc]
      induction b using WithTop.recTopCoe; · simp [ha, hc]
      induction c using WithTop.recTopCoe; · simp [ha, hb]
      simp only [← coe_mul, mul_assoc] }

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithTop α) :=
  { WithTop.mulZeroOneClass, WithTop.semigroupWithZero with }

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithTop α) :=
  { WithTop.monoidWithZero with
    mul := (· * ·)
    zero := 0
    mul_comm := fun a b => by
      simp only [or_comm', mul_def, mul_comm, @Option.map₂_comm _ _ _ _ a b _ mul_comm] }

variable [CanonicallyOrderedCommSemiring α]

private theorem distrib' (a b c : WithTop α) : (a + b) * c = a * c + b * c :=
  by
  induction c using WithTop.recTopCoe
  · by_cases ha : a = 0 <;> simp [ha]
  · by_cases hc : c = 0; · simp [hc]
    simp only [mul_coe hc]; cases a <;> cases b
    repeat'
      first
      | rfl
      | exact congr_arg some (add_mul _ _ _)

/-- This instance requires `canonically_ordered_comm_semiring` as it is the smallest class
that derives from both `non_assoc_non_unital_semiring` and `canonically_ordered_add_monoid`, both
of which are required for distributivity. -/
instance [Nontrivial α] : CommSemiring (WithTop α) :=
  { WithTop.addCommMonoidWithOne,
    WithTop.commMonoidWithZero with
    right_distrib := distrib'
    left_distrib := fun a b c => by rw [mul_comm, distrib', mul_comm b, mul_comm c]; rfl }

instance [Nontrivial α] : CanonicallyOrderedCommSemiring (WithTop α) :=
  { WithTop.commSemiring, WithTop.canonicallyOrderedAddMonoid, WithTop.noZeroDivisors with }

#print RingHom.withTopMap /-
/-- A version of `with_top.map` for `ring_hom`s. -/
@[simps (config := { fullyApplied := false })]
protected def RingHom.withTopMap {R S : Type _} [CanonicallyOrderedCommSemiring R] [DecidableEq R]
    [Nontrivial R] [CanonicallyOrderedCommSemiring S] [DecidableEq S] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f) : WithTop R →+* WithTop S :=
  { f.toMonoidWithZeroHom.withTop_map hf, f.toAddMonoidHom.withTop_map with toFun := WithTop.map f }
#align ring_hom.with_top_map RingHom.withTopMap
-/

end WithTop

namespace WithBot

variable [DecidableEq α]

section Mul

variable [Zero α] [Mul α]

instance : MulZeroClass (WithBot α) :=
  WithTop.mulZeroClass

#print WithBot.mul_def /-
theorem mul_def {a b : WithBot α} : a * b = if a = 0 ∨ b = 0 then 0 else Option.map₂ (· * ·) a b :=
  rfl
#align with_bot.mul_def WithBot.mul_def
-/

#print WithBot.mul_bot /-
@[simp]
theorem mul_bot {a : WithBot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
  WithTop.mul_top h
#align with_bot.mul_bot WithBot.mul_bot
-/

#print WithBot.bot_mul /-
@[simp]
theorem bot_mul {a : WithBot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
  WithTop.top_mul h
#align with_bot.bot_mul WithBot.bot_mul
-/

#print WithBot.bot_mul_bot /-
@[simp]
theorem bot_mul_bot : (⊥ * ⊥ : WithBot α) = ⊥ :=
  WithTop.top_mul_top
#align with_bot.bot_mul_bot WithBot.bot_mul_bot
-/

#print WithBot.mul_eq_bot_iff /-
theorem mul_eq_bot_iff {a b : WithBot α} : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff
#align with_bot.mul_eq_bot_iff WithBot.mul_eq_bot_iff
-/

#print WithBot.bot_lt_mul' /-
theorem bot_lt_mul' [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
  @WithTop.mul_lt_top' αᵒᵈ _ _ _ _ _ _ ha hb
#align with_bot.bot_lt_mul' WithBot.bot_lt_mul'
-/

#print WithBot.bot_lt_mul /-
theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : ⊥ < a * b :=
  @WithTop.mul_lt_top αᵒᵈ _ _ _ _ _ _ ha hb
#align with_bot.bot_lt_mul WithBot.bot_lt_mul
-/

end Mul

section MulZeroClass

variable [MulZeroClass α]

#print WithBot.coe_mul /-
@[norm_cast]
theorem coe_mul {a b : α} : (↑(a * b) : WithBot α) = a * b :=
  WithTop.coe_mul
#align with_bot.coe_mul WithBot.coe_mul
-/

#print WithBot.mul_coe /-
theorem mul_coe {b : α} (hb : b ≠ 0) {a : WithBot α} : a * b = a.bind fun a : α => ↑(a * b) :=
  WithTop.mul_coe hb
#align with_bot.mul_coe WithBot.mul_coe
-/

end MulZeroClass

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [MulZeroOneClass α] [Nontrivial α] : MulZeroOneClass (WithBot α) :=
  WithTop.mulZeroOneClass

instance [MulZeroClass α] [NoZeroDivisors α] : NoZeroDivisors (WithBot α) :=
  WithTop.noZeroDivisors

instance [SemigroupWithZero α] [NoZeroDivisors α] : SemigroupWithZero (WithBot α) :=
  WithTop.semigroupWithZero

instance [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] : MonoidWithZero (WithBot α) :=
  WithTop.monoidWithZero

instance [CommMonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] :
    CommMonoidWithZero (WithBot α) :=
  WithTop.commMonoidWithZero

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : CommSemiring (WithBot α) :=
  WithTop.commSemiring

instance [MulZeroClass α] [Preorder α] [PosMulMono α] : PosMulMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    rcases eq_or_ne x 0 with (rfl | x0'); · simp
    lift x to α; · rintro ⟨rfl⟩; exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction a using WithBot.recBotCoe; · simp_rw [mul_bot x0', bot_le]
    induction b using WithBot.recBotCoe; · exact absurd h (bot_lt_coe a).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0 
    exact mul_le_mul_of_nonneg_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosMono α] : MulPosMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    rcases eq_or_ne x 0 with (rfl | x0'); · simp
    lift x to α; · rintro ⟨rfl⟩; exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction a using WithBot.recBotCoe; · simp_rw [bot_mul x0', bot_le]
    induction b using WithBot.recBotCoe; · exact absurd h (bot_lt_coe a).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0 
    exact mul_le_mul_of_nonneg_right h x0⟩

instance [MulZeroClass α] [Preorder α] [PosMulStrictMono α] : PosMulStrictMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    lift x to α using x0.ne_bot
    induction b using WithBot.recBotCoe; · exact absurd h not_lt_bot
    induction a using WithBot.recBotCoe; · simp_rw [mul_bot x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0 
    exact mul_lt_mul_of_pos_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosStrictMono α] : MulPosStrictMono (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk]
    lift x to α using x0.ne_bot
    induction b using WithBot.recBotCoe; · exact absurd h not_lt_bot
    induction a using WithBot.recBotCoe; · simp_rw [bot_mul x0.ne.symm, ← coe_mul, bot_lt_coe]
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0 
    exact mul_lt_mul_of_pos_right h x0⟩

instance [MulZeroClass α] [Preorder α] [PosMulReflectLT α] : PosMulReflectLT (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h 
    rcases eq_or_ne x 0 with (rfl | x0'); · simpa using h
    lift x to α; · rintro ⟨rfl⟩; exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction b using WithBot.recBotCoe; · rw [mul_bot x0'] at h ; exact absurd h bot_le.not_lt
    induction a using WithBot.recBotCoe; · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0 
    exact lt_of_mul_lt_mul_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosReflectLT α] : MulPosReflectLT (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h 
    rcases eq_or_ne x 0 with (rfl | x0'); · simpa using h
    lift x to α; · rintro ⟨rfl⟩; exact (WithBot.bot_lt_coe (0 : α)).not_le x0
    induction b using WithBot.recBotCoe; · rw [bot_mul x0'] at h ; exact absurd h bot_le.not_lt
    induction a using WithBot.recBotCoe; · exact WithBot.bot_lt_coe _
    simp only [← coe_mul, coe_lt_coe] at *
    norm_cast at x0 
    exact lt_of_mul_lt_mul_right h x0⟩

instance [MulZeroClass α] [Preorder α] [PosMulReflectLE α] : PosMulReflectLE (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h 
    lift x to α using x0.ne_bot
    induction a using WithBot.recBotCoe; · exact bot_le
    induction b using WithBot.recBotCoe
    · rw [mul_bot x0.ne.symm, ← coe_mul] at h ; exact absurd h (bot_lt_coe (x * a)).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0 
    exact le_of_mul_le_mul_left h x0⟩

instance [MulZeroClass α] [Preorder α] [MulPosReflectLE α] : MulPosReflectLE (WithBot α) :=
  ⟨by
    rintro ⟨x, x0⟩ a b h; simp only [Subtype.coe_mk] at h 
    lift x to α using x0.ne_bot
    induction a using WithBot.recBotCoe; · exact bot_le
    induction b using WithBot.recBotCoe
    · rw [bot_mul x0.ne.symm, ← coe_mul] at h ; exact absurd h (bot_lt_coe (a * x)).not_le
    simp only [← coe_mul, coe_le_coe] at *
    norm_cast at x0 
    exact le_of_mul_le_mul_right h x0⟩

instance [CanonicallyOrderedCommSemiring α] [Nontrivial α] : OrderedCommSemiring (WithBot α) :=
  { WithBot.zeroLEOneClass, WithBot.orderedAddCommMonoid,
    WithBot.commSemiring with
    mul_le_mul_of_nonneg_left := fun _ _ _ => mul_le_mul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun _ _ _ => mul_le_mul_of_nonneg_right }

end WithBot

