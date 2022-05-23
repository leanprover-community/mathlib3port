/-
Copyright (c) 2021 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.RingTheory.Localization.Away
import Mathbin.SetTheory.Surreal.Basic

/-!
# Dyadic numbers
Dyadic numbers are obtained by localizing ℤ away from 2. They are the initial object in the category
of rings with no 2-torsion.

## Dyadic surreal numbers
We construct dyadic surreal numbers using the canonical map from ℤ[2 ^ {-1}] to surreals.
As we currently do not have a ring structure on `surreal` we construct this map explicitly. Once we
have the ring structure, this map can be constructed directly by sending `2 ^ {-1}` to `half`.

## Embeddings
The above construction gives us an abelian group embedding of ℤ into `surreal`. The goal is to
extend this to an embedding of dyadic rationals into `surreal` and use Cauchy sequences of dyadic
rational numbers to construct an ordered field embedding of ℝ into `surreal`.
-/


universe u

-- mathport name: «expr ≈ »
local infixl:0 " ≈ " => Pgame.Equiv

namespace Pgame

/-- For a natural number `n`, the pre-game `pow_half (n + 1)` is recursively defined as
`{ 0 | pow_half n }`. These are the explicit expressions of powers of `half`. By definition, we have
 `pow_half 0 = 0` and `pow_half 1 = half` and we prove later on that
`pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n`.-/
def powHalf : ℕ → Pgame
  | 0 => mk PUnit Pempty 0 Pempty.elimₓ
  | n + 1 => mk PUnit PUnit 0 fun _ => pow_half n

@[simp]
theorem pow_half_left_moves {n} : (powHalf n).LeftMoves = PUnit := by
  cases n <;> rfl

@[simp]
theorem pow_half_right_moves {n} : (powHalf (n + 1)).RightMoves = PUnit :=
  rfl

@[simp]
theorem pow_half_move_left {n i} : (powHalf n).moveLeft i = 0 := by
  cases n <;> cases i <;> rfl

@[simp]
theorem pow_half_move_right {n i} : (powHalf (n + 1)).moveRight i = powHalf n :=
  rfl

theorem pow_half_move_left' n : (powHalf n).moveLeft (Equivₓ.cast pow_half_left_moves.symm PUnit.unit) = 0 := by
  simp only [eq_self_iff_true, pow_half_move_left]

theorem pow_half_move_right' n :
    (powHalf (n + 1)).moveRight (Equivₓ.cast pow_half_right_moves.symm PUnit.unit) = powHalf n := by
  simp only [pow_half_move_right, eq_self_iff_true]

/-- For all natural numbers `n`, the pre-games `pow_half n` are numeric. -/
theorem numeric_pow_half {n} : (powHalf n).Numeric := by
  induction' n with n hn
  · exact numeric_one
    
  · constructor
    · rintro ⟨⟩ ⟨⟩
      dsimp' only [Pi.zero_apply]
      rw [← pow_half_move_left' n]
      apply hn.move_left_lt
      
    · exact ⟨fun _ => numeric_zero, fun _ => hn⟩
      
    

theorem pow_half_succ_lt_pow_half {n : ℕ} : powHalf (n + 1) < powHalf n :=
  Numeric.lt_move_right numeric_pow_half PUnit.unit

theorem pow_half_succ_le_pow_half {n : ℕ} : powHalf (n + 1) ≤ powHalf n :=
  pow_half_succ_lt_pow_half.le

theorem zero_lt_pow_half {n : ℕ} : 0 < powHalf n := by
  cases n <;> rw [← lf_iff_lt numeric_zero numeric_pow_half, zero_lf_le] <;> exact ⟨PUnit.unit, le_rfl⟩

theorem zero_le_pow_half {n : ℕ} : 0 ≤ powHalf n :=
  zero_lt_pow_half.le

theorem add_pow_half_succ_self_eq_pow_half {n} : powHalf (n + 1) + powHalf (n + 1) ≈ powHalf n := by
  induction' n with n hn
  · exact half_add_half_equiv_one
    
  · constructor <;> rw [le_iff_forall_lf] <;> constructor
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> apply lf_of_lt
      · calc 0 + pow_half (n.succ + 1) ≈ pow_half (n.succ + 1) := zero_add_equiv _ _ < pow_half n.succ :=
            pow_half_succ_lt_pow_half
        
      · calc pow_half (n.succ + 1) + 0 ≈ pow_half (n.succ + 1) := add_zero_equiv _ _ < pow_half n.succ :=
            pow_half_succ_lt_pow_half
        
      
    · rintro ⟨⟩
      rw [lf_iff_forall_le]
      right
      use Sum.inl PUnit.unit
      calc pow_half n.succ + pow_half (n.succ + 1) ≤ pow_half n.succ + pow_half n.succ :=
          add_le_add_left pow_half_succ_le_pow_half _ _ ≈ pow_half n := hn
      
    · rintro ⟨⟩
      apply lf_of_lt
      calc 0 ≈ 0 + 0 := (add_zero_equiv _).symm _ ≤ pow_half (n.succ + 1) + 0 :=
          add_le_add_right zero_le_pow_half _ _ < pow_half (n.succ + 1) + pow_half (n.succ + 1) :=
          add_lt_add_left zero_lt_pow_half _
      
    · rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> apply lf_of_lt
      · calc pow_half n.succ ≈ pow_half n.succ + 0 :=
            (add_zero_equiv _).symm _ < pow_half n.succ + pow_half (n.succ + 1) := add_lt_add_left zero_lt_pow_half _
        
      · calc pow_half n.succ ≈ 0 + pow_half n.succ :=
            (zero_add_equiv _).symm _ < pow_half (n.succ + 1) + pow_half n.succ := add_lt_add_right zero_lt_pow_half _
        
      
    

end Pgame

namespace Surreal

open Pgame

/-- The surreal number `half`. -/
def half : Surreal :=
  ⟦⟨Pgame.half, Pgame.numeric_half⟩⟧

/-- Powers of the surreal number `half`. -/
def powHalf (n : ℕ) : Surreal :=
  ⟦⟨Pgame.powHalf n, Pgame.numeric_pow_half⟩⟧

@[simp]
theorem pow_half_zero : powHalf 0 = 1 :=
  rfl

@[simp]
theorem pow_half_one : powHalf 1 = half :=
  rfl

@[simp]
theorem add_half_self_eq_one : half + half = 1 :=
  Quotientₓ.sound Pgame.half_add_half_equiv_one

theorem double_pow_half_succ_eq_pow_half (n : ℕ) : 2 • powHalf n.succ = powHalf n := by
  rw [two_nsmul]
  apply Quotientₓ.sound
  exact Pgame.add_pow_half_succ_self_eq_pow_half

theorem nsmul_pow_two_pow_half (n : ℕ) : 2 ^ n • powHalf n = 1 := by
  induction' n with n hn
  · simp only [nsmul_one, pow_half_zero, Nat.cast_oneₓ, pow_zeroₓ]
    
  · rw [← hn, ← double_pow_half_succ_eq_pow_half n, smul_smul (2 ^ n) 2 (pow_half n.succ), mul_comm, pow_succₓ]
    

theorem nsmul_pow_two_pow_half' (n k : ℕ) : 2 ^ n • powHalf (n + k) = powHalf k := by
  induction' k with k hk
  · simp only [add_zeroₓ, Surreal.nsmul_pow_two_pow_half, Nat.nat_zero_eq_zero, eq_self_iff_true, Surreal.pow_half_zero]
    
  · rw [← double_pow_half_succ_eq_pow_half (n + k), ← double_pow_half_succ_eq_pow_half k, smul_algebra_smul_comm] at hk
    rwa [← zsmul_eq_zsmul_iff' two_ne_zero]
    

theorem zsmul_pow_two_pow_half (m : ℤ) (n k : ℕ) : (m * 2 ^ n) • powHalf (n + k) = m • powHalf k := by
  rw [mul_zsmul]
  congr
  norm_cast
  exact nsmul_pow_two_pow_half' n k

theorem dyadic_aux {m₁ m₂ : ℤ} {y₁ y₂ : ℕ} (h₂ : m₁ * 2 ^ y₁ = m₂ * 2 ^ y₂) : m₁ • powHalf y₂ = m₂ • powHalf y₁ := by
  revert m₁ m₂
  wlog h : y₁ ≤ y₂
  intro m₁ m₂ h₂
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h
  rw [add_commₓ, pow_addₓ, ← mul_assoc, mul_eq_mul_right_iff] at h₂
  cases h₂
  · rw [h₂, add_commₓ, zsmul_pow_two_pow_half m₂ c y₁]
    
  · have := Nat.one_le_pow y₁ 2 Nat.succ_pos'
    linarith
    

/-- The additive monoid morphism `dyadic_map` sends ⟦⟨m, 2^n⟩⟧ to m • half ^ n. -/
def dyadicMap : Localization.Away (2 : ℤ) →+ Surreal where
  toFun := fun x =>
    (Localization.liftOn x fun x y => x • powHalf (Submonoid.log y)) <| by
      intro m₁ m₂ n₁ n₂ h₁
      obtain ⟨⟨n₃, y₃, hn₃⟩, h₂⟩ := localization.r_iff_exists.mp h₁
      simp only [Subtype.coe_mk, mul_eq_mul_right_iff] at h₂
      cases h₂
      · simp only
        obtain ⟨a₁, ha₁⟩ := n₁.prop
        obtain ⟨a₂, ha₂⟩ := n₂.prop
        have hn₁ : n₁ = Submonoid.pow 2 a₁ := Subtype.ext ha₁.symm
        have hn₂ : n₂ = Submonoid.pow 2 a₂ := Subtype.ext ha₂.symm
        have h₂ : 1 < (2 : ℤ).natAbs := one_lt_two
        rw [hn₁, hn₂, Submonoid.log_pow_int_eq_self h₂, Submonoid.log_pow_int_eq_self h₂]
        apply dyadic_aux
        rwa [ha₁, ha₂]
        
      · have := Nat.one_le_pow y₃ 2 Nat.succ_pos'
        linarith
        
  map_zero' := Localization.lift_on_zero _ _
  map_add' := fun x y =>
    Localization.induction_on₂ x y <| by
      rintro ⟨a, ⟨b, ⟨b', rfl⟩⟩⟩ ⟨c, ⟨d, ⟨d', rfl⟩⟩⟩
      have h₂ : 1 < (2 : ℤ).natAbs := one_lt_two
      have hpow₂ := Submonoid.log_pow_int_eq_self h₂
      simp_rw [Submonoid.pow_apply]  at hpow₂
      simp_rw [Localization.add_mk, Localization.lift_on_mk, Subtype.coe_mk,
        Submonoid.log_mul (Int.pow_right_injective h₂), hpow₂]
      calc
        (2 ^ b' * c + 2 ^ d' * a) • pow_half (b' + d') =
            (c * 2 ^ b') • pow_half (b' + d') + (a * 2 ^ d') • pow_half (d' + b') :=
          by
          simp only [add_smul, mul_comm, add_commₓ]_ = c • pow_half d' + a • pow_half b' := by
          simp only [zsmul_pow_two_pow_half]_ = a • pow_half b' + c • pow_half d' := add_commₓ _ _

@[simp]
theorem dyadic_map_apply (m : ℤ) (p : Submonoid.powers (2 : ℤ)) :
    dyadicMap (IsLocalization.mk' (Localization (Submonoid.powers 2)) m p) = m • powHalf (Submonoid.log p) := by
  rw [← Localization.mk_eq_mk']
  rfl

@[simp]
theorem dyadic_map_apply_pow (m : ℤ) (n : ℕ) :
    dyadicMap (IsLocalization.mk' (Localization (Submonoid.powers 2)) m (Submonoid.pow 2 n)) = m • powHalf n := by
  rw [dyadic_map_apply, @Submonoid.log_pow_int_eq_self 2 one_lt_two]

/-- We define dyadic surreals as the range of the map `dyadic_map`. -/
def Dyadic : Set Surreal :=
  Set.Range dyadicMap

-- We conclude with some ideas for further work on surreals; these would make fun projects.
-- TODO show that the map from dyadic rationals to surreals is injective
-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective
-- TODO show the maps from the dyadic rationals and from the reals
-- into the surreals are multiplicative
end Surreal

