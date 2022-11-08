/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import Mathbin.Data.Pnat.Defs
import Mathbin.Data.Nat.Order
import Mathbin.Algebra.Order.Positive.Ring

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
It is defined in `data.pnat.defs`, but most of the development is deferred to here so
that `data.pnat.defs` can have very few imports.
-/


deriving instance AddLeftCancelSemigroup, AddRightCancelSemigroup, AddCommSemigroup, LinearOrderedCancelCommMonoid, Add,
  Mul, Distrib for Pnat

namespace Pnat

@[simp]
theorem one_add_nat_pred (n : ℕ+) : 1 + n.natPred = n := by
  rw [nat_pred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]

@[simp]
theorem nat_pred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_nat_pred

@[mono]
theorem nat_pred_strict_mono : StrictMono natPred := fun m n h => Nat.pred_lt_pred m.2.ne' h

@[mono]
theorem nat_pred_monotone : Monotone natPred :=
  nat_pred_strict_mono.Monotone

theorem nat_pred_injective : Function.Injective natPred :=
  nat_pred_strict_mono.Injective

@[simp]
theorem nat_pred_lt_nat_pred {m n : ℕ+} : m.natPred < n.natPred ↔ m < n :=
  nat_pred_strict_mono.lt_iff_lt

@[simp]
theorem nat_pred_le_nat_pred {m n : ℕ+} : m.natPred ≤ n.natPred ↔ m ≤ n :=
  nat_pred_strict_mono.le_iff_le

@[simp]
theorem nat_pred_inj {m n : ℕ+} : m.natPred = n.natPred ↔ m = n :=
  nat_pred_injective.eq_iff

end Pnat

namespace Nat

@[mono]
theorem succ_pnat_strict_mono : StrictMono succPnat := fun m n => Nat.succ_lt_succ

@[mono]
theorem succ_pnat_mono : Monotone succPnat :=
  succ_pnat_strict_mono.Monotone

@[simp]
theorem succ_pnat_lt_succ_pnat {m n : ℕ} : m.succPnat < n.succPnat ↔ m < n :=
  succ_pnat_strict_mono.lt_iff_lt

@[simp]
theorem succ_pnat_le_succ_pnat {m n : ℕ} : m.succPnat ≤ n.succPnat ↔ m ≤ n :=
  succ_pnat_strict_mono.le_iff_le

theorem succ_pnat_injective : Function.Injective succPnat :=
  succ_pnat_strict_mono.Injective

@[simp]
theorem succ_pnat_inj {n m : ℕ} : succPnat n = succPnat m ↔ n = m :=
  succ_pnat_injective.eq_iff

end Nat

namespace Pnat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
@[simp, norm_cast]
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  SetCoe.ext_iff

@[simp, norm_cast]
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl

/-- `pnat.coe` promoted to an `add_hom`, that is, a morphism which preserves addition. -/
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := coe
  map_add' := add_coe

instance : CovariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.covariant_class_add_le

instance : CovariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.covariant_class_add_lt

instance : ContravariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  Positive.contravariant_class_add_le

instance : ContravariantClass ℕ+ ℕ+ (· + ·) (· < ·) :=
  Positive.contravariant_class_add_lt

/-- An equivalence between `ℕ+` and `ℕ` given by `pnat.nat_pred` and `nat.succ_pnat`. -/
@[simps (config := { fullyApplied := false })]
def _root_.equiv.pnat_equiv_nat : ℕ+ ≃ ℕ where
  toFun := Pnat.natPred
  invFun := Nat.succPnat
  left_inv := succ_pnat_nat_pred
  right_inv := Nat.nat_pred_succ_pnat

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps (config := { fullyApplied := false }) apply]
def _root_.order_iso.pnat_iso_nat : ℕ+ ≃o ℕ where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' _ _ := nat_pred_le_nat_pred

@[simp]
theorem _root_.order_iso.pnat_iso_nat_symm_apply : ⇑OrderIso.pnatIsoNat.symm = Nat.succPnat :=
  rfl

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := fun a b => Nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := fun a b => Nat.add_one_le_iff

instance : OrderBot ℕ+ where
  bot := 1
  bot_le a := a.property

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) :=
  rfl

@[simp]
theorem mk_bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) :=
  rfl

-- Some lemmas that rewrite inequalities between explicit numerals in `ℕ+`
-- into the corresponding inequalities in `ℕ`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp]
theorem bit0_le_bit0 (n m : ℕ+) : bit0 n ≤ bit0 m ↔ bit0 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem bit0_le_bit1 (n m : ℕ+) : bit0 n ≤ bit1 m ↔ bit0 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem bit1_le_bit0 (n m : ℕ+) : bit1 n ≤ bit0 m ↔ bit1 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem bit1_le_bit1 (n m : ℕ+) : bit1 n ≤ bit1 m ↔ bit1 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl

@[simp, norm_cast]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl

/-- `pnat.coe` promoted to a `monoid_hom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]
theorem coe_coe_monoid_hom : (coeMonoidHom : ℕ+ → ℕ) = coe :=
  rfl

@[simp]
theorem le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 :=
  le_bot_iff

theorem lt_add_left (n m : ℕ+) : n < m + n :=
  lt_add_of_pos_left _ m.2

theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast]
theorem coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) :=
  rfl

@[simp, norm_cast]
theorem coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) :=
  rfl

@[simp, norm_cast]
theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
  rfl

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : Sub ℕ+ :=
  ⟨fun a b => toPnat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 := by
  change (to_pnat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact to_pnat'_coe (tsub_pos_of_lt h)
    
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b)]
    rfl
    

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b := fun h =>
  Eq <| by
    rw [add_coe, sub_coe, if_pos h]
    exact add_tsub_cancel_of_le h.le

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (h1 : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h1 => False.elim <| h1 rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def caseStrongInductionOn {p : ℕ+ → Sort _} (a : ℕ+) (hz : p 1) (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  apply strong_induction_on a
  rintro ⟨k, kprop⟩ hk
  cases' k with k
  · exact (lt_irrefl 0 kprop).elim
    
  cases' k with k
  · exact hz
    
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (lt_succ_iff.2 hm)

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim]
def recOn (n : ℕ+) {p : ℕ+ → Sort _} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction' n with n IH
  · exact absurd h (by decide)
    
  · cases' n with n
    · exact p1
      
    · exact hp _ (IH n.succ_pos)
      
    

@[simp]
theorem rec_on_one {p} (p1 hp) : @Pnat.recOn 1 p p1 hp = p1 :=
  rfl

@[simp]
theorem rec_on_succ (n : ℕ+) {p : ℕ+ → Sort _} (p1 hp) : @Pnat.recOn (n + 1) p p1 hp = hp n (@Pnat.recOn n p p1 hp) :=
  by
  cases' n with n h
  cases n <;> [exact absurd h (by decide), rfl]

theorem mod_div_aux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (h : ¬(r = 0 ∧ q = 0)), ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | k, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, h => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_add, add_comm]
  | k, r + 1, q, h => rfl

theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_div (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀

theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_comm _ _).trans (mod_add_div _ _)

theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m := by
  rw [mul_comm]
  exact div_add_mod _ _

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k := by
  change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
  rw [mod_coe]
  split_ifs
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm⊢
    by_cases h':(m : ℕ) / (k : ℕ) = 0
    · rw [h', mul_zero] at hm
      exact (lt_irrefl _ hm).elim
      
    · let h' := Nat.mul_le_mul_left (k : ℕ) (Nat.succ_le_of_lt (Nat.pos_of_ne_zero h'))
      rw [mul_one] at h'
      exact ⟨h', le_refl (k : ℕ)⟩
      
    
  · exact ⟨Nat.mod_le (m : ℕ) (k : ℕ), (Nat.mod_lt (m : ℕ) k.pos).le⟩
    

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by
  constructor <;> intro h
  rcases h with ⟨_, rfl⟩
  apply dvd_mul_right
  rcases h with ⟨a, h⟩
  cases a
  · contrapose h
    apply NeZero
    
  use a.succ
  apply Nat.succ_pos
  rw [← coe_inj, h, mul_coe, mk_coe]

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h
    apply Eq
    rw [mod_coe, if_pos h]
    
  · intro h
    by_cases h':(m : ℕ) % (k : ℕ) = 0
    · exact h'
      
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, if_neg h'] at h
      exact ((Nat.mod_lt (m : ℕ) k.pos).Ne h).elim
      
    

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply Eq
  rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm => (le_of_dvd hmn).antisymm (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact Pnat.ne_zero n (eq_zero_of_zero_dvd h)

end Pnat

